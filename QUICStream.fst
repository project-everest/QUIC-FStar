(**

QUIC Stream - the high-level stream interface for applications

@summary: streams within a QUIC connection
*)
module QUICStream

open FStar
open FStar.HyperStack
open FStar.HyperStack.IO
open FStar.HyperStack.ST
open FStar.Int.Cast
open FStar.Printf
open C
open C.Failure
open C.String
open LowStar.Buffer
open LowStar.BufferOps
open QUICTypes
open QUICMutators
open QUICFFI
open QUICUtils
open QUICTLS

open HeapOps

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module L = FStar.List.Tot
module B = LowStar.Buffer
module DLL = DoublyLinkedListIface

let isStreamBidi (stream:U64.t): bool
=
  let bit = U64.(stream &^ 2UL) in
  bit = 0UL

let isStreamUni (stream:U64.t): bool
=
  let bit = U64.(stream &^ 2UL) in
  bit <> 0UL

let isStreamClientInitiated (stream:U64.t): bool
=
  let bit = U64.(stream &^ 1UL) in
  bit = 0UL

let isStreamServerInitiated (stream:U64.t): bool
=
  let bit = U64.(stream &^ 1UL) in
  bit <> 0UL

(** Determine if a stream has segments ready to send *)
let hasMoreToSend (strm:quic_stream): ST bool
   (requires (fun h0 -> True))
   (ensures (fun h0 _ h1 -> h0 == h1))
=
  push_frame();
  admit (); (* TODO: Prove *)
  let strmm = strm_get_mutable strm in
  let hasmore = if (DLL.is_null_node (DLL.dll_head strmm.segments)) then false else true in
  pop_frame();
  hasmore

#push-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
(** Find a quic_stream that has data ready for transmission.  May return null
    if there is no ready stream. *)
let findReadyStream (cs:pointer connection): ST (quic_stream_or_null)
   (requires heappre (fun h0 ( !* ) ->
        live h0 cs /\
        live h0 (!*cs).csm_state /\
        DLL.dll_valid h0 (!*((!*cs).csm_state)).streams))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let strm =
    if U64.(csm.dataSent >=^ csm.maxDataPeer) then (
      DLL.null_node // Not permitted to send more stream data when the connection  is at maxDataPeer
    ) else (
      let lst : quic_stream_list = (!*((!*cs).csm_state)).streams in
      let hhh0 = HST.get () in
      let head : quic_stream_or_null = DLL.dll_head lst in
      let pp : pointer quic_stream_or_null = B.alloca head 1ul in
      let pstrm = B.alloca DLL.null_node 1ul in
      let headisnull = DLL.is_null_node head in
      let pstop = B.alloca headisnull 1ul in
      let inv h =
        B.live h pp /\
        B.live h pstrm /\
        B.live h pp /\
        B.live h pstop /\
        B.loc_disjoint (B.loc_buffer pstop) (DLL.fp_dll h lst) /\
        B.loc_disjoint (B.loc_buffer pstrm) (DLL.fp_dll h lst) /\
        B.loc_disjoint (B.loc_buffer pp) (DLL.fp_dll h lst) /\
        (not (pstop@h) ==> (
          (pp@h =!= DLL.null_node) /\ (DLL.coerce_non_null (pp@h)) `L.memP` DLL.as_list h lst
          )) /\
        DLL.dll_valid h lst in
      let pre h : GTot Type0 = inv h in
      let post (x:bool) h : GTot Type0 =
        inv h /\
        (x == not (pstop@h)) in
      let test (): Stack bool (requires (fun h -> pre h)) (ensures (fun _ x h -> post x h)) =
        not !*pstop
      in
      let body (): Stack unit
          (requires (fun h0 -> post true h0))
          (ensures (fun _ _ h1 -> pre h1)) =
        let isready = hasMoreToSend (DLL.coerce_non_null !*pp) in
        if isready then (
          pstrm *= !*pp
          );
        pp *= DLL.next_node lst (DLL.coerce_non_null !*pp) ;
        let nn = DLL.is_null_node !*pp in
        pstop *= (nn || isready)
      in
      let hhh = HST.get () in
      C.Loops.while #pre #post test body;
      !*pstrm
      ) in
  pop_frame();
  strm
#pop-options

let getPacketSpaceState (cs:pointer connection) (ps:packet_space): ST packet_space_state
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let psn = indexOfPacketSpace ps in
  (!*cs).packetSpaces.(psn)

(** Determine if a connection has more data pending, ready to send *)
let connectionHasMoreToSend (cs:pointer connection): ST (option packet_space)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let pssInitial = getPacketSpaceState cs InitialSpace in
  (* Prioritize pending data from lower numbered epochs *)
  let epochIndex = indexOfEpoch csm.epoch in
  let hasMore =
    if csm.cstate <> Running then
      None
    else if U32.(epochIndex >=^ epochIndexInitial) then (
      if hasMoreToSend pssInitial.crypto_stream ||
         (pssInitial.sendAckOnlyIfNeeded && pssInitial.outgoingAckCount <> 0ul)then
        Some InitialSpace
      else if U32.(epochIndex >=^ epochIndexHandshake) then (
        let pssHandshake = getPacketSpaceState cs HandshakeSpace in
        if hasMoreToSend pssHandshake.crypto_stream ||
           (pssHandshake.sendAckOnlyIfNeeded && pssHandshake.outgoingAckCount <> 0ul) then (
          Some HandshakeSpace
        ) else if epochIndex = epochIndex1RTT then (
          let pssApplication = getPacketSpaceState cs ApplicationSpace in
          let fixedframeListEmpty = DLL.is_null_node (DLL.dll_head csm.fixedframes) in
          let hasMore = csm.pingPending ||
                        not fixedframeListEmpty ||
                        hasMoreToSend pssApplication.crypto_stream ||
                        (pssApplication.sendAckOnlyIfNeeded && pssApplication.outgoingAckCount <> 0ul) ||
                        not (DLL.is_null_node (findReadyStream cs)) in
          if hasMore then Some ApplicationSpace else None
        ) else
          None
      )
      else
        None
      )
    else
      None
  in
  pop_frame();
  hasMore

(** Enqueue a fixed frame for transmission *)
let enqueueFixedFrame (cs:pointer connection) (data:buffer_t) (len:U32.t): ST intptr_t (* a waitable handle *)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let hWait = createEvent 0l 0l in
  let fixed = { hWait = hWait; framedata = data; framelength = len; } in
  let pff = DLL.node_of HyperStack.root fixed in
  let csm = conn_get_mutable cs in
  DLL.dll_insert_at_tail csm.fixedframes pff;
  upd_fixedframes (!*cs).csm_state csm.fixedframes;
  pop_frame();
  hWait

(** Enqueue a fixed frame for transmission *)
let enqueueAsyncFixedFrame (cs:pointer connection) (data:buffer_t) (len:U32.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let fixed = { hWait = nullptr; framedata = data; framelength = len; } in
  let pff = DLL.node_of HyperStack.root fixed in
  let csm = conn_get_mutable cs in
  DLL.dll_insert_at_tail csm.fixedframes pff;
  upd_fixedframes (!*cs).csm_state csm.fixedframes;
  pop_frame()

(** Add the connection to the engine's ready-to-send list *)
let setHasReadyToSend (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let eng = from_engine_t (!*cs).eng in
  let pholder = DLL.node_of HyperStack.root cs in
  monitorEnter (!*eng).emonitor;
  DLL.dll_insert_at_tail (!*eng).readyconnections pholder;
  upd_readyconnections eng (!*eng).readyconnections;
  setEvent (!*eng).dataReadyToSend;
  monitorExit (!*eng).emonitor;
  pop_frame()

(** Refresh the 'ready to send' state for the connection *)
let updateReadyToSend (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if connectionHasMoreToSend cs <> None then (
    setHasReadyToSend cs
  )

(** Enqueue a CONNECTION_CLOSE.  This isn't waitable, as no response is expected from
      the peer *)
let enqueueConnectionClose (cs:pointer connection) (errcode:U16.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let len = 4ul in
  let data = B.malloc HyperStack.root 0uy len in
  let offset = append8 data 0ul 0x02uy in // CONNECTION_CLOSE
  let offset = append16 data offset errcode in // Error Code
  let offset = append8 data offset 0x00uy in // Reason Phrase Length (0)
  enqueueAsyncFixedFrame cs data len;
  updateReadyToSend cs;
  pop_frame()

(** Abort a connection:  send a CONNECTION_CLOSE and halt further communication *)
let abortConnection (cs:pointer connection) (transportErrorCode:U16.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  enqueueConnectionClose cs  transportErrorCode;
  pop_frame()

(** Find a stream within the connection, by its ID *)
let findStream (csm:connection_mutable) (stream:U64.t): ST (quic_stream_or_null)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let head = DLL.dll_head csm.streams in
  let pp : pointer quic_stream_or_null = B.alloca head 1ul in
  let pstrm = B.alloca DLL.null_node 1ul in
  let inv h = B.live h pp in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not (DLL.is_null_node !*pp)
  in
  let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    if (DLL.node_val (DLL.coerce_non_null !*pp)).streamID = stream then (
      pstrm *= !*pp;
      pp *= DLL.null_node
    ) else (
      pp *= DLL.next_node csm.streams (DLL.coerce_non_null !*pp)
    )
  in
  C.Loops.while test body;
  let strm = !*pstrm in
  pop_frame();
  strm

(** Free the memory associated with a segment *)
let deleteSegment (seg:qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
    push_frame();
    (* Quick check that the segment is not live.  This isn't sufficient, as a list with
       exactly one element won't trigger this check, as the one element's
       flink and blink are both null *)
    (* JB: We won't require this check anymore once we have proven
           memory safety; thus I haven't bothered converting this part
           over. *)
    // if not (is_null (!*seg).flink) || not (is_null (!*seg).blink)
    //     then failwith (of_literal "deleteSegment of a segment still on a list");

    if not (DLL.node_val seg).isApplicationOwned then B.free (DLL.node_val seg).data;
    let h = (DLL.node_val seg).available in
    if h <> (uint32_to_intptr_t 0ul) then closeHandle h;
    (* FIXME[jb]: We don't (yet) support free in the dlist interface *)
    // B.free seg;
    pop_frame()

(** Create a new stream instance *)
let createStream (stream:U64.t) (maxData:U64.t) : ST (quic_stream)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm:quic_stream_mutable = {
    recvState = RecvStreamRecv;
    partialsegments=DLL.dll_new HyperStack.root;
    readysegments=DLL.dll_new HyperStack.root;
    nextReadOffset = 0UL;
    error_code=0us;

    sendState = SendStreamSend;
    nextWriteOffset = 0UL;
    maxStreamData = maxData;
    segments=DLL.dll_new HyperStack.root;
    } in
  let strmr = B.malloc HyperStack.root strmm 1ul in
  let strmf:quic_stream_fixed = {
    streamID = stream;
    qsm_state = strmr;
  } in
  let strm = DLL.node_of HyperStack.root strmf in
  pop_frame();
  strm

(** Open a QUIC stream.  Called from quic_OpenStream() as well as from the frame-recieve path *)
let openStreamInternal (cs:pointer connection) (stream:U64.t) : ST (quic_stream_or_null)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm = (
      monitorEnter (!*cs).monitor;
      let csm = conn_get_mutable cs in
      let strm = findStream csm stream in
      let strm =
        if DLL.is_null_node strm then (
          let maxStreamID = if (isStreamBidi stream) then csm.maxStreamID_BIDIPeer else csm.maxStreamID_UNIPeer in
          if U64.gt stream maxStreamID then
            DLL.null_node
          else (
            let pstrm = createStream stream csm.defaultMaxStreamData in
            DLL.dll_insert_at_tail csm.streams pstrm;
            upd_streams (!*cs).csm_state csm.streams;
            DLL.coerce_nullable pstrm
          )
        ) else (
          strm
        ) in
        monitorExit (!*cs).monitor;
        strm
    ) in
  pop_frame();
  strm


(** Public API: Open a QUIC stream.  Returns NULL on failure. *)
let quic_OpenStream (cs:pointer connection) (stream:U64.t) : ST (quic_stream_or_null)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm =
    if U64.(stream >^ 0x3fffffffffffffffUL) then (* Invalid stream ID.  Must be less than 2^62 *)
      DLL.null_node
    else
      openStreamInternal cs stream
    in
  pop_frame();
  strm

(* Send data on a stream, without blocking until the data is actually sent.  Returns a waitable HANDLE. *)
let sendStreamNonBlocking (cs:pointer connection) (strm: quic_stream) (data:buffer_t) (datalength:U32.t) (fin:bool) : ST intptr_t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let strmm = strm_get_mutable strm in
  let ret =
      if strmm.sendState <> SendStreamSend then (
        print_string "Stream is not in a state where more data can be sent\n";
        nullptr
      ) else (
          // insert at tail of the segment list
          let seg:qstream_segment_fixed = {
            offset = strmm.nextWriteOffset;
            data = data;
            datalength = datalength;
            isApplicationOwned = true;
            fin = fin;
            available = createEvent 0l 0l;
            } in
          let pseg:qstream_segment = DLL.node_of HyperStack.root seg in
          DLL.dll_insert_at_tail strmm.segments pseg;
          upd_segments (DLL.node_val strm).qsm_state strmm.segments;
          let datalength64 = Cast.uint32_to_uint64 datalength in
          upd_nextWriteOffset (DLL.node_val strm).qsm_state U64.(strmm.nextWriteOffset +^ datalength64);
          setHasReadyToSend cs;
          if fin then
            upd_sendstate (DLL.node_val strm).qsm_state SendStreamDataSent;
          monitorExit (!*cs).monitor;
          seg.available
        ) in
  pop_frame();
  ret

(** Place a segment at the head of the list of segments to send *)
let putSegmentAtHead (strm:quic_stream) (segment:qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  DLL.dll_insert_at_head strmm.segments segment;
  upd_segments (DLL.node_val strm).qsm_state strmm.segments;
  pop_frame()

(** Split a segment in two, at offset 'offset'.  Return the first
    segment, and push the second back into the stream as the head *)
let splitSegmentAtOffset (strm:quic_stream) (segment:qstream_segment) (offset:U32.t): ST (qstream_segment)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset64 = Cast.uint32_to_uint64 offset in
  let data=(DLL.node_val segment).data in
  let firstseg = {
    offset=(DLL.node_val segment).offset;
    data=data;
    datalength=offset;
    isApplicationOwned = (DLL.node_val segment).isApplicationOwned;
    fin=false;
    available=(DLL.node_val segment).available;
  } in
  let data = B.offset data offset in
  let secondseg = {
    offset=U64.((DLL.node_val segment).offset+^offset64);
    data=data;
    datalength=U32.( (DLL.node_val segment).datalength-^offset);
    isApplicationOwned = (DLL.node_val segment).isApplicationOwned;
    fin=(DLL.node_val segment).fin;
    available=(DLL.node_val segment).available;
  } in
  let pfirstseg = DLL.node_of HyperStack.root firstseg in
  let psecondseg = DLL.node_of HyperStack.root secondseg in
  let strmm = strm_get_mutable strm in
  DLL.dll_insert_at_head strmm.segments psecondseg;
  upd_segments (DLL.node_val strm).qsm_state strmm.segments;
  pop_frame();
  pfirstseg

let sendStream (cs:pointer connection) (strm: quic_stream) (data:buffer_t) (datalength:U32.t) (fin:bool) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
    let available = sendStreamNonBlocking cs strm data datalength fin in
    waitForSingleObject available 0xfffffffful;
    closeHandle available

(* Public API: Send data on a stream.  This blocks until the data has been sent and ACK'd,
    then returns.  The caller is then able to free the data buffer. *)
let quic_SendStream (cs:pointer connection) (strm: quic_stream) (data:buffer_t) (datalength:U32.t) (fin:bool) : ST (err bool)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  // Validate that the stream ID is either bidi or uni and we are the client
  let id = (DLL.node_val strm).streamID in
  let isBidi = isStreamBidi id in
  let isCorrectDirection = (isStreamClientInitiated id) = (!*cs).is_client in
  if isBidi || isCorrectDirection then (
    sendStream cs strm data datalength fin;
    return true
  ) else (
    fail !$"Invalid direction for SendStream"
  )

(** Public API: Close a stream *)
let quic_CloseStream (cs:pointer connection) (strm:quic_stream): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let strmm = strm_get_mutable strm in
  upd_recvstate (DLL.node_val strm).qsm_state RecvStreamResetRead;
  upd_sendstate (DLL.node_val strm).qsm_state SendStreamResetRecvd;
  upd_error_code (DLL.node_val strm).qsm_state 0us;
  monitorExit (!*cs).monitor;
  pop_frame()

(** Enable the ping timer *)
let enablePingTimer (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let landcm = landc_get_mutable cs in
  setRepeatingTimer landcm.ping_alarm 500ul; // ping every 500ms
  pop_frame()

let setClientComplete (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  setEvent (!*cs).handshakeComplete;
  pop_frame()

let setServerAccept (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  pop_frame()

let packetSpaceFromEpoch (epoch:epoch) : ST packet_space
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  match epoch with
  | EpochInitial -> InitialSpace
  | Epoch0RTT -> ApplicationSpace
  | EpochHandshake -> HandshakeSpace
  | Epoch1RTT -> ApplicationSpace

(** data has arrived in a CRYPTO frame.  Forward it to miTLS *)
let processCryptoSegment (cs:pointer connection) (seg:qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "processCryptoSegment ENTER\n";

  // Mutable variables for the do/while loop
  let inbuf_cur = B.alloca (DLL.node_val seg).data 1ul in
  let inbuf_cur_length = B.alloca (DLL.node_val seg).datalength 1ul in
  C.Loops.do_while
      (fun h break -> live h inbuf_cur /\ (break ==> False))
      (fun _ ->
        let csm = conn_get_mutable cs in
        let outbuf_len = csm.maxPayloadSize in
        let outbuf = B.malloc HyperStack.root 0uy outbuf_len in
        let ctx:quic_process_ctx = {
          input = (!*inbuf_cur);
          input_len = (uint32_to_intptr_t (!*inbuf_cur_length));
          output = outbuf;
          output_len = (uint32_to_intptr_t outbuf_len);
          tls_error = 0us;
          consumed_bytes = nullptr;
          to_be_written = nullptr;
          tls_error_desc = nullptr;
          cur_reader_key = -1l;
          cur_writer_key = -1l;
          flags = 0us;
        } in
        let pctx = B.alloca ctx 1ul in
        print_string "  ffi_mitls_quic_process\n";
        let result = ffi_mitls_quic_process (csm.mitls_state) pctx in
        if result = 0l then failwith (of_literal "FFI_mitls_quic_process failed");

        let new_output_len = intptr_t_to_uint32 (!*pctx).output_len in
        if new_output_len = 0ul then (
          print_string "  No new output data\n";
          B.free outbuf
        ) else (
          print_string "  Sending new output data\n";
          // Send the data in the current packet space, before any ps/epoch update happens,
          // except when in 1RTT epoch... send using Handshake in that case.
          let epoch = if csm.epoch = Epoch1RTT then EpochHandshake else csm.epoch in
          let ps = packetSpaceFromEpoch epoch in
          let pss = getPacketSpaceState cs ps in
          let h = sendStreamNonBlocking cs pss.crypto_stream outbuf new_output_len false in
          closeHandle h;
          print_string "  Done sending\n"
        );

        let bytes_consumed = intptr_t_to_uint32 (!*pctx).consumed_bytes in
        inbuf_cur_length *= U32.( !*inbuf_cur_length -^ bytes_consumed);
        inbuf_cur *= B.offset !*inbuf_cur bytes_consumed;

        let bReadKeyChanged = (!*pctx).cur_reader_key <> csm.mitls_reader_key in
        let bWriteKeyChanged = (!*pctx).cur_writer_key <> csm.mitls_writer_key in
        let finished = (new_output_len = 0ul) &&
                       (not bReadKeyChanged) &&
                       (not bWriteKeyChanged) in
        upd_mitls_keys (!*cs).csm_state (!*pctx).cur_reader_key (!*pctx).cur_writer_key;

        if (bReadKeyChanged || bWriteKeyChanged) then (
          print_string "  key changed\n";
          let newEpoch =
            match csm.epoch with
            | EpochInitial -> (
              if (!*cs).is_client then (* Client, but no RTT inside quic_Handshake() *)
                EpochHandshake
              else (
                if bReadKeyChanged then (
                  Epoch0RTT (* Initial, and read key changed... 0-RTT is supported *)
                ) else (
                  EpochHandshake (* Initial, and read key didn't change.  No 0-RTT *)
                )
              )
            )
            | Epoch0RTT -> EpochHandshake
            | EpochHandshake -> Epoch1RTT
            | Epoch1RTT -> Epoch1RTT
            in
          upd_epoch (!*cs).csm_state newEpoch;
          upd_cstate (!*cs).csm_state Running;
          enablePingTimer cs;

          if bReadKeyChanged then (
            let keys = getTLSKeys cs (!*pctx).cur_reader_key in
            B.upd (!*cs).keys newEpoch keys
          );

          if bWriteKeyChanged then (
            let keys = getTLSKeys cs (!*pctx).cur_writer_key in
            B.upd (!*cs).keys newEpoch keys
          )
        );

        if finished && U16.((!*pctx).flags &^ qflag_complete) <> 0us then (
          if (!*cs).is_client then
            setClientComplete cs
          else
            setServerAccept cs

          //print_string "Releasing the miTLS handshake\n";
          // Release the miTLS handshake.
          //ffi_mitls_quic_free csm.mitls_state;
          //upd_mitls_state (!*cs).csm_state (uint32_to_intptr_t 0ul)
        );
        finished
        );
  print_string "processCryptoSegment EXIT\n";
  pop_frame()

(** data has arrived in a CRYPTO frame.  Forward it to miTLS *)
let processCrypto (cs:pointer connection) (strm:quic_stream): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm=strm_get_mutable strm in
  let seg = DLL.dll_head strmm.readysegments in
  // remove seg from the head of the list
  DLL.dll_remove_head strmm.readysegments;
  upd_readysegments (DLL.node_val strm).qsm_state strmm.readysegments;
  processCryptoSegment cs (DLL.coerce_non_null seg);
  deleteSegment (DLL.coerce_non_null seg);
  pop_frame()

(** Indicate new data is ready for the application to receive on a stream *)
let makeStreamDataAvailable (cs:pointer connection) (ps:packet_space) (strm:quic_stream) (seg:qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm=strm_get_mutable strm in
  let datalength = (DLL.node_val seg).datalength in
  let datalength64 = Cast.uint32_to_uint64 datalength in
  let nextReadOffset = U64.(strmm.nextReadOffset +^ datalength64) in
  upd_nextReadOffset (DLL.node_val strm).qsm_state nextReadOffset;
  DLL.dll_insert_at_tail strmm.readysegments seg;
  upd_readysegments (DLL.node_val strm).qsm_state strmm.readysegments;
  let pss = getPacketSpaceState cs ps in
  if strm = pss.crypto_stream then (
    processCrypto cs strm
  ) else (
    let csm = conn_get_mutable cs in
    let pholder = DLL.node_of HyperStack.root strm in
    DLL.dll_insert_at_tail csm.readystreams pholder;
    upd_readystreams (!*cs).csm_state csm.readystreams;
    setEvent (!*cs).streamDataAvailable
  );
  pop_frame()

(** Data returned from quic_RecvStream *)
type data_recv  = {
  stream_id: U64.t;
  recv_data: buffer_t;
  recv_len: U32.t;
  }

type reset_recv = {
  rst_stream_id: U64.t;
  rst_error_code: U16.t;
  }

type stream_recv =
  | ReceivedData of data_recv
  | Reset of reset_recv
  | ConnectionError of C.String.t

let recvStream (cs:pointer connection)  : ST stream_recv
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let csm = conn_get_mutable cs in
  let strmholder = DLL.dll_head csm.readystreams in
  DLL.dll_remove_head csm.readystreams;
  let strm = (DLL.node_val (DLL.coerce_non_null strmholder)) in
  (* FIXME[jb]: We don't support freeing in the dlist iface yet *)
  // B.free strmholder;
  upd_readystreams (!*cs).csm_state csm.readystreams;
  if DLL.is_empty csm.readystreams then
    resetEvent (!*cs).streamDataAvailable;

  let strmm = strm_get_mutable strm in
  let ret = if strmm.recvState = RecvStreamResetRecvd then (
     upd_recvstate  (DLL.node_val strm).qsm_state RecvStreamResetRead;
     let r = {  rst_stream_id = (DLL.node_val strm).streamID; rst_error_code = strmm.error_code;  } in
     Reset r
  ) else (
      // Get the first ready segment
      let seg = DLL.dll_head strmm.readysegments in
      // remove seg from the head of the list
      DLL.dll_remove_head strmm.readysegments;
      upd_readysegments (DLL.node_val strm).qsm_state strmm.readysegments;
      if (DLL.node_val (DLL.coerce_non_null seg)).fin then (
        upd_recvstate (DLL.node_val strm).qsm_state RecvStreamDataRead
      );
      // check if the next partial segment is ready for next recv
      let nextseg = DLL.dll_head strmm.partialsegments in
      if not (DLL.is_null_node nextseg) then (
        print_string "Next segment is present\n";
        if (DLL.node_val (DLL.coerce_non_null nextseg)).offset = strmm.nextReadOffset then (
          DLL.dll_remove_mid strmm.partialsegments (DLL.coerce_non_null nextseg);
          upd_partialsegments (DLL.node_val strm).qsm_state strmm.partialsegments;
          print_string "Making next segment available\n";
          makeStreamDataAvailable cs ApplicationSpace strm (DLL.coerce_non_null nextseg)
        )
      );
      monitorExit (!*cs).monitor;
      let ret = {
        stream_id = (DLL.node_val strm).streamID;
        recv_data = (DLL.node_val (DLL.coerce_non_null seg)).data;
        recv_len =  (DLL.node_val (DLL.coerce_non_null seg)).datalength;
      } in
      (* FIXME[jb]: We don't support freeing in dlist iface yet. *)
      // B.free seg; (* Don't call deleteSegment here, as it would free the data that we are returning *)
      ReceivedData ret
  ) in
  ret


(** Public API: Receive data on a stream.  This will block until data arrives.  It returns the number of bytes written into the buffer. *)
let quic_RecvStream (cs:pointer connection) : ST stream_recv
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  waitForSingleObject (!*cs).streamDataAvailable 0xfffffffful;

  monitorEnter (!*cs).monitor;
  // Get the first ready stream
  let csm = conn_get_mutable cs in
  let ret = if csm.cstate <> Running then
    ConnectionError csm.closedReason
  else
    recvStream cs in
  pop_frame();
  ret

(** Public API:  Query if the 'fin' marker has been received, for end of the stream *)
let quic_StreamIsFin (cs:pointer connection) (strm:quic_stream): ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let strmm = strm_get_mutable strm in
  let result = strmm.recvState = RecvStreamDataRead in
  monitorExit (!*cs).monitor;
  pop_frame();
  result

(** Retrieve the next stream segment from .segments, ready to send *)
let getNextSegment (strm:quic_stream): ST (qstream_segment)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  let seg = DLL.dll_head strmm.segments in
  // Remove from head of the list
  DLL.dll_remove_head strmm.segments;
  upd_segments (DLL.node_val strm).qsm_state strmm.segments;
  pop_frame();
  DLL.coerce_non_null seg

(** Merge a newly-arrived segment into the current segment list.  This must handle overlapping
    and duplicated segments arriving out of order. *)
let splitSegment (seg:qstream_segment) (firstlength:U32.t): ST ((qstream_segment) * (qstream_segment))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let data = (DLL.node_val seg).data in
  let firstdata = B.malloc HyperStack.root 0uy firstlength in
  B.blit data 0ul firstdata 0ul firstlength;
  let seconddatalength = U32.((DLL.node_val seg).datalength -^ firstlength) in
  let seconddata = B.malloc HyperStack.root 0uy seconddatalength in
  B.blit data firstlength seconddata 0ul seconddatalength;
  let first:qstream_segment_fixed = {
    offset = (DLL.node_val seg).offset;
    data = firstdata;
    datalength = firstlength;
    isApplicationOwned = false;
    fin = false;
    available = createEvent 0l 0l;
  } in
  let firstlength64 = Cast.uint32_to_uint64 firstlength in
  let secondoffset = U64.(first.offset +^ firstlength64) in
  let second:qstream_segment_fixed = {
    offset = secondoffset;
    data = seconddata;
    datalength = seconddatalength;
    isApplicationOwned = false;
    fin = (DLL.node_val seg).fin;
    available = createEvent 0l 0l;
  } in
  let pfirst = DLL.node_of HyperStack.root first in
  let psecond = DLL.node_of HyperStack.root second in
  deleteSegment seg;
  pop_frame();
  (pfirst, psecond)

(** Compute the end of a segment (offset+datalength) *)
let segmentEnd (seg:qstream_segment) : ST U64.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = (DLL.node_val seg).offset in
  let length = (DLL.node_val seg).datalength in
  let segend = U64.(offset +^ (Cast.uint32_to_uint64 length)) in
  pop_frame();
  segend

let verifyDataReceivedSize (cs:pointer connection) (seg:qstream_segment): ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let datalength32 = (DLL.node_val seg).datalength in
  let datalength = Cast.uint32_to_uint64 datalength32 in
  let newDataReceived = U64.( csm.dataReceived +^ datalength) in
  let ret =
    if U64.(newDataReceived >^ csm.maxDataLocal) then (
      B.free (DLL.node_val seg).data;
      (* FIXME[jb]: We don't support freeing in dlist iface yet *)
      // B.free seg;
      abortConnection cs 0x3us;  // abort with FLOW_CONTROL_ERROR
      false
    ) else (
      upd_dataReceived (!*cs).csm_state newDataReceived;
      true
    ) in
  pop_frame();
  ret

(** Body of the do/while loop.  Returns the new list, and true to keep iterating, or false to stop *)
let mergeSegmentsBody (cs:pointer connection) (partialsegments: qstream_segment_list) (c:qstream_segment) (seg:qstream_segment) : ST (qstream_segment_list * bool)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let c_offset = (DLL.node_val c).offset in
  let seg_offset = (DLL.node_val seg).offset in
  let c_segmentend = segmentEnd c in
  let seg_segmentend = segmentEnd seg in
  let ret =
    if (U64.lt c_segmentend c_offset) && (not (DLL.fast_has_prev partialsegments c)) then (
      // seg fits before the first element with no overlap.  Insert it.
      if verifyDataReceivedSize cs seg then (
        DLL.dll_insert_before c partialsegments seg;
        (partialsegments,false) // done
      ) else (
        (partialsegments,false) // done
      )
    ) else if U64.gte seg_offset c_segmentend then (
      // seg goes after current
      if not (DLL.fast_has_next partialsegments c) then (
        // at the end of the list.  Add to the end.
        if verifyDataReceivedSize cs seg then (
          DLL.dll_insert_at_tail partialsegments seg;
          (partialsegments, false) // done
        ) else (
          (partialsegments, false) // done
        )
      ) else (
        // advance to the next element
        (partialsegments, true)
      )
    ) else if (U64.gte seg_offset c_offset) && (U64.lte seg_segmentend c_segmentend) then (
      // seg is contained within cv.  Drop seg completely
      (partialsegments, false)
    ) else if (U64.lt seg_offset c_offset) && (seg_segmentend = c_offset) then (
      // seg is adjacent to c
      if verifyDataReceivedSize cs seg then (
        DLL.dll_insert_before c partialsegments seg;
        (partialsegments, false) // done
      ) else (
        (partialsegments, false) // done
      )
    ) else if (U64.lt seg_offset c_offset) && (U64.gte seg_segmentend c_offset) then (
      // seg overlaps with the beginning of cv.  Spit and insert the first part.
      let l = U64.(c_offset -^ seg_offset) in
      let l32 = Cast.uint64_to_uint32 l in
      let f,_ = splitSegment seg l32 in
      if verifyDataReceivedSize cs seg then (
        DLL.dll_insert_before c partialsegments f;
        (partialsegments, false) // done
      ) else (
        (partialsegments, false) // done
      )
    ) else (
      (partialsegments,true) // advancing
    )
    in
  pop_frame();
  ret

(** Search inside the partialsegments list...
  if seg is entirely in a gap, insert it
  if seg overlaps with another...
    if it is exactly overlapping, drop it
    if it overlaps from the front, insert before, after truncting seg
    if it overlaps from the rear, insert after, after pruning off the start *)
let mergeSegments (cs:pointer connection) (strm:quic_stream) (seg:qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  let list = strmm.partialsegments in
  let list =
    if DLL.is_empty list then (
      // first segment in list
      if verifyDataReceivedSize cs seg then
        (DLL.dll_insert_at_head list seg; list)
      else
        list
    ) else (
      let lv = DLL.coerce_non_null (DLL.dll_tail list) in // last value
      if U64.gte (DLL.node_val seg).offset (segmentEnd lv) then (
        // segment appends to the end of the list
        if verifyDataReceivedSize cs seg then
          (DLL.dll_insert_at_tail list seg; list)
        else
          list
      ) else if U64.gte (DLL.node_val seg).offset (DLL.node_val lv).offset then (
        // segment overlaps with the end of the list
        let l64 = U64.((segmentEnd lv) -^ (DLL.node_val seg).offset) in
        let l = Cast.uint64_to_uint32 l64 in
        if U32.lt l (DLL.node_val seg).datalength then (
          let _,s = splitSegment seg l in
          if verifyDataReceivedSize cs s then
            (DLL.dll_insert_at_tail list s; list)
          else
            list
        ) else (
          // They exactly overlap and there is nothing to do
          list
        )
      ) else (
        let c:(pointer qstream_segment) = B.alloca (DLL.coerce_non_null (DLL.dll_head list)) 1ul in
        let listmutable = B.alloca list 1ul in
        C.Loops.do_while
          (fun h break -> live h c /\ (break ==> False))
          (fun _ ->
            let list,keepgoing = mergeSegmentsBody cs list (!*c) seg in
            if not keepgoing then (
              listmutable *= list
            );
            c *= DLL.coerce_non_null (DLL.next_node list (!*c));
            not keepgoing // do... while keepgoing
          );
        !*listmutable
      )
    )
  in
  upd_partialsegments (DLL.node_val strm).qsm_state list;
  pop_frame()

(** Stream data has arrived from the peer.  Merge it in, taking care of out-of-order and
    partial/overlapping/disjoint segments *)
let streamRecvInternal (cs:pointer connection) (ps:packet_space) (strm:quic_stream) (seg:qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  if strmm.recvState = RecvStreamRecv then (
      if (DLL.node_val seg).offset = strmm.nextReadOffset then (
          if verifyDataReceivedSize cs seg then
            makeStreamDataAvailable cs ps strm seg
       ) else if U64.gt (segmentEnd seg) strmm.nextReadOffset then (
          // Data has arrived out of order.  Buffer it for later.
          // Note that the partial segments may be overlapping.
          mergeSegments cs strm seg;
          let pKeepGoing = B.alloca (not (DLL.is_null_node (DLL.dll_head strmm.partialsegments))) 1ul in
          let inv h = DLL.node_valid h seg in
          let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
            !*pKeepGoing
          in
          let body() : Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
              let strmm = strm_get_mutable strm in
              let seg = DLL.coerce_non_null (DLL.dll_head strmm.partialsegments) in
              let seg_offset = (DLL.node_val seg).offset in
              let seg_end = segmentEnd seg in
              if (U64.lte seg_offset strmm.nextReadOffset) &&
                 (U64.gt seg_end strmm.nextReadOffset) then (
                // The first segment overlaps with NextReadOffset.
                DLL.dll_remove_mid strmm.partialsegments seg;
                upd_partialsegments (DLL.node_val strm).qsm_state strmm.partialsegments;
                let seg =
                  if U64.lt seg_offset strmm.nextReadOffset then (
                    let l = U64.(strmm.nextReadOffset -^ seg_offset) in
                    let _,s = splitSegment seg (Cast.uint64_to_uint32 l) in
                    s
                  ) else
                    seg
                in
                makeStreamDataAvailable cs ps strm seg;
                let strmm = strm_get_mutable strm in
                pKeepGoing *= not (DLL.is_null_node (DLL.dll_head strmm.partialsegments)) // loop while the list is non-empty
              ) else (
                pKeepGoing *= false // stop looping
              )
          in
          C.Loops.while test body
       ) // else dropping duplicated data
   ); // else dropping data as the stream isn't in RecvStreamRecv
   pop_frame()

(** Stream data has arrived from the peer.  Merge it in, taking care of out-of-order and
    partial/overlapping/disjoint segments *)
let streamRecv (cs:pointer connection) (id:U64.t) (seg:qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let isInCorrectStream = ((isStreamClientInitiated id) = (!*cs).is_client) in
  if (isStreamUni id) && isInCorrectStream then
    failwith (of_literal "Receiving data from an unexpected uni stream direction");
  // bugbug: ensure that the stream ID is in bounds
  let strm = openStreamInternal cs id in
  if DLL.is_null_node strm then
    print_string (sprintf "Dropping received data for invalid stream ID %uL\n" id)
  else
    streamRecvInternal cs ApplicationSpace (DLL.coerce_non_null strm) seg;
  pop_frame()

//bugbug: probably want to handle miTLS failures more gracefully than returning unit.
let streamRecvInitialCrypto (eng:pointer engine) (seg:qstream_segment) (plaintext_cid:connectionid_t): ST (pointer connection)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let cs = createServerConnection eng plaintext_cid in
  let pss = getPacketSpaceState cs InitialSpace in
  let strm = pss.crypto_stream in
  processCryptoSegment cs seg;
  let nextReadOffset = (DLL.node_val seg).datalength in
  let nextReadOffset64 = Cast.uint32_to_uint64 nextReadOffset in
  upd_nextReadOffset (DLL.node_val strm).qsm_state nextReadOffset64;
  pop_frame();
  cs

(** Set the maximum allowable offset for a given stream response to MAX_STREAM_DATA *)
let setMaxStreamData (cs:pointer connection) (stream:U64.t) (maxdata:U64.t) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm = quic_OpenStream cs stream in
  let strmm = strm_get_mutable (DLL.coerce_non_null strm) in
  let maxdata = if U64.lt maxdata strmm.maxStreamData then
    strmm.maxStreamData
  else
    maxdata
  in
  upd_maxStreamData (DLL.node_val (DLL.coerce_non_null strm)).qsm_state maxdata;
  pop_frame()

(** Called when a previously sent stream segment has been ACK'd by the peer.  This
    releases the data *)
let ackStream (cs:pointer connection) (t:streamRecoveryTracker): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  setEvent (DLL.node_val (t.segment)).available;
  pop_frame()

(** Called when a previously sent CRYPTO segment has been ACK'd by the peer.  This
    releases the data *)
let ackCrypto (cs:pointer connection) (t:cryptoRecoveryTracker): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  setEvent (DLL.node_val (t.cryptosegment)).available;
  pop_frame()

(** Called by LossAndCongestion when it determines that a packet has been lost,
    and the stream data must be retransmitted. *)
let lostStream (cs:pointer connection) (t:streamRecoveryTracker): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let strm = findStream csm t.recoverystreamID in
  // Place this segment back in the list of segments to send
  let strmm = strm_get_mutable (DLL.coerce_non_null strm) in
  let seg = t.segment in
  DLL.dll_insert_at_head strmm.segments seg;
  upd_segments (DLL.node_val (DLL.coerce_non_null strm)).qsm_state strmm.segments;
  upd_dataSentSub (!*cs).csm_state (DLL.node_val seg).datalength;
  setHasReadyToSend cs;
  pop_frame()

(** Called by LossAndCongestion when it determines that a packet has been lost,
    and the stream data must be retransmitted. *)
let lostCrypto (cs:pointer connection) (ps:packet_space) (t:cryptoRecoveryTracker): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let pss = getPacketSpaceState cs ps in
  let strm = pss.crypto_stream in
  // Place this segment back in the list of segments to send
  let strmm = strm_get_mutable strm in
  let seg = t.cryptosegment in
  DLL.dll_insert_at_head strmm.segments seg;
  upd_segments (DLL.node_val strm).qsm_state strmm.segments;
  setHasReadyToSend cs;
  pop_frame()

(** Reset a stream in response to RST_STREAM *)
let rstStream (cs:pointer connection) (stream:U64.t) (errorCode:U16.t) (finalOffset:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm = DLL.coerce_non_null (quic_OpenStream cs stream) in
  upd_recvstate (DLL.node_val strm).qsm_state RecvStreamResetRecvd;
  upd_error_code (DLL.node_val strm).qsm_state errorCode;
  print_string (sprintf "RST_STREAM StreamID=%uL errorCode=%us\n" stream errorCode);
  (* Now report the stream as ready, so QUIC_recv() will wake for it *)
  let csm = conn_get_mutable cs in
  let pholder = DLL.node_of HyperStack.root strm in
  DLL.dll_insert_at_tail csm.readystreams pholder;
  upd_readystreams (!*cs).csm_state csm.readystreams;
  setEvent (!*cs).streamDataAvailable;
  pop_frame()
