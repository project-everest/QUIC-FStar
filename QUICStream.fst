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

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
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
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  let hasmore = if  DLL.is_empty strmm.segments then false else true in
  pop_frame();
  hasmore

(** Find a quic_stream that has data ready for transmission.  May return null
    if there is no ready stream. *)
let findReadyStream (cs:pointer connection): ST (pointer_or_null quic_stream)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let strm =
    if U64.(csm.dataSent >=^ csm.maxDataPeer) then
      null // Not permitted to send more stream data when the connection  is at maxDataPeer
    else (
      let head : quic_stream = DLL.dll_head (!*((!*cs).csm_state)).streams in
      let pp = B.alloca head 1ul in
      let pstrm = B.alloca head 1ul in (* REVIEW[jb]: changed null to head here, is it ok? *)
      let headisnull = DLL.is_empty (!*((!*cs).csm_state)).streams in
      let pstop = B.alloca headisnull 1ul in
      let inv h = DLL.node_valid h (B.get h pp 0) in
      let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
        not !*pstop
      in
      let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
        let isready = hasMoreToSend !*pp in
        if isready then (
          pstrm *= !*pp
          );
        pp *= DLL.next_node (!*((!*cs).csm_state)).streams (!*pp);
        pstop *= ((DLL.has_next (!*((!*cs).csm_state)).streams (!*pp)) || isready)
      in
      C.Loops.while test body;
      pstrm
      ) in
  pop_frame();
  strm

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
      if hasMoreToSend !*pssInitial.crypto_stream ||
         (pssInitial.sendAckOnlyIfNeeded && pssInitial.outgoingAckCount <> 0ul)then
        Some InitialSpace
      else if U32.(epochIndex >=^ epochIndexHandshake) then (
        let pssHandshake = getPacketSpaceState cs HandshakeSpace in
        if hasMoreToSend !*pssHandshake.crypto_stream ||
           (pssHandshake.sendAckOnlyIfNeeded && pssHandshake.outgoingAckCount <> 0ul) then (
          Some HandshakeSpace
        ) else if epochIndex = epochIndex1RTT then (
          let pssApplication = getPacketSpaceState cs ApplicationSpace in
          let fixedframeListEmpty = DLL.is_empty csm.fixedframes in
          let hasMore = csm.pingPending ||
                        not fixedframeListEmpty ||
                        hasMoreToSend !*pssApplication.crypto_stream ||
                        (pssApplication.sendAckOnlyIfNeeded && pssApplication.outgoingAckCount <> 0ul) ||
                        not (is_null (findReadyStream cs)) in
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
  let pff = DLL.node_of fixed in
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
  let pff = DLL.node_of fixed in
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
  let pholder = DLL.node_of cs in
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
let findStream (csm:connection_mutable) (stream:U64.t): ST (pointer_or_null quic_stream)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let head = DLL.dll_head csm.streams in
  let pp : pointer_or_null quic_stream = B.alloca head 1ul in
  let pstrm = B.alloca head 1ul in
  let inv h = B.live h pp in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    DLL.has_next csm.streams !*pp
  in
  let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    if (DLL.node_val (!*pp)).streamID = stream then (
      pstrm *= !*pp;
      pp *= admit ()
    ) else (
      pp *= DLL.next_node csm.streams (!*pp)
    )
  in
  C.Loops.while test body;
  let strm = pstrm in
  pop_frame();
  strm

(** Free the memory associated with a segment *)
let deleteSegment (seg:pointer qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
    push_frame();
    (* Quick check that the segment is not live.  This isn't sufficient, as a list with
       exactly one element won't trigger this check, as the one element's
       flink and blink are both null *)
    if not (is_null (!*seg).flink) || not (is_null (!*seg).blink)
        then failwith (of_literal "deleteSegment of a segment still on a list");

    if not (!*seg).p.isApplicationOwned then B.free (!*seg).p.data;
    let h = (!*seg).p.available in
    if h <> (uint32_to_intptr_t 0ul) then closeHandle h;
    B.free seg;
    pop_frame()

(** Create a new stream instance *)
let createStream (stream:U64.t) (maxData:U64.t) : ST (pointer quic_stream)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let pstrm =
    let strmm:quic_stream_mutable = {
      recvState = RecvStreamRecv;
      partialsegments=empty_list;
      readysegments=empty_list;
      nextReadOffset = 0UL;
      error_code=0us;

      sendState = SendStreamSend;
      nextWriteOffset = 0UL;
      maxStreamData = maxData;
      segments=empty_list;
      } in
    let strmr = B.malloc HyperStack.root strmm 1ul in
    let strmf:quic_stream_fixed = {
      streamID = stream;
      qsm_state = strmr;
    } in
    let strm = empty_entry strmf in
    B.malloc HyperStack.root strm 1ul in
  pop_frame();
  pstrm

(** Open a QUIC stream.  Called from quic_OpenStream() as well as from the frame-recieve path *)
let openStreamInternal (cs:pointer connection) (stream:U64.t) : ST (pointer_or_null quic_stream)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm = (
      monitorEnter (!*cs).monitor;
      let csm = conn_get_mutable cs in
      let strm = findStream csm stream in
      let strm =
        if is_null strm then (
          let maxStreamID = if (isStreamBidi stream) then csm.maxStreamID_BIDIPeer else csm.maxStreamID_UNIPeer in
          if U64.gt stream maxStreamID then
            null
          else (
            let pstrm = createStream stream csm.defaultMaxStreamData in
            let list = insertTailList csm.streams pstrm in
            upd_streams (!*cs).csm_state list;
            pstrm
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
let quic_OpenStream (cs:pointer connection) (stream:U64.t) : ST (pointer_or_null quic_stream)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm =
    if U64.(stream >^ 0x3fffffffffffffffUL) then (* Invalid stream ID.  Must be less than 2^62 *)
      null
    else
      openStreamInternal cs stream
    in
  pop_frame();
  strm
  
(* Send data on a stream, without blocking until the data is actually sent.  Returns a waitable HANDLE. *)
let sendStreamNonBlocking (cs:pointer connection) (strm: pointer quic_stream) (data:buffer_t) (datalength:U32.t) (fin:bool) : ST intptr_t
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
          let lseg:qstream_segment = empty_entry seg in
          let pseg = B.malloc HyperStack.root lseg 1ul in
          let list = insertTailList strmm.segments pseg in
          upd_segments (!*strm).p.qsm_state list;
          let datalength64 = Cast.uint32_to_uint64 datalength in
          upd_nextWriteOffset (!*strm).p.qsm_state U64.(strmm.nextWriteOffset +^ datalength64);
          setHasReadyToSend cs;
          if fin then
            upd_sendstate (!*strm).p.qsm_state SendStreamDataSent;
          monitorExit (!*cs).monitor;
          seg.available
        ) in
  pop_frame();
  ret

(** Place a segment at the head of the list of segments to send *)
let putSegmentAtHead (strm:pointer quic_stream) (segment:pointer qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  let list = insertHeadList strmm.segments segment in
  upd_segments (!*strm).p.qsm_state list;
  pop_frame()

(** Split a segment in two, at offset 'offset'.  Return the first
    segment, and push the second back into the stream as the head *)
let splitSegmentAtOffset (strm:pointer quic_stream) (segment:pointer qstream_segment) (offset:U32.t): ST (pointer qstream_segment)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset64 = Cast.uint32_to_uint64 offset in
  let data=(!*segment).p.data in
  let firstseg = {
    offset=(!*segment).p.offset;
    data=data;
    datalength=offset;
    isApplicationOwned = (!*segment).p.isApplicationOwned;
    fin=false;
    available=(!*segment).p.available;
  } in
  let data = B.offset data offset in
  let secondseg = {
    offset=U64.((!*segment).p.offset+^offset64);
    data=data;
    datalength=U32.( (!*segment).p.datalength-^offset);
    isApplicationOwned = (!*segment).p.isApplicationOwned;
    fin=(!*segment).p.fin;
    available=(!*segment).p.available;
  } in
  let lfirstseg:qstream_segment = empty_entry firstseg in
  let lsecondseg:qstream_segment = empty_entry secondseg in
  let pfirstseg = B.malloc HyperStack.root lfirstseg 1ul in
  let psecondseg = B.malloc HyperStack.root lsecondseg 1ul in
  let strmm = strm_get_mutable strm in
  let list = insertHeadList strmm.segments psecondseg in
  upd_segments (!*strm).p.qsm_state list;
  pop_frame();
  pfirstseg

let sendStream (cs:pointer connection) (strm: pointer quic_stream) (data:buffer_t) (datalength:U32.t) (fin:bool) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
    let available = sendStreamNonBlocking cs strm data datalength fin in
    waitForSingleObject available 0xfffffffful;
    closeHandle available

(* Public API: Send data on a stream.  This blocks until the data has been sent and ACK'd,
    then returns.  The caller is then able to free the data buffer. *)
let quic_SendStream (cs:pointer connection) (strm: pointer quic_stream) (data:buffer_t) (datalength:U32.t) (fin:bool) : ST (err bool)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  // Validate that the stream ID is either bidi or uni and we are the client
  let id = (!*strm).p.streamID in
  let isBidi = isStreamBidi id in
  let isCorrectDirection = (isStreamClientInitiated id) = (!*cs).is_client in
  if isBidi || isCorrectDirection then (
    sendStream cs strm data datalength fin;
    return true
  ) else (
    fail !$"Invalid direction for SendStream"
  )

(** Public API: Close a stream *)
let quic_CloseStream (cs:pointer connection) (strm:pointer quic_stream): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let strmm = strm_get_mutable strm in
  upd_recvstate (!*strm).p.qsm_state RecvStreamResetRead;
  upd_sendstate (!*strm).p.qsm_state SendStreamResetRecvd;
  upd_error_code (!*strm).p.qsm_state 0us;
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
let processCryptoSegment (cs:pointer connection) (seg:pointer qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "processCryptoSegment ENTER\n";
  
  // Mutable variables for the do/while loop
  let inbuf_cur = B.alloca (!*seg).p.data 1ul in
  let inbuf_cur_length = B.alloca (!*seg).p.datalength 1ul in
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
let processCrypto (cs:pointer connection) (strm:pointer quic_stream): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm=strm_get_mutable strm in
  let seg = strmm.readysegments.lhead in
  // remove seg from the head of the list
  let list = removeEntryList strmm.readysegments seg in
  upd_readysegments (!*strm).p.qsm_state list;
  processCryptoSegment cs seg;
  deleteSegment seg;
  pop_frame()

(** Indicate new data is ready for the application to receive on a stream *)
let makeStreamDataAvailable (cs:pointer connection) (ps:packet_space) (strm:pointer quic_stream) (seg:pointer qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm=strm_get_mutable strm in
  let datalength = (!*seg).p.datalength in
  let datalength64 = Cast.uint32_to_uint64 datalength in
  let nextReadOffset = U64.(strmm.nextReadOffset +^ datalength64) in
  upd_nextReadOffset (!*strm).p.qsm_state nextReadOffset;
  let list = insertTailList strmm.readysegments seg in
  upd_readysegments (!*strm).p.qsm_state list;
  let pss = getPacketSpaceState cs ps in
  if strm = pss.crypto_stream then (
    processCrypto cs strm
  ) else (
    let csm = conn_get_mutable cs in
    let holder = empty_entry strm in
    let pholder = B.malloc HyperStack.root holder 1ul in
    let list = insertTailList csm.readystreams pholder in
    upd_readystreams (!*cs).csm_state list;
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
  let strmholder = csm.readystreams.lhead in
  let list = removeEntryList csm.readystreams strmholder in
  let strm = (!*strmholder).p in
  B.free strmholder;
  upd_readystreams (!*cs).csm_state list;
  if is_null list.lhead then // list is empty
    resetEvent (!*cs).streamDataAvailable;

  let strmm = strm_get_mutable strm in
  let ret = if strmm.recvState = RecvStreamResetRecvd then (
     upd_recvstate  (!*strm).p.qsm_state RecvStreamResetRead;
     let r = {  rst_stream_id = (!*strm).p.streamID; rst_error_code = strmm.error_code;  } in
     Reset r
  ) else (
      // Get the first ready segment
      let seg = strmm.readysegments.lhead in
      // remove seg from the head of the list
      let list = removeEntryList strmm.readysegments seg in
      upd_readysegments (!*strm).p.qsm_state list;
      if (!*seg).p.fin then (
        upd_recvstate (!*strm).p.qsm_state RecvStreamDataRead
      );
      // check if the next partial segment is ready for next recv
      let nextseg = strmm.partialsegments.lhead in
      if not (is_null nextseg) then (
        print_string "Next segment is present\n";
        if (!*nextseg).p.offset = strmm.nextReadOffset then (
          let list = removeEntryList strmm.partialsegments nextseg in
          upd_partialsegments (!*strm).p.qsm_state list;
          print_string "Making next segment available\n";
          makeStreamDataAvailable cs ApplicationSpace strm nextseg
        )
      );
      monitorExit (!*cs).monitor;
      let ret = {
        stream_id = (!*strm).p.streamID;
        recv_data = (!*seg).p.data;
        recv_len =  (!*seg).p.datalength;
      } in
      B.free seg; (* Don't call deleteSegment here, as it would free the data that we are returning *)
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
let quic_StreamIsFin (cs:pointer connection) (strm:pointer quic_stream): ST bool
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
let getNextSegment (strm:pointer quic_stream): ST (pointer qstream_segment)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  let seg = strmm.segments.lhead in
  // Remove from head of the list
  let list = removeEntryList strmm.segments seg in
  upd_segments (!*strm).p.qsm_state list;
  pop_frame();
  seg

(** Merge a newly-arrived segment into the current segment list.  This must handle overlapping
    and duplicated segments arriving out of order. *)
let splitSegment (seg:pointer qstream_segment) (firstlength:U32.t): ST ((pointer qstream_segment) * (pointer qstream_segment))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let data = (!*seg).p.data in
  let firstdata = B.malloc HyperStack.root 0uy firstlength in
  B.blit data 0ul firstdata 0ul firstlength;
  let seconddatalength = U32.((!*seg).p.datalength -^ firstlength) in
  let seconddata = B.malloc HyperStack.root 0uy seconddatalength in
  B.blit data firstlength seconddata 0ul seconddatalength;
  let first:qstream_segment_fixed = {
    offset = (!*seg).p.offset;
    data = firstdata;
    datalength = firstlength;
    isApplicationOwned = false;
    fin = false;
    available = createEvent 0l 0l;
  } in
  let first = empty_entry first in
  let firstlength64 = Cast.uint32_to_uint64 firstlength in
  let secondoffset = U64.(first.p.offset +^ firstlength64) in
  let second:qstream_segment_fixed = {
    offset = secondoffset;
    data = seconddata;
    datalength = seconddatalength;
    isApplicationOwned = false;
    fin = (!*seg).p.fin;
    available = createEvent 0l 0l;
  } in
  let second = empty_entry second in
  let pfirst = B.malloc HyperStack.root first 1ul in
  let psecond = B.malloc HyperStack.root second 1ul in
  deleteSegment seg;
  pop_frame();
  (pfirst, psecond)

(** Compute the end of a segment (offset+datalength) *)
let segmentEnd (seg:pointer qstream_segment) : ST U64.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = (!*seg).p.offset in
  let length = (!*seg).p.datalength in
  let segend = U64.(offset +^ (Cast.uint32_to_uint64 length)) in
  pop_frame();
  segend

let verifyDataReceivedSize (cs:pointer connection) (seg:pointer qstream_segment): ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let datalength32 = (!*seg).p.datalength in
  let datalength = Cast.uint32_to_uint64 datalength32 in
  let newDataReceived = U64.( csm.dataReceived +^ datalength) in
  let ret =
    if U64.(newDataReceived >^ csm.maxDataLocal) then (
      B.free (!*seg).p.data;
      B.free seg;
      abortConnection cs 0x3us;  // abort with FLOW_CONTROL_ERROR
      false
    ) else (
      upd_dataReceived (!*cs).csm_state newDataReceived;
      true
    ) in
  pop_frame();
  ret

(** Body of the do/while loop.  Returns the new list, and true to keep iterating, or false to stop *)
let mergeSegmentsBody (cs:pointer connection) (partialsegments: qstream_segment_list) (c:pointer qstream_segment) (seg:pointer qstream_segment) : ST (qstream_segment_list * bool)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let c_offset = (!*c).p.offset in
  let seg_offset = (!*seg).p.offset in
  let c_segmentend = segmentEnd c in
  let seg_segmentend = segmentEnd seg in
  let ret =
    if (U64.lt c_segmentend c_offset) && (c=partialsegments.lhead) then (
      // seg fits before the first element with no overlap.  Insert it.
      if verifyDataReceivedSize cs seg then (
        let partialsegments = insertEntryBefore partialsegments c seg in
        (partialsegments,false) // done
      ) else (
        (partialsegments,false) // done
      )
    ) else if U64.gte seg_offset c_segmentend then (
      // seg goes after current
      if c = partialsegments.ltail then (
        // at the end of the list.  Add to the end.
        if verifyDataReceivedSize cs seg then (
          let partialsegments = insertTailList partialsegments seg in
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
        let partialsegments = insertEntryBefore partialsegments c seg in
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
        let partialsegments = insertEntryBefore partialsegments c f in
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
let mergeSegments (cs:pointer connection) (strm:pointer quic_stream) (seg:pointer qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  let list = strmm.partialsegments in
  let list =
    if is_null list.lhead then (
      // first segment in list
      if verifyDataReceivedSize cs seg then
        insertHeadList list seg
      else
        list
    ) else (
      let lv = list.ltail in // last value
      if U64.gte (!*seg).p.offset (segmentEnd lv) then (
        // segment appends to the end of the list
        if verifyDataReceivedSize cs seg then
          insertTailList list seg
        else
          list
      ) else if U64.gte (!*seg).p.offset (!*lv).p.offset then (
        // segment overlaps with the end of the list
        let l64 = U64.((segmentEnd lv) -^ (!*seg).p.offset) in
        let l = Cast.uint64_to_uint32 l64 in
        if U32.lt l (!*seg).p.datalength then (
          let _,s = splitSegment seg l in
          if verifyDataReceivedSize cs s then
            insertTailList list s
          else
            list
        ) else (
          // They exactly overlap and there is nothing to do
          list
        )
      ) else (
        let c:(pointer (pointer qstream_segment)) = B.alloca list.lhead 1ul in
        let listmutable = B.alloca list 1ul in
        C.Loops.do_while
          (fun h break -> live h c /\ (break ==> False))    
          (fun _ -> 
            let list,keepgoing = mergeSegmentsBody cs list (!*c) seg in
            if not keepgoing then (
              listmutable *= list
            );
            c *= (!*(!*c)).flink;
            not keepgoing // do... while keepgoing
          );                           
        !*listmutable
      )
    )
  in
  upd_partialsegments (!*strm).p.qsm_state list;
  pop_frame()

(** Stream data has arrived from the peer.  Merge it in, taking care of out-of-order and
    partial/overlapping/disjoint segments *)
let streamRecvInternal (cs:pointer connection) (ps:packet_space) (strm:pointer quic_stream) (seg:pointer qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmm = strm_get_mutable strm in
  if strmm.recvState = RecvStreamRecv then (
      if (!*seg).p.offset = strmm.nextReadOffset then (
          if verifyDataReceivedSize cs seg then
            makeStreamDataAvailable cs ps strm seg
       ) else if U64.gt (segmentEnd seg) strmm.nextReadOffset then (
          // Data has arrived out of order.  Buffer it for later.
          // Note that the partial segments may be overlapping.
          mergeSegments cs strm seg;
          let pKeepGoing = B.alloca (not (is_null strmm.partialsegments.lhead)) 1ul in
          let inv h = B.live h seg in
          let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
            !*pKeepGoing
          in
          let body() : Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
              let strmm = strm_get_mutable strm in
              let seg = strmm.partialsegments.lhead in
              let seg_offset = (!*seg).p.offset in
              let seg_end = segmentEnd seg in
              if (U64.lte seg_offset strmm.nextReadOffset) &&
                 (U64.gt seg_end strmm.nextReadOffset) then (
                // The first segment overlaps with NextReadOffset.
                let list = removeEntryList strmm.partialsegments seg in
                upd_partialsegments (!*strm).p.qsm_state list;
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
                pKeepGoing *= not (is_null strmm.partialsegments.lhead) // loop while the list is non-empty
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
let streamRecv (cs:pointer connection) (id:U64.t) (seg:pointer qstream_segment): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let isInCorrectStream = ((isStreamClientInitiated id) = (!*cs).is_client) in
  if (isStreamUni id) && isInCorrectStream then
    failwith (of_literal "Receiving data from an unexpected uni stream direction");
  // bugbug: ensure that the stream ID is in bounds
  let strm = openStreamInternal cs id in
  if strm = null then
    print_string (sprintf "Dropping received data for invalid stream ID %uL\n" id)
  else
    streamRecvInternal cs ApplicationSpace strm seg;
  pop_frame()

//bugbug: probably want to handle miTLS failures more gracefully than returning unit.
let streamRecvInitialCrypto (eng:pointer engine) (seg:pointer qstream_segment) (plaintext_cid:connectionid_t): ST (pointer connection)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let cs = createServerConnection eng plaintext_cid in
  let pss = getPacketSpaceState cs InitialSpace in
  let strm = pss.crypto_stream in
  processCryptoSegment cs seg;
  let nextReadOffset = (!*seg).p.datalength in
  let nextReadOffset64 = Cast.uint32_to_uint64 nextReadOffset in
  upd_nextReadOffset (!*strm).p.qsm_state nextReadOffset64;
  pop_frame();
  cs

(** Set the maximum allowable offset for a given stream response to MAX_STREAM_DATA *)
let setMaxStreamData (cs:pointer connection) (stream:U64.t) (maxdata:U64.t) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm = quic_OpenStream cs stream in
  let strmm = strm_get_mutable strm in
  let maxdata = if U64.lt maxdata strmm.maxStreamData then
    strmm.maxStreamData
  else
    maxdata
  in
  upd_maxStreamData (!*strm).p.qsm_state maxdata;
  pop_frame()

(** Called when a previously sent stream segment has been ACK'd by the peer.  This
    releases the data *)
let ackStream (cs:pointer connection) (t:streamRecoveryTracker): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  setEvent (!*(t.segment)).p.available;
  pop_frame()
  
(** Called when a previously sent CRYPTO segment has been ACK'd by the peer.  This
    releases the data *)
let ackCrypto (cs:pointer connection) (t:cryptoRecoveryTracker): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  setEvent (!*(t.cryptosegment)).p.available;
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
  let strmm = strm_get_mutable strm in
  let seg = t.segment in
  let list = insertHeadList strmm.segments seg in
  upd_segments (!*strm).p.qsm_state list;
  upd_dataSentSub (!*cs).csm_state (!*seg).p.datalength;
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
  let list = insertHeadList strmm.segments seg in
  upd_segments (!*strm).p.qsm_state list;
  setHasReadyToSend cs;
  pop_frame()
  
(** Reset a stream in response to RST_STREAM *)
let rstStream (cs:pointer connection) (stream:U64.t) (errorCode:U16.t) (finalOffset:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strm = quic_OpenStream cs stream in
  upd_recvstate (!*strm).p.qsm_state RecvStreamResetRecvd;
  upd_error_code (!*strm).p.qsm_state errorCode;
  print_string (sprintf "RST_STREAM StreamID=%uL errorCode=%us\n" stream errorCode);
  (* Now report the stream as ready, so QUIC_recv() will wake for it *)
  let csm = conn_get_mutable cs in
  let holder = empty_entry strm in
  let pholder = B.malloc HyperStack.root holder 1ul in
  let list = insertTailList csm.readystreams pholder in
  upd_readystreams (!*cs).csm_state list;
  setEvent (!*cs).streamDataAvailable;
  pop_frame()
