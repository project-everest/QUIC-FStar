(**

QUICFrame - parse and produce QUIC frames, which are embedded inside packets

@summary:  Parse and produce QUIC frames
*)
module QUICFrame

open FStar
open FStar.HyperStack
open FStar.HyperStack.IO
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Int.Cast
open FStar.Printf
open C
open C.Failure
open C.String
open LowStar.Buffer
open LowStar.BufferOps
open QUICTypes
open QUICMutators
open QUICStream
open QUICLossAndCongestion
open QUICUtils
open QUICFFI

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module B = LowStar.Buffer

(** Prepare one frame of stream data from a segment, having already
    confirmed that the frame and segment fit entirely in the frame. *)
let prepareStreamSegment (streamID:U64.t) (segment:pointer qstream_segment) (packet:buffer_t) (p:U32.t) (lrlist:lossRecoveryTracker_list): ST (U32.t * lossRecoveryTracker_list)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let strmtracker = {recoverystreamID=streamID; segment=segment;} in
  let tracker = StrmTracker strmtracker in
  let trackerentry = empty_entry tracker in
  let ptrackerentry = B.malloc HyperStack.root trackerentry 1ul in
  let lrlist = insertTailList lrlist ptrackerentry in
  let fin = (!*segment).p.fin in
  let f = if fin then 0x01uy else 0x00uy in
  let segment_offset = (!*segment).p.offset in
  let data_length = (!*segment).p.datalength in
  let fin_as_int = if fin then 1ul else 0ul in
  print_string (sprintf "prepareStreamFrame ID=%uL offset=%uL len=%ul fin=%ul\n" streamID segment_offset data_length fin_as_int);
  let oo = if segment_offset = 0UL then 0x00uy else 0x04uy in
  let d = 0x02uy in // data length is always present
  let s = U8.(0x10uy |^ f |^ oo |^ d) in
  // Produce a STREAM frame
  let p = append8 packet p s in
  let p = appendvar packet p streamID in
  let p = if segment_offset = 0UL then p else appendvar packet p segment_offset in
  let p = appendvar packet p (Cast.uint32_to_uint64 data_length) in
  let p = appendbytes packet p (!*segment).p.data data_length in
  pop_frame();
  (p, lrlist)

(** Prepare one frame of stream data *)
let prepareStreamFrame (cs:pointer connection) (str: pointer quic_stream) (packet:buffer_t) (packetlen:U32.t) (p:U32.t) (lrlist:lossRecoveryTracker_list): ST (U32.t * lossRecoveryTracker_list)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "Preparing STREAM frame\n";
  let ret = begin
    let segment = getNextSegment str in
    let available_bytes = U32.(packetlen-^p) in
    let streamID = (!*str).p.streamID in
    let segment_offset = (!*segment).p.offset in
    let data_length = (!*segment).p.datalength in
    let segment_offset_size = if segment_offset = 0UL then 0ul else (encodedsize segment_offset) in
    let header_size = U32.(1ul +^ (encodedsize streamID) +^ segment_offset_size +^ (encodedsize (Cast.uint32_to_uint64 data_length))) in
    if U32.(available_bytes <^ (header_size+^1ul)) then (
      // not enough space to send a single byte of stream data
      putSegmentAtHead str segment;
      (p,lrlist)
    ) else (
      let csm = conn_get_mutable cs in
      let maxAllowedData64 = U64.(csm.maxDataPeer -^ csm.dataSent) in
      let maxAllowedData =
        if U64.(maxAllowedData64 >^ 0xffffffffUL) then
          0xfffffffful // this is always longer than or equal the segment data_length
        else
          Cast.uint64_to_uint32 maxAllowedData64
        in
      let lengthToSend = minu32 data_length maxAllowedData in
      let lengthToSend =
        if U32.(available_bytes <^ (header_size+^lengthToSend)) then
          U32.(available_bytes-^header_size)
        else
          lengthToSend
        in
      let segment =
        if data_length <> lengthToSend then (
          // only part of the segment can fit in this packet.  Split the segment,
          // returning the head portion, and enqueing the tail portion back
          // into the stream for transmission later.
          splitSegmentAtOffset str segment lengthToSend
        ) else (
          // the full segment can fit in this packet
          segment
        )
      in
      upd_dataSentAdd (!*cs).csm_state (!*segment).p.datalength;
      prepareStreamSegment streamID segment packet p lrlist
     )
  end in
  pop_frame();
  ret

(** Prepare a CRYPTO frame *)
let prepareCryptoFrame (crypto_stream:pointer quic_stream) (payload:buffer_t) (payloadlength:U32.t) (p:U32.t) (lrlist:lossRecoveryTracker_list): ST (U64.t * U32.t * lossRecoveryTracker_list)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "Preparing CRYPTO frame\n";
  let segment:pointer qstream_segment = getNextSegment crypto_stream in
  let cryptotracker = { cryptosegment=segment; } in
  let tracker = CryptoTracker cryptotracker in
  let trackerentry = empty_entry tracker in
  let ptrackerentry = B.malloc HyperStack.root trackerentry 1ul in
  let lrlist = insertTailList lrlist ptrackerentry in
  let segment_offset = (!*segment).p.offset in
  let data_length = (!*segment).p.datalength in
  let p = appendvar payload p 0x18UL in // Frame is CRYPTO(0x18)
  let p = appendvar payload p (!*segment).p.offset in
  let p = appendvar payload p (Cast.uint32_to_uint64 data_length) in
  if U32.(p +^ data_length >^ payloadlength) then failwith (C.String.of_literal "Crypto frame doen't fit in the packet");
  let p = appendbytes payload p (!*segment).p.data data_length in
  pop_frame();
  (segment_offset, p, lrlist)

(** Build the ackblock list *)
let addAckBlocks (blocks: ackblock_list) (start:U64.t) (count:U64.t): ST ackblock_list
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  // Determine the gap of missing packets between the previous block
  // and this new one.
  push_frame();
  let gap = 
    if is_null blocks.lhead then
      0UL
    else (
      let lastblock = blocks.ltail in
      U64.((!*lastblock).p.start -^ (!*lastblock).p.length -^ start +^ 1UL)
    )
  in
  let block = {gap=gap; start=start; length=count; } in
  let blockentry = empty_entry block in
  let pblock = B.malloc HyperStack.root blockentry 1ul in
  let blocks = insertTailList blocks pblock in
  pop_frame();
  blocks

(** Callback function for C qsort(), to sort U64.t in reverse order *)
let reverseCompare (pa:pointer U64.t) (pb:pointer U64.t): ST Int32.t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
=
  let a = !*pa in
  let b = !*pb in
  U64.(
  if a <^ b then
    1l
  else if a >^ b then
    -1l
  else
    0l
  )

(** Group consecutive numbers together into a single block. Returns the list and count of elements in it*)
let buildAckBlocks (acks:pointer U64.t) (ackcount:U32.t): ST (ackblock_list * U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  qsort64 acks ackcount reverseCompare; // Sort the array in reverse order

  let blocks = B.alloca empty_list 1ul in
  let start = B.alloca !*acks 1ul in
  let count = B.alloca 0UL 1ul in
  let blockcount = B.alloca 0ul 1ul in
  C.Loops.for 0ul ackcount  (fun _ _ -> True) (fun c ->
      let a = acks.(c) in
      let start_minus_count = U64.(!*start -^ !*count) in
      if U64.gt a start_minus_count then (
        () // The list is sorted.  a > start-count means a is a duplicated value.  Drop it.
      ) else if a = start_minus_count then ( // if the new Ack matches the expected (start-count, since we are descending)
        count *= U64.(!*count +^ 1UL)
      ) else (
        let list = addAckBlocks !*blocks !*start !*count in
        blocks *= list;
        start *=a;
        count *= 1UL;
        blockcount *= U32.(!*blockcount +^ 1ul)
      )
  );
  // Add the final block
  let blocks = addAckBlocks !*blocks !*start !*count in
  let blockcount = U32.(!*blockcount +^ 1ul) in
  pop_frame();
  (blocks, blockcount)

  //*)

(** Get ready to encode one frame of ACKs *)
let prepareAckFrame (cs:pointer connection) (ps:packet_space) (frame:buffer_t) (p:U32.t) (payloadlength:U32.t) (lrlist:lossRecoveryTracker_list): ST (U32.t * lossRecoveryTracker_list)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  upd_sendAckOnlyIfNeeded cs ps false;
  let ret = 
    let pss = getPacketSpaceState cs ps in
    if pss.outgoingAckCount = 0ul then (
      print_string "Preparing ACK frame:  No outgoing ACKs\n";
      (p, lrlist)
    ) else (
      print_string (sprintf "Preparing ACK frame:  Sending %ul acks\n" pss.outgoingAckCount);
      let blocks,count = buildAckBlocks pss.outgoingAcks pss.outgoingAckCount in
      upd_outgoingAckCount cs ps 0ul;
      let largestAcknowledged = (!*(blocks.lhead)).p.start in
      let ackdelay = 10000UL in // bugbug: keep track of this value
      let p = append8 frame p 0x1auy in // ACK frame type
      let p = appendvar frame p largestAcknowledged in
      let p = appendvar frame p ackdelay in
      let p = appendvar frame p (Cast.uint32_to_uint64 U32.(count-^1ul)) in
      let firstblock = blocks.lhead in
      let p = appendvar frame p U64.((!*firstblock).p.length -^ 1UL) in // First ACK Block
      let flink = (!*firstblock).flink in
      let pblock:(pointer (pointer ackblock)) = B.alloca flink 1ul in
      let pp = B.alloca p 1ul in
      let pstop = B.alloca (is_null flink) 1ul in
      let inv h = B.live h pp in
      let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
        not !*pstop
      in
      let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
        let block = !*pblock in
        let gap = (!*block).p.gap in
        let ackBlock = (!*block).p.length in
        let p = appendvar frame !*pp gap in
        let p = appendvar frame p ackBlock in
        pp *= p;
        pblock *= (!*(!*pblock)).flink;
        pstop *= (is_null !*pblock)
      in
      C.Loops.while test body;
      let acktracker = AckTracker blocks in
      let ptrackerentry = B.malloc HyperStack.root (empty_entry acktracker) 1ul in
      let lrlist = insertTailList lrlist ptrackerentry in
      (!*pp,lrlist)
    ) in
  pop_frame();
  ret

let getGapBlockOffset (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err (U64.t * U64.t * U32.t))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  gap_offset <-- (getvar_s packet length offset);
  let gap,offset = gap_offset in
  block_offset <-- (getvar_s packet length offset);
  let block,offset = block_offset in
  return (gap, block, offset)

(** Process an ACK frame *)
let processAckFrame (cs:pointer connection) (packet:buffer_t) (offset:U32.t) (length:U32.t) (hasECN:bool): ST (err U32.t)
   (requires (fun _ -> (U32.v offset > 1)))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
  print_string "processAckFrame\n";
  let offset = U32.(offset+^1ul) in // skip the frame type byte
  largestAck_offset <-- (getvar_s packet length offset);
  let largestAck,offset = largestAck_offset in
  ackDelay_offset <-- (getvar_s packet length offset);
  let ackDelay,offset = ackDelay_offset in
  blockCount_offset <-- (getvar_s packet length offset);
  let blockCount,offset = blockCount_offset in
  firstAckBlock_offset <-- (getvar_s packet length offset);
  let firstAckBlock,offset = firstAckBlock_offset in
  let ackPacket (pn:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true)) =
      onPacketAcked cs pn
  in
  let start = U64.(largestAck-^firstAckBlock) in
  let stop = U64.(largestAck+^1UL) in // stopping condition is i<stop, so add 1
  C.Loops.for64 start stop (fun h1 i -> true) ackPacket;
  let pret = B.alloca (Ok 0ul) 1ul in
  let pstart = B.alloca start 1ul in
  let poffset = B.alloca offset 1ul in
  let ackBlock (bn:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true)) =
    let gap_block_offset = getGapBlockOffset packet length offset in
    (match gap_block_offset with
    | Fail m -> pret *= fail m
    | Ok g_b_o -> (
        let gap,block,offset = g_b_o in
        poffset *= offset;
        let largestack = U64.(!*pstart -^ gap) in
        let start = U64.(largestack -^block) in
        pstart *= start;
        let stop = U64.(largestAck+^1UL) in // stopping condition is i<stop, so add 1
        C.Loops.for64 start stop (fun h1 i -> true) ackPacket
        )
      )
  in
  C.Loops.for64 0UL blockCount (fun h1 i -> true) ackBlock;
  match !*pret with
  | Fail _ -> !*pret
  | Ok _ -> return !*poffset
  end in
  pop_frame();
  ret

(** Process a stream frame *)
let processStreamFrameInternal (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err (U32.t * U64.t * pointer qstream_segment))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    st <-- (getu8_s packet length offset);
    let offset = U32.(offset +^ 1ul) in
    let fin = U8.(st &^ 1uy) in
    let len = U8.((st >>^ 1ul) &^ 1uy) in
    let off = U8.((st >>^ 2ul) &^ 1uy) in
    streamID_offset <-- (getvar_s packet length offset);
    let streamID, offset = streamID_offset in
    streamOffset_offset <-- (
      if off=0uy then return (0UL, offset)
      else getvar_s packet length offset
      );
    let streamOffset, offset = streamOffset_offset in
    dataLength64_offset <-- (
      if len=0uy then (
        let dataLength = Cast.uint32_to_uint64 U32.(length-^offset) in
        return (dataLength, length)
      ) else (
        getvar_s packet length offset
      )
    );
    let dataLength64,offset = dataLength64_offset in
    let dataLength32 = Cast.uint64_to_uint32 dataLength64 in
    datalengthcheck <-- (
      if U64.(dataLength64 >^ 0x10000UL) then
        fail !$"Stream data length too long"
      else if U32.(offset+^dataLength32 >^ length) then
        fail !$"Stream data length too long"
      else
        return offset
    );  
    print_string (sprintf "processStreamFrameInternal ID=%uL offset=%uL length=%ul fin=%uy\n" streamID streamOffset dataLength32 fin);
    let segdata = B.malloc HyperStack.root 0uy dataLength32 in
    B.blit packet offset segdata 0ul dataLength32;
    let segfixed:qstream_segment_fixed = {
      offset=streamOffset;
      data = segdata;
      datalength = dataLength32;
      isApplicationOwned = false;
      fin = if fin = 0uy then false else true;
      available = nullptr;
    } in
    let seg = empty_entry segfixed in
    let pseg = B.malloc HyperStack.root seg 1ul in
    let endingoffset = U32.(offset +^ dataLength32) in
    return (endingoffset, streamID, pseg)
  end in
  pop_frame();
  ret

(** Process a stream frame *)
let processStreamFrame (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
    f <-- (processStreamFrameInternal packet length offset);
    let offset,streamID,pseg = f in
    streamRecv cs streamID pseg;
    return offset
  end in
  pop_frame();
  offset

(** Process a CRYPTO frame into a stream segment *)
let processCryptoFrameInternal (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err (U32.t * pointer qstream_segment))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    let offset = U32.(offset +^ 1ul) in // skip the frame type byte
    streamOffset_offset <-- (getvar_s packet length offset);
    let streamOffset,offset = streamOffset_offset in
    dataLength_offset <-- (getvar_s packet length offset);
    let dataLength64,offset = dataLength_offset in
    let dataLength32 = Cast.uint64_to_uint32 dataLength64 in
    datalengthcheck <-- (
      if U64.(dataLength64 >^ 0x10000UL) then
        fail !$"Stream data length too long"
      else if U32.(offset+^dataLength32 >^ length) then
        fail !$"Stream data length too long"
      else
        return offset
    );  
    print_string (sprintf "processCryptoFrameInternal offset=%uL length=%ul\n" streamOffset dataLength32);
    let segdata = B.malloc HyperStack.root 0uy dataLength32 in
    B.blit packet offset segdata 0ul dataLength32;
    let segfixed:qstream_segment_fixed = {
      offset=streamOffset;
      data = segdata;
      datalength = dataLength32;
      isApplicationOwned = false;
      fin = false;
      available = nullptr;
    } in
    let seg = empty_entry segfixed in
    let pseg = B.malloc HyperStack.root seg 1ul in
    let endingoffset = U32.(offset +^ dataLength32) in
    return (endingoffset, pseg)
  end in
  pop_frame();
  ret
  
(** Process a CRYPTO frame *)
let processCryptoFrame (cs:pointer connection) (ps:packet_space) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
    f <-- (processCryptoFrameInternal packet length offset);
    let offset,pseg = f in
    let pss = getPacketSpaceState cs ps in
    streamRecvInternal cs ps pss.crypto_stream pseg;
    return offset
  end in
  pop_frame();
  offset
 
(** Process the stream frame in a Initial packet *)
let processInitialCryptoFrame (eng:pointer engine) (packet:buffer_t) (length:U32.t) (plaintext_cid:connectionid_t) (packetNumber:U64.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
    f <-- (processCryptoFrameInternal packet length 0ul);
    let offset,pseg = f in
    // this allocates a new connection and returns it, with the
    // monitor locked.  Release it before returning, as we are
    // done with it.
    let cs = streamRecvInitialCrypto eng pseg plaintext_cid in
    registerAck cs InitialSpace packetNumber;
    monitorExit (!*cs).monitor;
    return offset
  end in
  pop_frame();
  offset

(** Parse MaxStreamData *)
let processMaxStreamData (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
    streamID_offset <-- (getvar_s packet length offset);
    let streamID,offset = streamID_offset in
    maxStreamData_offset <-- (getvar_s packet length offset);
    let maxStreamData,offset = maxStreamData_offset in
    setMaxStreamData cs streamID maxStreamData;
    return offset
  end in
  pop_frame();
  offset

(** Parse MaxStreamID *)
let processMaxStreamID (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
    maxID_offset <-- (getvar_s packet length offset);
    let maxID,offset = maxID_offset in
    let csm = conn_get_mutable cs in
    if U64.((maxID &^ 1UL) = 0UL) then ( // MAX BIDI stream ID
      if U64.lt csm.maxStreamID_BIDIPeer maxID then (
        upd_maxStreamID_BIDIPeer (!*cs).csm_state maxID
      )
    ) else ( // MAX UNI stream ID
      if U64.lt csm.maxStreamID_UNIPeer maxID then (
        upd_maxStreamID_UNIPeer (!*cs).csm_state maxID
      )
    );
    return offset
  end in
  pop_frame();
  offset

(** Parse MaxData *)
let processMaxData (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
    maxData_offset <-- (getvar_s packet length offset);
    let maxData,offset = maxData_offset in
    let csm = conn_get_mutable cs in
    if U64.lt csm.maxDataPeer maxData then (
      upd_maxDataPeer (!*cs).csm_state maxData;
      setHasReadyToSend cs (* Now that data can be sent, try sending data *)
    );
    return offset
  end in
  pop_frame();
  offset

(** Parse RST_STREAM *)
let processRstStream (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
    streamID_offset <-- (getvar_s packet length offset);
    let streamID,offset = streamID_offset in
    errorCode <-- (getu16_s packet length offset);
    finalOffset_offset <-- (getvar_s packet length U32.(offset+^2ul));
    let finalOffset,offset = finalOffset_offset in
    rstStream cs streamID errorCode finalOffset;
    return offset
  end in
  pop_frame();
  offset

(** Parse CONNECTION_CLOSE *)
let processConnectionClose (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
  errorCode <-- (getu16_s packet length offset);
  rpLen_offset <-- (getvar_s packet length U32.(offset+^2ul));
  let rpLen,offset = rpLen_offset in
  if rpLen=0UL then (
    print_string (sprintf "CONNECTION_CLOSE ErrorCode=%us\n" errorCode);
    upd_cstate (!*cs).csm_state Closed;
    return  offset
  ) else if U64.(rpLen >^ 0x65535UL) then (
    fail !$"CONNECTION_CLOSE with invalid Reason Phrase Length"
  ) else (
    let rpLen32 = Cast.uint64_to_uint32 rpLen in
    let finaloffset = U32.(offset +^ rpLen32) in
    if U32.(finaloffset >^ length) then (
        fail !$"CONNECTION_CLOSE with invalid Reason Phrase Length"
    ) else (
      // bugbug: how to print a UTF8-encoded string sitting at packet[offset] length rpLen32
      print_string (sprintf "CONNECTION_CLOSE ErrorCode=%us: Reason=is included" errorCode);
      upd_cstate (!*cs).csm_state Closed;
      return finaloffset
    )
  )
  end in
  cancelTimer (!*(!*cs).landc_state).ping_alarm;
  pop_frame();
  offset

(** Parse APPLICATION_CLOSE *)
let processApplicationClose (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let offset = begin
  errorCode <-- (getu16_s packet length offset);
  rpLen_offset <-- (getvar_s packet length U32.(offset+^2ul));
  let rpLen,offset = rpLen_offset in
  if rpLen=0UL then (
    print_string (sprintf "APPLICATION_CLOSE ErrorCode=%us\n" errorCode);
    upd_cstate (!*cs).csm_state Closed;
    return offset
  ) else if U64.(rpLen >^ 0x65535UL) then (
    fail !$"APPLICATION_CLOSE with invalid Reason Phrase Length"
  ) else (
    let rpLen32 = Cast.uint64_to_uint32 rpLen in
    let finaloffset = U32.(offset +^ rpLen32) in
    if U32.(finaloffset >^ length) then (
        fail !$"APPLICATION_CLOSE with invalid Reason Phrase Length"
    ) else (
      // bugbug: how to print a UTF8-encoded string sitting at packet[offset] length rpLen32
      print_string (sprintf "APPLICATION_CLOSE ErrorCode=%us: Reason=is included" errorCode);
      upd_cstate (!*cs).csm_state Closed;
      return finaloffset
    )
  )
  end in
  cancelTimer (!*(!*cs).landc_state).ping_alarm;
  pop_frame();
  offset

(** Parse BLOCKED *)
let processBlocked (cs:pointer connection) (packet:buffer_t) (length:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  blockedOffset_offset <-- (getvar_s packet length offset);
  let blockedOffset, offset = blockedOffset_offset in
  print_string (sprintf "BLOCKED at offset %uL" blockedOffset);
  pop_frame();
  return offset

(* Public API: Reset a stream *)
let quic_ResetStream (cs:pointer connection) (strm:pointer quic_stream) (err:U16.t) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let strmm = strm_get_mutable strm in
  upd_sendstate (!*strm).p.qsm_state SendStreamResetSent;
  let data = B.malloc HyperStack.root 0uy 19ul in
  let offset = append8 data 0ul 0x01uy in // RST_STREAM
  let offset = appendvar data offset (!*strm).p.streamID in
  let offset = append16 data offset err in // Error Code
  let offset = appendvar data offset strmm.nextWriteOffset in // Final Offset
  let hWait = enqueueFixedFrame cs data offset in
  monitorExit (!*cs).monitor;
  waitForSingleObject hWait 0xfffffffful;
  closeHandle hWait;
  pop_frame()

(** Parse a protected frame of data *)
let processProtectedFrame (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    (* The frame type is actually encoded as a variable length integer.  But it is required to be
        stored in the shortest form possible, which makes it easy to check just the first byte
        to parse the predefined frame types *)
    ft <-- (getu8_s packet packetlen offset); // Frame Type
    match ft with
    | 0x00uy -> return U32.(offset+^1ul) // PADDING
    | 0x01uy -> processRstStream cs packet packetlen U32.(offset+^1ul)
    | 0x02uy -> processConnectionClose cs packet packetlen U32.(offset+^1ul)
    | 0x03uy -> processApplicationClose cs packet packetlen U32.(offset+^1ul)
    | 0x04uy -> processMaxData cs packet packetlen  U32.(offset+^1ul)
    | 0x05uy -> processMaxStreamData cs packet packetlen U32.(offset+^1ul)
    | 0x06uy -> processMaxStreamID cs packet packetlen U32.(offset+^1ul)
    | 0x07uy -> return U32.(offset+^1ul) (* PING.  Nothing to do, except ACK the packet *)
    | 0x08uy -> processBlocked cs packet packetlen U32.(offset+^1ul)
    | 0x09uy -> failwith (of_literal "STREAM_BLOCKED is NYI\n")
    | 0x0auy -> failwith (of_literal "STREAM_ID_BLOCKED is NYI\n")
    | 0x0buy -> failwith (of_literal "NEW_CONNECTION_ID is NYI\n")
    | 0x0cuy -> failwith (of_literal "STOP_SENDING is NYI\n")
    | 0x0duy -> failwith (of_literal "RETIRE_CONNECTION_ID is NYI\n")
    | 0x0euy -> failwith (of_literal "PATH_CHALLENGE is NYI\n")
    | 0x0fuy -> failwith (of_literal "PATH_RESPONSE is NYI\n")
    | 0x10uy -> processStreamFrame cs packet packetlen offset
    | 0x11uy -> processStreamFrame cs packet packetlen offset
    | 0x12uy -> processStreamFrame cs packet packetlen offset
    | 0x13uy -> processStreamFrame cs packet packetlen offset
    | 0x14uy -> processStreamFrame cs packet packetlen offset
    | 0x15uy -> processStreamFrame cs packet packetlen offset
    | 0x16uy -> processStreamFrame cs packet packetlen offset
    | 0x17uy -> processStreamFrame cs packet packetlen offset
    | 0x18uy -> processCryptoFrame cs ApplicationSpace packet packetlen offset
    | 0x19uy -> failwith (of_literal "NEW_TOKEN is NYI\n")
    | 0x1auy -> processAckFrame cs packet offset packetlen false
    | 0x1buy -> processAckFrame cs packet offset packetlen true
    | _ -> if U8.(ft >=^ 0x10uy) && U8.(ft <=^ 0x17uy) then (
            processStreamFrame cs packet packetlen offset
          ) else (
            print_string (sprintf "unsupported protected frame type %uy\n" ft);
            fail !$"Unknown frame type"
          )
  end in
  pop_frame();
  ret

(** Parse all of the frames within a protected packet *)
let processProtectedFrames (cs:pointer connection) (packet:buffer_t) (offset:U32.t) (length:U32.t): ST (err U32.t)
   (requires (fun _ -> ((U32.v offset) < (U32.v length))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();

  let pstop = B.alloca U32.(offset >=^ length) 1ul in
  let pret = B.alloca (Ok 0ul) 1ul in
  let poffset = B.alloca offset 1ul in
  let inv h = B.live h pret in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not !*pstop
  in
  let body(): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    let ret = processProtectedFrame cs packet length !*poffset in
    pret *= ret;
    (match ret with
    | Fail f -> pstop *= true // stop looping
    | Ok offset ->
      poffset *= offset;
      pstop *= U32.(offset >=^ length)
    )
  in
  C.Loops.while test body;
  let ret = !*pret in
  pop_frame();
  ret

(** Parse one frame from an Initial packet *)
let processInitialFrame (cs:pointer connection) (packet:buffer_t) (offset:U32.t) (length:U32.t): ST (err U32.t)
   (requires (fun _ -> ((U32.v offset) < (U32.v length))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    ft <-- (getu8_s packet length offset); // Frame Type
    if ft = 0uy then // PADDING
      return U32.(offset+^1ul)
    else if ft = 0x02uy then
      processConnectionClose cs packet length U32.(offset+^1ul)
    else if ft = 0x03uy then
      processApplicationClose cs packet length U32.(offset+^1ul)
    else if ft = 0x1auy then
      processAckFrame cs packet offset length false
    else if ft = 0x19uy then
      processAckFrame cs packet offset length true
    else if ft = 0x18uy then
      processCryptoFrame cs InitialSpace packet length offset
    else (
      // bugbug: treat as connection error
      print_string (sprintf "unsupported cleartext frame type %uy\n" ft);
      fail !$"Invalid frame type"
      )
  end in
  pop_frame();
  ret

(** Parse one frame from a Handshake packet *)
let processHandshakeFrame (cs:pointer connection) (packet:buffer_t) (offset:U32.t) (length:U32.t): ST (err U32.t)
   (requires (fun _ -> ((U32.v offset) < (U32.v length))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    ft <-- (getu8_s packet length offset); // Frame Type
    if ft = 0uy then // PADDING
      return U32.(offset+^1ul)
    else if ft = 0x02uy then
      processConnectionClose cs packet length U32.(offset+^1ul)
    else if ft = 0x03uy then
      processApplicationClose cs packet length U32.(offset+^1ul)
    else if ft = 0x1auy then
      processAckFrame cs packet offset length false
    else if ft = 0x19uy then
      processAckFrame cs packet offset length true
    else if ft = 0x18uy then
      processCryptoFrame cs HandshakeSpace packet length offset
    else (
      // bugbug: treat as connection error
      print_string (sprintf "unsupported cleartext frame type %uy\n" ft);
      fail !$"Invalid frame type"
      )
  end in
  pop_frame();
  ret

(** Parse all of the frames within an Initial packet *)
let processInitialFrames (cs:pointer connection) (packet:buffer_t) (offset:U32.t) (length:U32.t): ST (err U32.t)
   (requires (fun _ -> ((U32.v offset) < (U32.v length))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();

  let pstop = B.alloca U32.(offset >=^ length) 1ul in
  let pret = B.alloca (Ok 0ul) 1ul in
  let poffset = B.alloca offset 1ul in
  let inv h = B.live h pret in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not !*pstop
  in
  let body(): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    let ret = processInitialFrame cs packet !*poffset length in
    pret *= ret;
    (match ret with
    | Fail f -> pstop *= true // stop looping
    | Ok offset ->
      poffset *= offset;
      pstop *= U32.(offset >=^ length)
    )
  in
  C.Loops.while test body;
  let ret = !*pret in
  pop_frame();
  ret

(** Parse all of the frames within a Handshake packet *)
let processHandshakeFrames (cs:pointer connection) (packet:buffer_t) (offset:U32.t) (length:U32.t): ST (err U32.t)
   (requires (fun _ -> ((U32.v offset) < (U32.v length))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();

  let pstop = B.alloca U32.(offset >=^ length) 1ul in
  let pret = B.alloca (Ok 0ul) 1ul in
  let poffset = B.alloca offset 1ul in
  let inv h = B.live h pret in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not !*pstop
  in
  let body(): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    let ret = processHandshakeFrame cs packet !*poffset length in
    pret *= ret;
    (match ret with
    | Fail f -> pstop *= true // stop looping
    | Ok offset ->
      poffset *= offset;
      pstop *= U32.(offset >=^ length)
    )
  in
  C.Loops.while test body;
  let ret = !*pret in
  pop_frame();
  ret

(** Parse one frame from a ClientHello packet *)
let processClientInitialFrame (eng:pointer engine) (packet:buffer_t) (offset:U32.t) (length:U32.t) (plaintext_cid:connectionid_t) (packetNumber:U64.t): ST (err U32.t)
   (requires (fun _ -> ((U32.v offset) < (U32.v length))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    ft <-- (getu8_s packet length offset); // Frame Type
    if offset=0ul then (
      if ft = 0x18uy then // CRYPTO frame
        processInitialCryptoFrame eng packet length plaintext_cid packetNumber
      else
        fail !$"First byte must be a stream frame"
    )
    else if ft = 0uy then // PADDING frame
      return U32.(offset+^1ul)
    else (
      // bugbug: return PROTOCOL_VIOLATION for unsupported frames
      print_string (sprintf "unsupported frame type %uy\n" ft);
      fail !$"Invalid frame type"
      )
  end in
  pop_frame();
  ret

(** Parse all frames within a ClientHello send to a server *)
let processClientInitialFrames (eng:pointer engine) (packet:buffer_t) (length:U32.t) (plaintext_cid:connectionid_t) (packetNumber:U64.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let pstop = B.alloca false 1ul in
  let pret = B.alloca (Ok 0ul) 1ul in
  let poffset = B.alloca 0ul 1ul in
  let inv h = B.live h pret in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not !*pstop
  in
  let body(): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    let ret = processClientInitialFrame eng packet !*poffset length plaintext_cid packetNumber in
    pret *= ret;
    (match ret with
    | Fail f -> pstop *= true // stop looping
    | Ok offset ->
      poffset *= offset;
      pstop *= U32.(offset >=^ length)
    )
  in
  C.Loops.while test body;
  let ret = !*pret in
  pop_frame();
  ret

(** Prepare a PING frame *)
let preparePingFrame (packet:buffer_t) (packetlen:U32.t) (p:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "Preparing PING\n";
  let p = append8 packet p 0x07uy in
  pop_frame();
  p

(** Prepare a fixed frame *)
let prepareFixedFrame  (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t) (p:U32.t) (lrlist:lossRecoveryTracker_list) (pff:pointer fixedframe): ST (U32.t * lossRecoveryTracker_list)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let framedata = (!*pff).p.framedata in
  let frametype = !*framedata in
  (match frametype with
  | 0x00uy -> print_string "Preparing PADDING\n"
  | 0x01uy -> print_string "Preparing RST_STREAM\n"
  | 0x02uy -> print_string "Preparing CONNECTION_CLOSE\n"
  | 0x03uy -> print_string "Preparing APPLICATION_CLOSE\n"
  | 0x04uy -> print_string "Preparing MAX_DATA\n"
  | 0x05uy -> print_string "Preparing MAX_STREAM_DATA\n"
  | 0x06uy -> print_string "Preparing MAX_STREAM_ID\n"
  | 0x07uy -> failwith (of_literal "PING isn't supported as a fixed frame")
  | 0x08uy -> print_string "Preparing BLOCKED\n"
  | 0x09uy -> print_string "Preparing STREAM_BLOCKED\n"
  | 0x0auy -> print_string "Preparing STREAM_ID_BLOCKED\n"
  | 0x0buy -> print_string "Preparing NEW_CONNECTION_ID\n"
  | 0x0cuy -> print_string "Preparing STOP_SENDING\n"
  | 0x0duy -> print_string "Preparing RETIRE_CONNECTION_ID\n"
  | 0x0euy -> print_string "Preparing PATH_CHALLENGE\n"
  | 0x0fuy -> print_string "Preparing PATH_RESPONSE\n"
  | 0x19uy -> print_string "Preparing NEW_TOKEN\n"
  | _ -> failwith (of_literal "Unknown fixed-frame kind")
  );
  let length = (!*pff).p.framelength in
  let p = appendbytes packet p framedata length in
  let tracker = FixedFrameTracker pff in
  let trackerentry = empty_entry tracker in
  let ptrackerentry = B.malloc HyperStack.root trackerentry 1ul in
  let lrlist = insertTailList lrlist ptrackerentry in
  if frametype = 0x02uy || frametype = 0x03uy then (
    upd_cstate (!*cs).csm_state Closed
  );
  B.free framedata;
  pop_frame();
  p,lrlist
