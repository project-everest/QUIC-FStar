# module QUICStream
streams within a QUIC connection



QUIC Stream - the high-level stream interface for applications



```fsharp
let ((findStream (csm:connection_mutable) (stream:U32.t)):(Stack (pointer_or_null quic_stream) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):findStreamRec csm.streams.lhead stream
```


 Find a stream within the connection, by its ID 

```fsharp
let ((quic_OpenStream (cs:pointer connection) (stream:U32.t)):(Stack (pointer quic_stream) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); monitorEnter (!*(cs)).monitor; let  csm = conn_get_mutable cs in let  strm = findStream csm stream in let  strm = if is_null strm then (if U32.gt stream csm.maxStreamID then C.String.print (C.String.of_literal "BUGBUG: send STREAM_ID_NEEDED
") else (); let  (strmm:quic_stream_mutable) = {state=StreamIdle appstate=AppOpen nextWriteOffset=0 maxStreamData=csm.defaultMaxStreamData nextReadOffset=0 segments=empty_list readysegments=empty_list partialsegments=empty_list} in let  strmr = FStar.Buffer.rcreate FStar.HyperHeap.root strmm 1 in let  (strmf:quic_stream_fixed) = {streamID=stream hasDataReady=createEvent 0 0 qsm_state=strmr} in let  strm = empty_entry strmf in let  pstrm = FStar.Buffer.rcreate FStar.HyperHeap.root strm 1 in let  list = insertTailList csm.streams pstrm in upd_streams (!*(cs)).csm_state list; pstrm) else strm in monitorExit (!*(cs)).monitor; pop_frame (); strm
```


 Public API: Open a QUIC stream.  Returns NULL on failure. 

```fsharp
let ((quic_CloseStream (cs:pointer connection) (strm:pointer quic_stream)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); monitorEnter (!*(cs)).monitor; let  strmm = strm_get_mutable strm in if =(strmm.appstate, AppOpen) then C.String.print (C.String.of_literal "bugbug: send RST_STREAM with NO_ERROR to indicate that the stream is now closed
") else (); upd_appstate (!*(strm)).p.qsm_state AppClosed; monitorExit (!*(cs)).monitor; pop_frame ()
```


 Public API: Close a stream 

```fsharp
let ((quic_RecvStream (cs:pointer connection) (strm:pointer quic_stream) (buffer:buffer_t) (bufferlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); waitForSingleObject (!*(strm)).p.hasDataReady 0xffffffff; monitorEnter (!*(cs)).monitor; let  strmm = strm_get_mutable strm in let  seg = strmm.readysegments.lhead in let  list = removeEntryList strmm.readysegments seg in upd_readysegments (!*(strm)).p.qsm_state list; if is_null strmm.readysegments.lhead then resetEvent (!*(strm)).p.hasDataReady else (); if (!*(seg)).p.fin then upd_appstate (!*(strm)).p.qsm_state AppFin else (); monitorExit (!*(cs)).monitor; let  blitlen = (!*(seg)).p.datalength in let  blitlen = if (U32.lt bufferlen blitlen) then blitlen else bufferlen in let  data = (!*(seg)).p.data in FStar.Buffer.blit data 0 buffer 0 blitlen; pop_frame (); blitlen
```


 Public API: Receive data on a stream.  This will block until data arrives.  It returns the number of bytes written into the buffer. 

```fsharp
let ((quic_StreamIsFin (cs:pointer connection) (strm:pointer quic_stream)):(Stack bool ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strmm = strm_get_mutable strm in let  result = =(strmm.appstate, AppFin) in pop_frame (); result
```


 Public API:  Query if the 'fin' marker has been received, for end of the stream 

```fsharp
let ((getNextSegment (strm:pointer quic_stream)):(Stack (pointer qstream_segment) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strmm = strm_get_mutable strm in let  seg = strmm.segments.lhead in let  list = removeEntryList strmm.segments seg in upd_segments (!*(strm)).p.qsm_state list; pop_frame (); seg
```


 Retrieve the next stream segment from .segments, ready to send 

```fsharp
let ((hasMoreToSend (strm:pointer quic_stream)):(Stack bool ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strmm = strm_get_mutable strm in let  hasmore = if (is_null strmm.segments.lhead) then false else true in pop_frame (); hasmore
```


 Determine if a stream has segments ready to send 

```fsharp
let ((splitSegment (seg:pointer qstream_segment) (firstlength:U32.t)):(Stack (*((pointer qstream_segment), (pointer qstream_segment))) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  data = (!*(seg)).p.data in let  firstdata = FStar.Buffer.rcreate FStar.HyperHeap.root 0 firstlength in Buffer.blit data 0 firstdata 0 firstlength; let  seconddatalength = _ in let  seconddata = FStar.Buffer.rcreate FStar.HyperHeap.root 0 seconddatalength in Buffer.blit data firstlength seconddata 0 seconddatalength; let  (first:qstream_segment_fixed) = {offset=(!*(seg)).p.offset data=firstdata datalength=firstlength fin=false available=createEvent 0 0} in let  first = empty_entry first in let  firstlength64 = Cast.uint32_to_uint64 firstlength in let  secondoffset = _ in let  (second:qstream_segment_fixed) = {offset=secondoffset data=seconddata datalength=seconddatalength fin=(!*(seg)).p.fin available=createEvent 0 0} in let  second = empty_entry second in let  pfirst = FStar.Buffer.rcreate FStar.HyperHeap.root first 1 in let  psecond = FStar.Buffer.rcreate FStar.HyperHeap.root second 1 in pop_frame (); ((FStar.Pervasives.Native.Mktuple2 pfirst psecond))
```


 Merge a newly-arrive segment into the current segment list.  This must handle overlapping
    and duplicated segments arriving out of order. 

```fsharp
let ((segmentEnd (seg:pointer qstream_segment)):(Stack U64.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  offset = (!*(seg)).p.offset in let  length = (!*(seg)).p.datalength in let  segend = _ in pop_frame (); segend
```


 Compute the end of a segment (offset+datalength) 

```fsharp
let ((mergeSegmentsBody (partialsegments:qstream_segment_list) (c:pointer qstream_segment) (seg:pointer qstream_segment)):(Stack (*(qstream_segment_list, bool)) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  c_offset = (!*(c)).p.offset in let  seg_offset = (!*(seg)).p.offset in let  c_segmentend = segmentEnd c in let  seg_segmentend = segmentEnd seg in let  ret = if &&((U64.lt c_segmentend c_offset), (=(c, partialsegments.lhead))) then (let  partialsegments = insertEntryBefore partialsegments c seg in ((FStar.Pervasives.Native.Mktuple2 partialsegments false))) else if U64.gte seg_offset c_segmentend then (if =(c, partialsegments.ltail) then (let  partialsegments = insertTailList partialsegments seg in ((FStar.Pervasives.Native.Mktuple2 partialsegments false))) else (((FStar.Pervasives.Native.Mktuple2 partialsegments true)))) else if &&((U64.gte seg_offset c_offset), (U64.lte seg_segmentend c_segmentend)) then (((FStar.Pervasives.Native.Mktuple2 partialsegments false))) else if &&((U64.lt seg_offset c_offset), (=(seg_segmentend, c_offset))) then (let  partialsegments = insertEntryBefore partialsegments c seg in ((FStar.Pervasives.Native.Mktuple2 partialsegments false))) else if &&((U64.lt seg_offset c_offset), (U64.gte seg_segmentend c_offset)) then (let  l = _ in let  l32 = Cast.uint64_to_uint32 l in let  (f, _) = splitSegment seg l32 in let  partialsegments = insertEntryBefore partialsegments c f in ((FStar.Pervasives.Native.Mktuple2 partialsegments false))) else (((FStar.Pervasives.Native.Mktuple2 partialsegments true))) in pop_frame (); ret
```


 Body of the do/while loop.  Returns the new list, and true to keep iterating, or false to stop 

```fsharp
let ((mergeSegments (strm:pointer quic_stream) (seg:pointer qstream_segment)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strmm = strm_get_mutable strm in let  list = strmm.partialsegments in let  list = if is_null list.lhead then (insertHeadList list seg) else (let  lv = list.ltail in if U64.gte (!*(seg)).p.offset (segmentEnd lv) then (insertTailList list seg) else if U64.gte (!*(seg)).p.offset (!*(lv)).p.offset then (let  l64 = _ in let  l = Cast.uint64_to_uint32 l64 in if U32.lt l (!*(seg)).p.datalength then (let  (_, s) = splitSegment seg l in insertTailList list s) else (list)) else (let  (c:(pointer (pointer qstream_segment))) = Buffer.create list.lhead 1 in let  listmutable = Buffer.create list 1 in C.Loops.do_while ((fun h break -> /\(live h c, (==>(break, False))))) ((fun _ -> let  (list, keepgoing) = mergeSegmentsBody list (!*(c)) seg in if not keepgoing then (.()<-(listmutable, 0, list)) else (); .()<-(c, 0, (!*((!*(c)))).flink); not keepgoing)); .()(listmutable, 0))) in upd_partialsegments (!*(strm)).p.qsm_state list; pop_frame ()
```


 Search inside the partialsegments list...
  if seg is entirely in a gap, insert it
  if seg overlaps with another...
    if it is exactly overlapping, drop it
    if it overlaps from the front, insert before, after truncting seg
    if it overlaps from the rear, insert after, after pruning off the start 

```fsharp
let ((makeStreamDataAvailable (strm:pointer quic_stream) (seg:pointer qstream_segment)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strmm = strm_get_mutable strm in let  datalength = (!*(seg)).p.datalength in let  datalength64 = Cast.uint32_to_uint64 datalength in upd_nextReadOffset (!*(strm)).p.qsm_state _; let  list = insertTailList strmm.readysegments seg in upd_readysegments (!*(strm)).p.qsm_state list; setEvent (!*(strm)).p.hasDataReady; pop_frame ()
```


 Indicate new data is ready for the application to receive on a stream 

```fsharp
let ((streamRecv (cs:pointer connection) (id:U32.t) (seg:pointer qstream_segment)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strm = quic_OpenStream cs id in let  strmm = strm_get_mutable strm in if =((!*(seg)).p.offset, strmm.nextReadOffset) then (makeStreamDataAvailable strm seg) else if U64.gt (segmentEnd seg) strmm.nextReadOffset then (mergeSegments strm seg; C.Loops.do_while ((fun h _ -> true)) ((fun _ -> let  strmm = strm_get_mutable strm in let  seg = strmm.partialsegments.lhead in let  seg_offset = (!*(seg)).p.offset in let  seg_end = segmentEnd seg in if &&((U64.lte seg_offset strmm.nextReadOffset), (U64.gt seg_end strmm.nextReadOffset)) then (let  list = removeEntryList strmm.partialsegments seg in upd_partialsegments (!*(strm)).p.qsm_state list; let  seg = if U64.lt seg_offset strmm.nextReadOffset then (let  l = _ in let  (_, s) = splitSegment seg (Cast.uint64_to_uint32 l) in s) else seg in makeStreamDataAvailable strm seg; let  strmm = strm_get_mutable strm in is_null strmm.partialsegments.lhead) else (true))); C.String.print (C.String.of_literal "Merge of out-of-order data is NYI")) else (); pop_frame ()
```


 Stream data has arrived from the peer.  Merge it in, taking care of out-of-order and
    partial/overlapping/disjoint segments 

```fsharp
let ((setMaxStreamData (cs:pointer connection) (stream:U32.t) (maxdata:U64.t)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strm = quic_OpenStream cs stream in let  strmm = strm_get_mutable strm in let  maxdata = if U64.gt maxdata strmm.maxStreamData then maxdata else strmm.maxStreamData in upd_maxStreamData (!*(strm)).p.qsm_state maxdata; pop_frame ()
```


 Set the maximum allowable offset for a given stream 

```fsharp
let ((ackStream (cs:pointer connection) (t:streamRecoveryTracker)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); setEvent (!*((t.segment))).p.available; pop_frame ()
```


 Called when a previously sent stream segment has been ACK'd by the peer.  This
    releases the data 

```fsharp
let ((lostStream (cs:pointer connection) (t:streamRecoveryTracker)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  csm = conn_get_mutable cs in let  strm = findStream csm t.recoverystreamID in let  strmm = strm_get_mutable strm in let  seg = t.segment in let  list = insertHeadList strmm.segments seg in upd_segments (!*(strm)).p.qsm_state list; setEvent (!*(cs)).dataReadyToSend; pop_frame ()
```


 Called by LossandCongestion when it determines that a packet has been lost,
    and the stream data must be retransmitted. 

