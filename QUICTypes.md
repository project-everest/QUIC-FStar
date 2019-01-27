# module QUICTypes
Common datatypes



QUIC Types - the set of datatypes shared across all of the QUIC codebase.



```fsharp
type abbrev 
```


 Type of a network buffer 

```fsharp
type abbrev 
```


 Type of an offset into a buffer of bytes 

```fsharp
type dlist = { (* Forward link *)flink:pointer_or_null (dlist t); (* Backward link *)blink:pointer_or_null (dlist t); (* payload *)p:t } 
```


 A doubly-linked list of quic_stream 

```fsharp
type dlisthead = { (* head forward link *)lhead:pointer_or_null (dlist t); (* head backward link *)ltail:pointer_or_null (dlist t) } 
```


 Head of a doubly linked list 

```fsharp
let ((empty_entry (#t:Type) (payload:t)):dlist (t)):{flink=null (dlist t) blink=null (dlist t) p=payload}
```


 Initialze an element of a doubly linked list 

```fsharp
let ((empty_list (#t:Type)):dlisthead t):{lhead=null t ltail=null t}
```


 Initialize a doubly-linked list head 

```fsharp
let ((insertHeadList (#t:Type) (h:dlisthead t) (e:pointer (dlist t))):(Stack (dlisthead t) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):if is_null h.lhead then (.()<-(e, 0, {.()(e, 0) with flink=null t blink=null t}); {lhead=e ltail=e}) else (let  next = h.lhead in .()<-(next, 0, {!*(next) with blink=e}); .()<-(e, 0, {.()(e, 0) with flink=next blink=null t}); {lhead=e ltail=h.ltail})
```


 Insert an element e as the first element in a doubly linked list 

```fsharp
let ((insertTailList (#t:Type) (h:dlisthead t) (e:pointer (dlist t))):(Stack (dlisthead t) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):if is_null h.lhead then (.()<-(e, 0, {!*(e) with flink=null t blink=null t}); {lhead=e ltail=e}) else (let  prev = h.ltail in .()<-(prev, 0, {!*(prev) with flink=e}); .()<-(e, 0, {!*(e) with flink=null t blink=prev}); {lhead=h.lhead ltail=e})
```


 Insert an element e as the last element in a doubly linked list. 

```fsharp
let ((removeEntryList (#t:Type) (h:dlisthead t) (e:pointer (dlist t))):(Stack (dlisthead t) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):if =(h.lhead, e) then (if =(h.ltail, e) then ({lhead=null t ltail=null t}) else (let  next = (!*(e)).flink in .()<-(next, 0, {.()(next, 0) with blink=null t}); {lhead=(!*(e)).flink ltail=h.ltail})) else if =(h.ltail, e) then (let  prev = (!*(e)).blink in .()<-(prev, 0, {.()(prev, 0) with flink=null t}); {lhead=h.lhead ltail=(!*(e)).blink}) else (let  next = (!*(e)).flink in let  prev = (!*(e)).blink in .()<-(prev, 0, {.()(prev, 0) with flink=next}); .()<-(next, 0, {.()(next, 0) with blink=prev}); h)
```


 Remove entry e from the doubly linked list 

```fsharp
let ((insertEntryAfter (#t:Type) (h:dlisthead t) (prior:pointer (dlist t)) (e:pointer (dlist t))):(Stack (dlisthead t) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):if =(h.ltail, prior) then (insertTailList h e) else (let  next = (!*(prior)).flink in .()<-(prior, 0, {.()(prior, 0) with flink=e}); .()<-(e, 0, {.()(e, 0) with blink=prior flink=next}); .()<-(next, 0, {.()(next, 0) with blink=e}); h)
```


 Insert e after prior, in list h 

```fsharp
let ((insertEntryBefore (#t:Type) (h:dlisthead t) (next:pointer (dlist t)) (e:pointer (dlist t))):(Stack (dlisthead t) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):if =(h.lhead, next) then (insertHeadList h e) else (let  prior = (!*(next)).blink in .()<-(prior, 0, {.()(prior, 0) with flink=e}); .()<-(e, 0, {.()(e, 0) with blink=prior flink=next}); .()<-(next, 0, {.()(next, 0) with blink=e}); h)
```


 Insert e after next, in list h 

```fsharp
type mitls_hash = TLS_hash_MD5: | TLS_hash_SHA1: | TLS_hash_SHA224: | TLS_hash_SHA256: | TLS_hash_SHA384: | TLS_hash_SHA512: 
```


 mitls_hash enum, from mitls FFI 

```fsharp
type mitls_aead = TLS_aead_AES_128_GCM: | TLS_aead_AES_256_GCM: | TLS_aead_CHACHA20_POLY1305: 
```


 mitls_aead, from mitls FFI 

```fsharp
type mitls_secret = { (* hash type *)hash:mitls_hash; (* aead type *)ae:mitls_aead; (* secret length, in bytes *)secret_length:U32.t; (* secret value *)secret:FStar.Buffer.buffer (C.char) } 
```


 F* representation of mitls_secret, which is serialized into an array of bytes and pinned, for interop.  Used for FFI. 

```fsharp
type mitls_ticket = { ticket_len:U64.t; ticket:FStar.Buffer.buffer (C.char); session_len:U64.t; session:FStar.Buffer.buffer (C.char) } 
```


 A miTLS ticket.  Used for FFI 

```fsharp
val intptr_to_uint32:Unidentified product: [intptr_t] U32.t
```


 FFI helper - cast an intptr_t to a UInt32.t.  Use with care, as it will truncate the value 

```fsharp
val uint32_to_intptr:Unidentified product: [U32.t] intptr_t
```


 FFI helper - cast a UInt32.t to an intptr_t. 

```fsharp
type abbrev 
```


 an opaque handle to a crypto key 

```fsharp
type abbrev 
```


 backed by a C mitls_secret (4 bytes, 4 bytes, 20 bytes) 

```fsharp
type qstream_segment_fixed = { (* Starting byte offset within the stream *)offset:U64.t; (* Actual stream data *)data:buffer_t; (* Length of the stream data in bytes *)datalength:U32.t; (* Is the final segment *)fin:bool; (* Waitable HANDLE, manual-reset, to signal that the data is ready for consumption *)available:intptr_t } 
```


 A segment of data within a stream 

```fsharp
type abbrev 
```


 Either on quic_stream.segments (for outgoing data), or on partialsegments or readysegments (for incoming data) 

```fsharp
type quic_stream_state = StreamIdle: | StreamOpen: | StreamHalfClosedLocal: | StreamHalfClosedRemote: | StreamClosed: 
```


 The QUIC view of a stream state 

```fsharp
type stream_state = AppOpen: | AppFin: | AppClosed: 
```


 The app view of a stream state 

```fsharp
type quic_stream_mutable = { (* The QUIC-level state, based on ACKd messages fromm the peer.  The app state may be quite different. *)state:quic_stream_state; (* The app-level state *)appstate:stream_state; (* Next stream offset where writes will go *)nextWriteOffset:U64.t; (* For throttling stream sends *)maxStreamData:U64.t; (* Data that is ready to send for the first time *)segments:qstream_segment_list; (* Data arriving with offsets above this go into partialsegments *)nextReadOffset:U64.t; (* Data that has been received but is still incomplete *)partialsegments:qstream_segment_list; (* Data that has been recieved and is ready for QUIC_RecvStream() to return *)readysegments:qstream_segment_list } 
```


 Mutable portion of a QUIC stream 

```fsharp
type quic_stream_fixed = { streamID:U32.t; (* A HANDLE to a manual reset event.  Set whenever readysegments is nonempty *)hasDataReady:intptr_t; qsm_state:(pointer quic_stream_mutable) } 
```


 A QUIC stream of outgoing data 

```fsharp
type streamRecoveryTracker = { recoverystreamID:U32.t; segment:pointer qstream_segment } 
```


 Data required, in order to recover a stream frame from a lost packet 

```fsharp
type ackblock_fixed = { gap:U64.t; start:U64.t; length:U64.t } 
```


 Helper, with encoding of ACK frames 

```fsharp
type ackRecoveryTracker = { largestAcknowledged:U64.t; blocks:ackblock_list } 
```


 Data required, in order to recover an ACK frame from a lost packet 

```fsharp
type sentPacket_fixed = { (* Time the packet was sent, in 100ns Windows ticks *)time:Int64.t; packet_number:U64.t; (* Number of retransmittable bytes in this packet *)bytes:UInt16.t; tracker:lossRecoveryTracker_list } 
```


 Data associated with a sent packet, used to recover in case of loss 

```fsharp
type lossAndCongestion_mutable = { (* (fixed field) multi-modal alarm used for loss detection.  A PTP_TIMER *)loss_detection_alarm:intptr_t; (* (fixed field) - a PTP_TIMER *)ping_alarm:intptr_t; (* The number of times the handshake packets have been retransmitted without receiving an ack *)handshake_count:UInt32.t; (* The number of times a tail loss probe has been sent without receiving an ack *)tlp_count:UInt32.t; (* The number of times an rto has been sent without receiving an ack. *)rto_count:UInt32.t; (*The last packet number sent prior to the first retransmission timeout. *)largest_sent_before_rto:U64.t; (* The time the most recent packet was sent. In 100ns Windows ticks*)time_of_last_sent_packet:Int64.t; (* The packet number of the most recently sent packet. *)largest_sent_packet:U64.t; (* The largest packet number acknowledged in an ack frame. *)largest_acked_packet:U64.t; (* The most recent RTT measurement made when receiving an ack for a previously unacked packet *)latest_rtt:Int64.t; (* The smoothed RTT of the connection, computed as described in [RFC6298] *)smoothed_rtt:Int64.t; (* The RTT variance, computed as described in [RFC6298] *)rttvar:Int64.t; (*The largest delta between the largest acked retransmittable packet
       and a packet containing retransmittable frames before it’s declared lost. *)reordering_threshold:U64.t; (* The reordering window as a fraction of max(smoothed_rtt, latest_rtt). *)time_reordering_fraction_numerator:Int64.t; time_reordering_fraction_denominator:Int64.t; (* The time at which the next packet will be considered lost based on early transmit or 
        exceeding the reordering window in time. *)loss_time:Int64.t; (* An association of packet numbers to information about them, including a number field indicating
        the packet number, a time field indicating the time a packet was sent, and a bytes field
        indicating the packet’s size. sent_packets is ordered by packet number, and packets remain
        in sent_packets until acknowledged or lost. *)sent_packets:sentPacket_list; retransmittable_packets_outstanding:UInt32.t; handshake_packets_outstanding:bool; (* The sum of the size in bytes of all sent packets
        that contain at least one retransmittable or PADDING frame, and
        have not been acked or declared lost.  The size does not include
        IP or UDP overhead.  Packets only containing ack frames do not
        count towards byte_in_flight to ensure congestion control does not
        impede congestion feedback. *)bytes_in_flight:U64.t; (* The packet number after which QUIC will no longer be in recovery. *)end_of_recovery:U64.t; (* Maximum number of bytes in flight that may be sent. *)congestion_window:U64.t; (* Slow start threshold in bytes. When the congestion window is below ssthresh, it grows by the 
        number of bytes acknowledged for each ack. *)ssthresh:U64.t } 
```


 Mutable state related to the LossAndCongestion module.  Fields are generally
    all taken directly from the QUIC RFC. 

```fsharp
type connection_state = Start: | ClientInitial: | ServerStatelessRetry: | Cleartext: | Protected: 
```


 States of a QUIC connection 

```fsharp
type packet_holder_fixed = { packet:buffer_t; packetlen:U32.t } 
```


 A queue of packets that have arrived but haven't been processed yet 

```fsharp
type connection_mutable = { cstate:connection_state; connectionID:U64.t; connectionID0RTT:U64.t; mitls_state:quic_state; packetNumber:U64.t; maxReceivedPacketNumber:U64.t; key1rttEncrypt:quic_key; key1rttDecrypt:quic_key; key0rtt:quic_key; stream0BytesReceived:U64.t; defaultMaxStreamData:U64.t; maxData:U64.t; maxStreamID:U32.t; maxPayloadSize:U32.t; pingPending:bool; streams:quic_stream_list; shortHeaderPackets:packet_holder_list; (* count of acks in outgoingAks *)outgoingAckCount:U32.t } 
```


 The mutable state related to a QUIC connection 

```fsharp
type connection = { monitor:intptr_t; encryptkey:quic_key; decryptkey:quic_key; (* A HANDLE to a manual reset event *)dataReadyToSend:intptr_t; (* max count of entries in outgoingAcks allocation *)maxoutgoingAcks:U32.t; outgoingAcks:(pointer U64.t); landc_state:(pointer lossAndCongestion_mutable); csm_state:(pointer connection_mutable) } 
```


 All state associated with a QUIC connection between two computers 

