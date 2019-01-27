(**

QUIC Types - the set of datatypes shared across all of the QUIC codebase.

@summary:  Common datatypes
*)
module QUICTypes

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Int
open C
open C.String
open LowStar.Buffer
open LowStar.BufferOps
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module I32 = FStar.Int32
module B = LowStar.Buffer

(** Type of a network buffer *)
type buffer_t = B.buffer(UInt8.t)

(** A doubly-linked list of a type*)
type dlist (t:Type0) = {
(* Forward link *)
  flink: pointer_or_null (dlist t);
(* Backward link *)
  blink: pointer_or_null (dlist t);
(* payload *)
  p: t;
}

(** Head of a doubly linked list *)
type dlisthead (t:Type) = {
  (* head forward link *)
  lhead: pointer_or_null (dlist t);
  (* head backward link *)
  ltail: pointer_or_null (dlist t);
}

(** Initialze an element of a doubly linked list *)
let empty_entry (#t:Type) (payload:t): dlist(t) =
  { flink = null; blink = null; p = payload; }
  
(** Initialize a doubly-linked list head *)
let empty_list (#t:Type) : dlisthead t =
  { lhead = null; ltail = null;}

(** Insert an element e as the first element in a doubly linked list *)
let insertHeadList (#t:Type) (h:dlisthead t) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if is_null h.lhead then ( // the list is empty
    e *= { !*e with flink=null; blink = null};
    { lhead = e; ltail = e; }
  ) else (
    let next = h.lhead in
    next *= { !*next with blink=e; };  // next->blink = e
    e *= { !*e with flink=next; blink = null }; // e.flink=next/e.blink=null
    { lhead = e; ltail = h.ltail }
  )

(** Insert an element e as the last element in a doubly linked list. *)
let insertTailList (#t:Type) (h:dlisthead t) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if is_null h.lhead then ( // the list is empty
    e *= { !*e with flink=null; blink = null };
    { lhead = e; ltail = e; }
  ) else (
    let prev = h.ltail in
    prev *={ !*prev with flink=e; }; // tail->flink=e
    e *= { !*e with flink=null; blink = prev }; // e->flink=null/e.blink=tail
    { lhead = h.lhead; ltail = e; }
  )

(** Remove entry e from the doubly linked list *)
let removeEntryList (#t:Type) (h:dlisthead t) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if h.lhead = e then ( // removing from the head of the list
    if h.ltail = e then (// and removing from the tail - the list will now be empty
      { lhead = null; ltail = null; }
    ) else (
      let next = (!*e).flink in
      next *= { !*next with blink = null; }; // e.flink.blink <- null
      { lhead = (!*e).flink; ltail = h.ltail; }
    )
  ) else if h.ltail = e then ( // removing from the tail of the list, but the list will be non-empty
    let prev = (!*e).blink in
    prev *= { !*prev with flink = null; }; // e.blink.flink <- null
    { lhead = h.lhead; ltail = (!*e).blink; }
  ) else ( // removing from the middle of the list
    let next = (!*e).flink in
    let prev = (!*e).blink in
    prev *= { !*prev with flink = next; };
    next *= { !*next with blink = prev; };
    h
  )

(** Insert e after prior, in list h *)
let insertEntryAfter (#t:Type) (h:dlisthead t) (prior:pointer (dlist t)) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if h.ltail = prior then ( // appending to the end of the list
    insertTailList h e
  ) else (
    let next = (!*prior).flink in
    prior *= { !*prior with flink = e };
    e *= { !*e with blink=prior; flink=next };
    next *={ !*next with blink = e };
    h
  )

(** Insert e after next, in list h *)
let insertEntryBefore (#t:Type) (h:dlisthead t) (next:pointer (dlist t)) (e:pointer (dlist t)): ST (dlisthead t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if h.lhead = next then ( // adding to the front of the list
    insertHeadList h e
  ) else (
    let prior = (!*next).blink in
    prior *= { !*prior with flink = e };
    e *= { !*e with blink=prior; flink=next };
    next *= { !*next with blink = e };
    h
  )

type err a =
  | Ok of a
  | Fail of C.String.t

inline_for_extraction
let return (#a:Type) (x:a) : err a = Ok x

inline_for_extraction
let fail (#a:Type) (msg:C.String.t) : err a = Fail msg

inline_for_extraction
let bind (#a:Type) (#b:Type)
         (f:err a)
         (g: a -> St (err b))
    : St (err b)
    = match f with
      | Ok x -> g x
      | Fail msg -> Fail msg

(** mitls_hash enum, from mitls FFI *)
type mitls_hash =
    | TLS_hash_MD5
    | TLS_hash_SHA1
    | TLS_hash_SHA224
    | TLS_hash_SHA256
    | TLS_hash_SHA384
    | TLS_hash_SHA512

(** mitls_aead, from mitls FFI *)
type mitls_aead =
    | TLS_aead_AES_128_GCM
    | TLS_aead_AES_256_GCM
    | TLS_aead_CHACHA20_POLY1305
    
(** F* representation of mitls_secret, which is serialized into an array of bytes and pinned, for interop.  Used for FFI. *)
type mitls_secret = {
    (** hash type *)
    hash: mitls_hash;
    (** aead type *)
    ae: mitls_aead;
    (** secret length, in bytes *)
    secret_length: U32.t;
    (** secret value *)
    secret: Buffer.buffer (C.char);
}

(** A miTLS ticket *)
type mitls_ticket = {
    ticket_len: U64.t;
    ticket: buffer_t; // bugbug: an array of 1020 bytes, not a ptr
    session_len: U64.t;
    session: buffer_t; // bugbug: an array of 256 bytes, not a ptr
}

type quic_state = intptr_t
type quic_key = intptr_t (** an opaque handle to a crypto key *)
type mitls_secret_native = intptr_t (** backed by a C mitls_secret (4 bytes, 4 bytes, 20 bytes) *)
type quic_hash = mitls_hash
type quic_aead = mitls_aead
type quic_secret = mitls_secret
type quic_secret_native = mitls_secret_native
type quic_ticket = mitls_ticket

(** A segment of data within a stream *)
type qstream_segment_fixed = {
    (** Starting byte offset within the stream *)
    offset:U64.t;
    (** Actual stream data *)
    data:buffer_t;
    (** Length of the stream data in bytes *)
    datalength:U32.t;
    (** Is the final segment *)
    fin:bool;
    (** Is the buffer owned by the calling application?  Otherwise, it's owned by QUIC-F* *)
    isApplicationOwned:bool;
    (** Waitable HANDLE, manual-reset, to signal that the data is ready for consumption *)
    available:intptr_t;
}

(** Either on quic_stream.segments (for outgoing data), or on partialsegments or readysegments (for incoming data) *)
type qstream_segment = dlist qstream_segment_fixed
type qstream_segment_list = dlisthead qstream_segment_fixed

(** A fixed-value frame, queued for transmission.  Used for frames other than
    the dynamic ones (ACK, STREAM).  *)
type fixedframe_fixed = {
    (** Waitable event HANDLE, or 0 if the event is async *)
    hWait:intptr_t;
    framedata:buffer_t;
    framelength:U32.t;
}

(** A list of fixed-value frames *)
type fixedframe = dlist fixedframe_fixed
type fixedframe_list = dlisthead fixedframe_fixed

(** The QUIC view of a Send Stream *)
type quic_send_stream_state =
  //| SendStreamReady
  | SendStreamSend
  | SendStreamDataSent
  | SendStreamResetSent
  | SendStreamDataRecvd // terminal state
  | SendStreamResetRecvd // terminal state

(** The QUIC view of a Recv Stream *)
type quic_recv_stream_state =
  | RecvStreamRecv
  //| RecvStreamSizeKnown
  //| RecvStreamDataRecvd
  | RecvStreamResetRecvd
  | RecvStreamDataRead  // terminal state
  | RecvStreamResetRead // terminal state

(** Mutable portion of a QUIC stream *)
type quic_stream_mutable = {
  (* Receive-stream fields *)
  (** Current recv-stream state *)
  recvState: quic_recv_stream_state;
  (** Data that has been received but is still incomplete *)
  partialsegments: qstream_segment_list;
  (** Data that has been recieved and is ready for QUIC_RecvStream() to return *)
  readysegments: qstream_segment_list;
  (** Data arriving with offsets above this go into partialsegments *)
  nextReadOffset: U64.t;
  (** Error code, set by RST_STREAM *)
  error_code: U16.t;

  (* Send-stream fields *)
  (** Current send-stream state *)
  sendState: quic_send_stream_state;
  (** Next stream offset where writes will go *)
  nextWriteOffset: U64.t;
  (** For throttling stream sends *)
  maxStreamData: U64.t;
  (** Data that is ready to send for the first time *)
  segments: qstream_segment_list;
}

(** A QUIC stream of outgoing data *)
type quic_stream_fixed = {
    streamID: U64.t;
    qsm_state: (pointer quic_stream_mutable);
}

type quic_stream = dlist quic_stream_fixed
type quic_stream_list = dlisthead quic_stream_fixed

(** Data required, in order to recover a CRYPTO frame from a lost packet *)
type cryptoRecoveryTracker = {
    cryptosegment: pointer qstream_segment;
    }
    
(** Data required, in order to recover a stream frame from a lost packet *)
type streamRecoveryTracker = {
    recoverystreamID: U64.t; // the ID isn't used, but helpful for debugging
    segment: pointer qstream_segment;
    }

(** Helper, with encoding of ACK frames *)
type ackblock_fixed = {
    gap: U64.t;
    start: U64.t;
    length: U64.t;
    }

type ackblock = dlist ackblock_fixed
type ackblock_list = dlisthead ackblock_fixed

(* Indicies into the connection.packetSpaces array *)
let psIndexInitial = 0ul
let psIndexHandshake = 1ul
let psIndexApplication = 2ul

type packet_space =
    | InitialSpace
    | HandshakeSpace
    | ApplicationSpace

(* Translate a packet_space value to a psIndex* value *)
let indexOfPacketSpace (ps:packet_space): U32.t =
  match ps with
  | InitialSpace -> psIndexInitial
  | HandshakeSpace -> psIndexHandshake
  | ApplicationSpace -> psIndexApplication

(** Data required, in order to recover an ACK frame from a lost packet *)
type ackRecoveryTracker = {
    blocks: ackblock_list;
    }

type lossRecoveryTracker_fixed =
    | CryptoTracker of cryptoRecoveryTracker
    | StrmTracker of streamRecoveryTracker
    | AckTracker of ackblock_list
    | FixedFrameTracker of pointer fixedframe

type lossRecoveryTracker = dlist lossRecoveryTracker_fixed
type lossRecoveryTracker_list = dlisthead lossRecoveryTracker_fixed

(** Data associated with a sent packet, used to recover in case of loss *)
type sentPacket_fixed = {
    (** Time the packet was sent, in 100ns Windows ticks *)
    time: Int64.t;
    ps: packet_space;
    packet_number: U64.t;
    (** Number of retransmittable bytes in this packet *)
    bytes: UInt16.t;
    tracker: lossRecoveryTracker_list;
    }

type sentPacket = dlist sentPacket_fixed
type sentPacket_list = dlisthead sentPacket_fixed

(** Mutable state related to the LossAndCongestion module.  Fields are generally
    all taken directly from the QUIC RFC. *)
type lossAndCongestion_mutable = {
    (** (fixed field) multi-modal alarm used for loss detection.  A PTP_TIMER *)
    loss_detection_alarm: intptr_t; // PTP_TIMER

    (** (fixed field) - a PTP_TIMER *)
    ping_alarm: intptr_t;

    (** The number of times the handshake packets have been retransmitted without receiving an ack *)
    handshake_count: UInt32.t;

    (** The number of times a tail loss probe has been sent without receiving an ack *)
    tlp_count: UInt32.t;

    (** The number of times an rto has been sent without receiving an ack. *)
    rto_count: UInt32.t;

    (**The last packet number sent prior to the first retransmission timeout. *)
    largest_sent_before_rto: U64.t;

    (** The time the most recent packet was sent. In 100ns Windows ticks*)
    time_of_last_sent_packet: Int64.t;

    (** The packet number of the most recently sent packet. *)
    largest_sent_packet: U64.t;

    (** The largest packet number acknowledged in an ack frame. *)
    largest_acked_packet: U64.t;

    (** The most recent RTT measurement made when receiving an ack for a previously unacked packet *)
    latest_rtt: Int64.t;

    (** The smoothed RTT of the connection, computed as described in [RFC6298] *)
    smoothed_rtt: Int64.t;

    (** The RTT variance, computed as described in [RFC6298] *)
    rttvar: Int64.t;
    
    (**The largest delta between the largest acked retransmittable packet
       and a packet containing retransmittable frames before it’s declared lost. *)
    reordering_threshold: U64.t;

    (** The reordering window as a fraction of max(smoothed_rtt, latest_rtt). *)
    time_reordering_fraction_numerator: Int64.t;
    time_reordering_fraction_denominator: Int64.t;
    
    (** The time at which the next packet will be considered lost based on early transmit or 
        exceeding the reordering window in time. *)
    loss_time: Int64.t;
    
    (** An association of packet numbers to information about them, including a number field indicating
        the packet number, a time field indicating the time a packet was sent, and a bytes field
        indicating the packet’s size. sent_packets is ordered by packet number, and packets remain
        in sent_packets until acknowledged or lost. *)
    sent_packets: sentPacket_list;

    (* The following are fields not specified in QUIC-RECOVERY, but useful *)
    retransmittable_packets_outstanding: UInt32.t;
    handshake_packets_outstanding: bool; // bugbug: handle this

    (* Congestion Control variables *)

    (** The sum of the size in bytes of all sent packets
        that contain at least one retransmittable or PADDING frame, and
        have not been acked or declared lost.  The size does not include
        IP or UDP overhead.  Packets only containing ack frames do not
        count towards byte_in_flight to ensure congestion control does not
        impede congestion feedback. *)
    bytes_in_flight: U64.t;

    (** The packet number after which QUIC will no longer be in recovery. *)
    end_of_recovery: U64.t;

    (** Maximum number of bytes in flight that may be sent. *)
    congestion_window: U64.t;
    
    (** Slow start threshold in bytes. When the congestion window is below ssthresh, it grows by the 
        number of bytes acknowledged for each ack. *)
    ssthresh: U64.t;
    }

(** States of a QUIC connection *)
type connection_state =
    | Start 
    | ServerStatelessRetry
    | Running
    | Closed

(** A queue of packets that have arrived but haven't been processed yet *)
type packet_holder_fixed = {
  packet:buffer_t;
  packetlen:U32.t;
}

type packet_holder = dlist packet_holder_fixed
type packet_holder_list = dlisthead packet_holder_fixed

type stream_holder = dlist (pointer quic_stream)
type stream_holder_list = dlisthead (pointer quic_stream)

(** A legal connection ID length *)
type cil_t = cil:U8.t {U8.v cil = 0 || (4 <= (U8.v cil) && (U8.v cil) <= 18)}

type connectionid_t = {
    cil: cil_t;     // either 0, or 4..18
    cid: buffer_t;  // whose length in bytes is cil
    }

(** A pair of crypto keys *)
type key_pair = {
    reader: quic_key;
    writer: quic_key;
    }

(* Indicies into the connection.keys array *)
let epochIndexInitial = 0ul
let epochIndex0RTT = 1ul
let epochIndexHandshake= 2ul
let epochIndex1RTT = 3ul

type epoch =
  | EpochInitial
  | Epoch0RTT
  | EpochHandshake
  | Epoch1RTT

let indexOfEpoch (epoch:epoch): U32.t =
  match epoch with
  | EpochInitial -> epochIndexInitial
  | Epoch0RTT -> epochIndex0RTT
  | EpochHandshake -> epochIndexHandshake
  | Epoch1RTT -> epochIndex1RTT

(** State associated with a packet space.  There are three spaces: Initial, Handshake, and Application *)
type packet_space_state = {
  (** next packet number to transmit with *)
  packetNumber: U64.t;

  (** number of unacknowledged packets *)
  numberNotYetAcked: U64.t;

  (** highest packet number seen so far *)
  maxReceivedPacketNumber: U64.t;

  (** queue of outgoing ACKs *)
  outgoingAcks: (pointer U64.t); (* of length maxoutgoingAcks *)

  (** count of entries in outgoingAcks *)
  outgoingAckCount: U32.t;

  (** set when it's OK to send an ACK-only packet *)
  sendAckOnlyIfNeeded: bool;

  (** A bidirection stream of data to/from CRYPTO frames *)
  crypto_stream: pointer quic_stream;
}

(** The mutable state related to a QUIC connection *)
type connection_mutable = {
    cstate: connection_state;
    closedReason: C.String.t; // set whenever the connection is closed
    app_state: intptr_t; // opaque-to-QUICFStar app state associated with the connection
    dest_connectionID: connectionid_t;
    mitls_state: quic_state;

    epoch: epoch;
    mitls_reader_key: I32.t;
    mitls_writer_key: I32.t;

    defaultMaxStreamData: U64.t; // Set via the peer's transport parameters
    maxDataPeer: U64.t; // Set via the peer's transport parameters
    maxStreamID_BIDIPeer: U64.t; // Set via the peer's transport parameters
    maxStreamID_UNIPeer: U64.t; // Set via the peer's transport parameters
    maxDataLocal: U64.t; // Set via the peer's transport parameters
    maxStreamID_BIDILocal: U64.t; // Set via the peer's transport parameters
    maxStreamID_UNILocal: U64.t; // Set via the peer's transport parameters
    maxPayloadSize: U32.t;
    pingPending:bool;

    dataSent:U64.t; // sum of all data sent in STREAM frames.  Must be <= maxDataPeer.
    dataReceived:U64.t; // sum all all received STREAM frames.  Must be <= maxDataLocal.

    streams: quic_stream_list; // List of all active streams
    readystreams: stream_holder_list; // List of streams that have recieved data, ready for quic_recvstream()
    shortHeaderPackets: packet_holder_list;
    fixedframes: fixedframe_list;

    // 0-RTT support
    tls_ticket: pointer_or_null mitls_ticket;
    }

(** An opaque representation of (pointer engine), as F* does not
    support recursive types. *)
type engine_t = intptr_t

(** All state associated with a QUIC connection between two computers *)
type connection = {
    monitor: intptr_t;
    (** array of 4 key pairs (Initial, 0RTT, Handshake, 1RTT) *)
    keys: B.buffer(key_pair);
    is_client:bool;
    hostname:C.String.t;
    landc_state: (pointer lossAndCongestion_mutable);
    csm_state: (pointer connection_mutable);
    statelessResetToken: buffer_t;
    (** A HANDLE to an auto reset event *)
    handshakeComplete: intptr_t;
    (** A HANDLE to a manual reset event.  Set whenever readystreams is non-empty *)
    streamDataAvailable: intptr_t;
    (** A (pointer engine)  *)
    eng: engine_t;
    source_connectionID: connectionid_t;
    (** Array of 3 packet spaces *)
    packetSpaces: (pointer packet_space_state);
    }

type connectionholder = dlist (pointer connection)
type connectionholder_list = dlisthead (pointer connection)

(** New-connection callback.  It is passed the cbstate that was
    initially passed to quic_InitializeServer, along with the new
    connection object.  It returns a value to be stored inside
    the connection, that can be fetched via quic_GetAppstate(),
    and will be returned by quic_PreparePacket(). *)
type newConnectionCallback = intptr_t -> (pointer_or_null connection) -> intptr_t

type versionreply_fixed = {
  replyid:connectionid_t;
  replyapp_state:intptr_t;
}

type versionreply = dlist versionreply_fixed
type versionreply_list = dlisthead versionreply_fixed

(** All state associated with this client or server application *)
type engine = {
    eis_client:bool;
    emonitor: intptr_t;
    ehostname:C.String.t;
    connections:connectionholder_list;
    (** A HANDLE to a manual reset event *)
    dataReadyToSend: intptr_t;
    (** List of connections with data ready to send *)
    readyconnections:connectionholder_list;
    (** List of version nego replies, ready to send *)
    versionreplies:versionreply_list;
    (** App callback, called when a new connection object is created *)
    newconnection: newConnectionCallback;
    (** Opaque value passed to the app callback *)
    newconnection_state: intptr_t;
    (** Length of an outgoing ClientID *)
    eng_cil:cil_t;
    }

let cleartextHashSize:U32.t = 16ul
let quicVersion:U32.t = 0xff00000ful
let maxoutgoingAcks = 4096ul
