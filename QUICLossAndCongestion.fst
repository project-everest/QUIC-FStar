(**

QUIC Loss and Congestion Control

@summary: Implement loss detection and congestion control on the network
*)
module QUICLossAndCongestion

open FStar
open FStar.HyperStack
open FStar.HyperStack.IO
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Int.Cast
open FStar.Printf
open C
open C.Failure
open C.Loops
open C.String
open LowStar.Buffer
open LowStar.BufferOps
open QUICTypes
open QUICMutators
open QUICStream
open QUICFFI
open QUICUtils

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module I64 = FStar.Int64
module I32 = FStar.Int32
module Cast = FStar.Int.Cast
module B = LowStar.Buffer

// Loss Detection Constants - See section 3.2.1 "Constants of interest"
let kMaxTLPs = 2ul
let kReorderingThreshold = 3UL
let kTimeReorderingFractionNumerator = 1L
let kTimeReorderingFractionDenominator = 8L
inline_for_extraction let kMinTLPTimeout  = I64.(10L*^10000L) // 10ms in ticks
inline_for_extraction let kMinRTOTimeout  = I64.(200L*^1000L) // 200ms ticks
inline_for_extraction let kDelayedAckTimeout = I64.(25L*^10000L) // 25ms in ticks
inline_for_extraction let kDefaultInitialRtt = I64.(100L*^10000L) // 100ms in ticks

// Congestion Control Constants - See section 4.3 "Constants of interest"
let kDefaultMss = 1460UL // The default max packet size used for calculating default and minimum congestion windows.
let kInitialWindow = 14600UL // U64.(10UL*^kDefaultMss)
let kMinimumWindow = 1920UL  // U64.(2UL*^kDefaultMss)
let kLossReductionFactorNumerator = 1UL
let kLossReductionFactorDenominator = 2UL


(** Calculate the next loss&detection alarm time, and set the timer *)
let setLossDetectionAlarm (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let l = landc_get_mutable cs in
  if l.retransmittable_packets_outstanding = 0ul then
    cancelTimer l.loss_detection_alarm
  else I64.(
    let now = getSystemTime() in
    let alarm_duration =
      if l.handshake_packets_outstanding then (
        // Handshake retransmission alarm
        let alarm_duration = 
          if l.smoothed_rtt = 0L then 
            (2L *^ kDefaultInitialRtt)
          else
            (2L *^ l.smoothed_rtt)
        in
        let alarm_duration = if kMinTLPTimeout >^ alarm_duration then kMinTLPTimeout else alarm_duration in
        (alarm_duration *^ (1L <<^ l.handshake_count))
      ) else if l.loss_time <> 0L then (
        l.loss_time -^ now
      ) else if U32.lt l.tlp_count kMaxTLPs then (
        // Tail loss probe
        let alarm_duration =
          if l.retransmittable_packets_outstanding <> 0ul then
           ((3L *^ l.smoothed_rtt) /^ 2L +^ kDelayedAckTimeout)
         else
           kMinTLPTimeout
        in
        let smoothed = I64.(2L *^ l.smoothed_rtt) in
        if alarm_duration >^ smoothed then alarm_duration else smoothed
      ) else (
        // RTO alarm
        let alarm_duration = l.smoothed_rtt +^ 4L *^ l.rttvar in
        let alarm_duration = if alarm_duration >^ kMinRTOTimeout then alarm_duration else kMinRTOTimeout in
        (alarm_duration *^ (1L <<^ l.rto_count))
      )
    in
    // The alarm_duration may be negative, if loss_time is in the past
    let safe_alarm_duration = if alarm_duration <^ 10000L then 10000L else alarm_duration in
    let safe_alarm_duration = safe_alarm_duration *^ 100L in // bugbug: for debugging, slow things down
    setOneShotTimer l.loss_detection_alarm safe_alarm_duration
  );
  pop_frame()

(** Per-packet congestion control *)
let onPacketSentCC (cs:pointer connection) (sent_bytes:U32.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let bytes_in_flight = (!*(!*cs).landc_state).bytes_in_flight in
  let sent_bytes64 = Cast.uint32_to_uint64 sent_bytes in
  upd_bytes_in_flight (!*cs).landc_state U64.(bytes_in_flight +^ sent_bytes64);
  pop_frame()

(** Update Loss&Congestion when a packet has been sent *)
let onPacketSent (cs:pointer connection) (ps:packet_space) (packet_number:U64.t) (sent_bytes:U32.t) (tracker:lossRecoveryTracker_list): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string (sprintf "Prepared packet pn=%uL sent_bytes=%ul\n" packet_number sent_bytes);
  let is_ack_only = sent_bytes = 0ul in
  let now = getSystemTime() in
  upd_time_of_last_sent_packet (!*cs).landc_state now;
  upd_largest_sent_packet (!*cs).landc_state packet_number;
  let spfixed:sentPacket_fixed = {
    time=now;
    ps = ps;
    packet_number=packet_number;
    bytes = Cast.uint32_to_uint16 sent_bytes;
    tracker = tracker;
    } in
  let sp = empty_entry spfixed in
  let psp = B.malloc HyperStack.root sp 1ul in
  let list = insertTailList (!*(!*cs).landc_state).sent_packets psp in
  upd_sent_packets (!*cs).landc_state list;
  if not is_ack_only then (
    onPacketSentCC cs sent_bytes;
    inc_retransmittable_packets_outstanding (!*cs).landc_state;
    setLossDetectionAlarm cs
  );
  pop_frame()

(** Update the RTT based on RFC 6298 *)
let updateRtt (cs:pointer connection) (latest_rtt:I64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  // Based on {{RFC6298}}.
  upd_latest_rtt (!*cs).landc_state latest_rtt;
  let smoothed_rtt = (!*(!*cs).landc_state).smoothed_rtt in
  if smoothed_rtt = 0L then I64.(
    upd_smoothed_rtt (!*cs).landc_state latest_rtt;
    upd_rttvar (!*cs).landc_state (latest_rtt >>^ 1ul)
  ) else I64.(
    let tmp = smoothed_rtt -^ latest_rtt in
    let tmp = if tmp >=^ 0L then tmp else (0L -^ tmp) in
    let rttvar = (!*(!*cs).landc_state).rttvar in
    let rttvar = (3L *^ rttvar +^ tmp) >>^ 2ul in
    let smoothed_rtt = (7L *^ smoothed_rtt +^ latest_rtt) >>^ 3ul in
    upd_rttvar (!*cs).landc_state rttvar;
    upd_smoothed_rtt (!*cs).landc_state smoothed_rtt
  );
  pop_frame()
  
(** Handle ACK of a frame of ACK data *)
let ackAck (cs:pointer connection) (a:ackblock_list): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  // Free all of the ackblock_list elements
  let pb = B.alloca a.lhead 1ul in
  C.Loops.do_while
    (fun h break -> live h pb /\ (break ==> False))
    (fun _ ->
      let b = !*pb in
      pb *= (!*b).flink;
      B.free b;
      is_null !*pb // do...while !is_null !*pb
  );
  pop_frame()

(** Register arrival of a packet, so an ACK will be sent later *)
let registerAck (cs:pointer connection) (ps:packet_space) (pn:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let psn = indexOfPacketSpace ps in
  let p = (!*cs).packetSpaces.(psn) in
  let index = p.outgoingAckCount in
  p.outgoingAcks.(index) <- pn;
  (!*cs).packetSpaces.(psn) <- {p with outgoingAckCount = U32.(index+^1ul) };
  pop_frame()
 
// This belongs in QUICFrame, but needs to be called from this higher-level module
(** Handle loss of a frame of ACK data *)
let lostAck (cs:pointer connection) (ps:packet_space) (a:ackblock_list): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let pb = B.alloca a.lhead 1ul in
  C.Loops.do_while
    (fun h break -> live h pb /\ (break ==> False))
    (fun _ ->
      let b = !*pb in
      let start = (!*b).p.start in
      let length = (!*b).p.length in
      let f (i:U64.t) : ST unit
        (requires (fun _ -> true))
        (ensures (fun _ _ _ -> true))
        =
        let pn = U64.(start +^ i) in
        registerAck cs ps pn
        in
      C.Loops.for64 0UL length (fun h _ -> true) f;
      pb *= (!*b).flink;
      B.free b;
      is_null !*pb // do...while !is_null !*pb
  );
  pop_frame()

(** This handles Ack of a fixedframe *)
let ackFixedframe (cs:pointer connection) (pff:pointer fixedframe): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  // bugbug: on ACK of CONNECTION_CLOSE and APPLICATION_CLOSE, cease transmission
  let framedata = (!*pff).p.framedata in
  let frametype = !*framedata in
  (match frametype with
  | 0x00uy -> print_string "ACKing PADDING\n"
  | 0x01uy -> (
    print_string "ACKing RST_STREAM\n";
    let streamID,_  = getvar framedata 1ul in
    let strm = openStreamInternal cs streamID in
    if strm <> null then (
      let strmm = strm_get_mutable strm in
      if strmm.sendState = SendStreamResetSent then
        upd_sendstate (!*strm).p.qsm_state SendStreamResetRecvd
      )
    )
  | 0x02uy -> (
    print_string "ACKing CONNECTION_CLOSE\n";
    upd_cstate (!*cs).csm_state Closed
    )
  | 0x03uy -> print_string "ACKing APPLICATION_CLOSE\n"
  | 0x04uy -> print_string "ACKing MAX_DATA\n"
  | 0x05uy -> print_string "ACKing MAX_STREAM_DATA\n"
  | 0x06uy -> print_string "ACKing MAX_STREAM_ID\n"
  | 0x07uy -> failwith (of_literal "ACKing PING isn't supported as a fixed frame")
  | 0x08uy -> print_string "ACKing BLOCKED\n"
  | 0x09uy -> print_string "ACKing STREAM_BLOCKED\n"
  | 0x0auy -> print_string "ACKing STREAM_ID_BLOCKED\n"
  | 0x0buy -> print_string "ACKing NEW_CONNECTION_ID\n"
  | 0x0cuy -> print_string "ACKing STOP_SENDING\n"
  | 0x0duy -> print_string "ACKing RETIRE_CONNECTION_ID\n"
  | 0x0euy -> print_string "ACKing PATH_CHALLENGE\n"
  | 0x0fuy -> print_string "ACKing PATH_RESPONSE\n"
  | 0x19uy -> print_string "ACKing NEW_TOKEN\n"
  | _ -> failwith (of_literal "ACKing Unknown fixed-frame kind")
  );
  let hWait = (!*pff).p.hWait in
  if hWait <> nullptr then
    setEvent hWait;
  B.free framedata;
  pop_frame()
  
let lostFixedframe (cs:pointer connection) (pff:pointer fixedframe): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let list = insertHeadList csm.fixedframes pff in
  upd_fixedframes (!*cs).csm_state list;
  pop_frame()

(** Handle loss of a full packet *)
let onPacketLost (cs:pointer connection) (lp:pointer sentPacket) (now:I64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  // Remove lost packets from bytes_in_flight.
  let time_since_sent = I64.(now -^ (!*lp).p.time) in
  let tss = I64.(time_since_sent /^ 10000L) in
  let landcm = landc_get_mutable cs in
  let bytes16 = (!*lp).p.bytes in
  let bytes64 = Cast.uint16_to_uint64 bytes16 in
  upd_bytes_in_flight (!*cs).landc_state U64.(landcm.bytes_in_flight -^ bytes64);
  let pt = B.alloca (!*lp).p.tracker.lhead 1ul in
  C.Loops.do_while
    (fun h break -> live h pt /\ (break ==> False))
    (fun _ ->
      let t:(pointer lossRecoveryTracker) = !*pt in
      (match (!*t).p with
      | CryptoTracker c -> lostCrypto cs (!*lp).p.ps c
      | StrmTracker s -> lostStream cs s
      | AckTracker a -> lostAck cs (!*lp).p.ps a
      | FixedFrameTracker p -> lostFixedframe cs p
      );
      let t = !*pt in
      pt *= (!*(!*pt)).flink;
      B.free t;
      is_null !*pt // do... while !is_null !*pt
    );
  pop_frame()

(** Begin a new recovery epoch *)
let startNewRecoveryEpoch (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let landcm = landc_get_mutable cs in
  upd_end_of_recovery (!*cs).landc_state landcm.largest_sent_packet;
  let cw = U64.(landcm.congestion_window *^ kLossReductionFactorNumerator /^ kLossReductionFactorDenominator) in
  let cw = maxu64 cw kMinimumWindow in
  upd_congestion_window (!*cs).landc_state cw;
  upd_ssthresh (!*cs).landc_state cw;
  pop_frame()
  
(** Determine which previously-sent packets are lost.  This may initiate
    retransmission of data. *)
let detectLostPackets (cs:pointer connection) (largest_acked:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  upd_loss_time (!*cs).landc_state 0L;
  let landcm = landc_get_mutable cs in
  if not (is_null landcm.sent_packets.lhead) then I64.(
    let delay_until_lost =
      if landcm.time_reordering_fraction_denominator <> 0L then (
        let m = maxi64 landcm.latest_rtt landcm.smoothed_rtt in
        let dul = (1L +^ landcm.time_reordering_fraction_numerator) *^ m in
        dul /^ landcm.time_reordering_fraction_denominator
      ) else if largest_acked = landcm.largest_sent_packet then (
        // Early retransmit alarm
        let m = maxi64 landcm.latest_rtt landcm.smoothed_rtt in
        (9L *^ m) /^ 8L
      ) else (
        0x7fffffffffffffffL // maxint64
      ) in
    let last = (!*landcm.sent_packets.ltail) in
    let largest_lost_packet_number = last.p.packet_number in // last is largest
    let now = getSystemTime() in
    let plist = B.alloca landcm.sent_packets 1ul in
    let punacked = B.alloca landcm.sent_packets.lhead 1ul in
    C.Loops.do_while
      (fun h break -> live h punacked /\ (break ==> False))
      (fun _ ->
          let unacked:(pointer sentPacket) = !*punacked in
          let time_since_sent = now -^ (!*unacked).p.time in
          let packet_delta = U64.(largest_acked -^ (!*unacked).p.packet_number) in
          if (time_since_sent >^ delay_until_lost) ||
             (U64.gt packet_delta landcm.reordering_threshold) then (
            plist *= removeEntryList (!*plist) unacked;
            onPacketLost cs unacked now;
            B.free unacked
          ) else if (landcm.loss_time = 0L) && (delay_until_lost <> 0x7fffffffffffL) then (
            upd_loss_time (!*cs).landc_state (now +^ delay_until_lost -^ time_since_sent)
          );
          punacked *= (!*(!*punacked)).flink;
          is_null !*punacked // do... while !is_null !*punacked
      );
    upd_sent_packets (!*cs).landc_state !*plist;
    if connectionHasMoreToSend cs <> None then (
      // new ACKs or stream data may be ready to retransmit
      setHasReadyToSend cs
    );
    if U64.lt landcm.end_of_recovery largest_lost_packet_number then (
      startNewRecoveryEpoch cs
    )
  );
  pop_frame()

(** Determine if a packet number has been sent previously or not *)
let sentPacketsContains (sent_packets:sentPacket_list) (pn:U64.t): ST (pointer_or_null sentPacket)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let head = sent_packets.lhead in
  let pp = B.alloca head 1ul in
  let pret = B.alloca null 1ul in
  let headisnull = is_null head in
  let pstop = B.alloca headisnull 1ul in
  let inv h = B.live h pp in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not !*pstop
  in
  let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    let isfound = (!*(!*pp)).p.packet_number = pn in
    if isfound then (
      pret *= !*pp
      );
    pp *= (!*(!*pp)).flink;
    pstop *= ((is_null !*pp) || isfound)
  in
  C.Loops.while test body;
  let ret = !*pret in
  pop_frame();
  ret

(** Called when an ACK has been received.  Free tracking resources related to the packet. *)
let onAckReceived (cs:pointer connection) (largest_acked:U64.t) (ack_delay:U16.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let lm = landc_get_mutable cs in
  upd_largest_acked_packet (!*cs).landc_state largest_acked;
  let packet = sentPacketsContains lm.sent_packets largest_acked in
  if not (is_null packet) then I64.(
    let largest_acked_time = (!*packet).p.time in
    let now = getSystemTime() in
    let latest_rtt = now -^ largest_acked_time in
    let ack_delay64 = Cast.uint16_to_int64 ack_delay in
    let latest_rtt = 
      if latest_rtt >^ ack_delay64 then (
        latest_rtt -^ ack_delay64
      ) else (
        latest_rtt
      ) in
    upd_latest_rtt (!*cs).landc_state latest_rtt;
    updateRtt cs latest_rtt;
    // Find all newly acked packets
    // for acked_packet in DetermineNewlyAckedPackets():
    //  OnPacketAcked(acked_packet.packet_number)
    detectLostPackets cs largest_acked;
    setLossDetectionAlarm cs
  );
  pop_frame()

(** Congestion Control for an ack'd packet *)
let onPacketAckedCC (cs:pointer connection) (acked_packet: pointer sentPacket): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let bytes_in_flight = (!*(!*cs).landc_state).bytes_in_flight in
  let acked_bytes = (!*acked_packet).p.bytes in
  let acked_bytes = Cast.uint16_to_uint64 acked_bytes in
  let bytes_in_flight = U64.(bytes_in_flight +^ acked_bytes) in
  upd_bytes_in_flight (!*cs).landc_state bytes_in_flight;
  if U64.gte (!*acked_packet).p.packet_number (!*(!*cs).landc_state).end_of_recovery then (
    let cw = (!*(!*cs).landc_state).congestion_window in
    let ssthresh =  (!*(!*cs).landc_state).ssthresh in
    let cw = if U64.lt cw ssthresh then (
      // Slow start
      U64.(cw +^ acked_bytes)
    ) else (
      U64.(cw +^ kDefaultMss *^ acked_bytes /^ cw)
    ) in
    upd_congestion_window (!*cs).landc_state cw
  );
  // else Do not increase congestion window in recovery period.
  pop_frame()
  
let onRetransmissionTimeoutVerified (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  upd_congestion_window (!*cs).landc_state kMinimumWindow;
  pop_frame()

(** Ack one tracker *)
let ackTracker (cs:pointer connection) (t:pointer lossRecoveryTracker): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  (match (!*t).p with
  | CryptoTracker c -> ackCrypto cs c
  | StrmTracker s -> ackStream cs s
  | AckTracker a -> ackAck cs a
  | FixedFrameTracker f -> ackFixedframe cs f
  );
  pop_frame()
  
(** Walk the lossRecoveryTracker list and ack each element.  On return, all
    entries in the list have been freed.  *)
let ackTrackerList (cs:pointer connection) (l:lossRecoveryTracker_list) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let head = l.lhead in
  let pp = B.alloca head 1ul in
  let inv h = B.live h pp in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not (is_null !*pp)
  in
  let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    ackTracker cs !*pp;
    let tmp = !*pp in
    pp *= (!*(!*pp)).flink;
    B.free tmp
  in
  C.Loops.while test body;
  pop_frame()

(** A packet has been ACK'd by the peer *)
let onPacketAcked (cs:pointer connection) (acked_packet_number:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let lm = landc_get_mutable cs in
  let acked_packet = sentPacketsContains lm.sent_packets acked_packet_number in
  if not (is_null acked_packet) then (
    onPacketAckedCC cs acked_packet;
    let list = removeEntryList lm.sent_packets acked_packet in
    upd_sent_packets (!*cs).landc_state list;
    if (!*acked_packet).p.bytes <> 0us then (
      dec_retransmittable_packets_outstanding (!*cs).landc_state
    );
    ackTrackerList cs (!*acked_packet).p.tracker;
    B.free acked_packet // the p.tracker list has already been freed
  ) else (
    () // packet wasn't found in sent_packets
  );
  if (U32.gt lm.rto_count 0ul) && (U64.gt acked_packet_number lm.largest_sent_before_rto) then (
    onRetransmissionTimeoutVerified cs
  );
  upd_handshake_count (!*cs).landc_state 0ul;
  upd_tlp_count (!*cs).landc_state 0ul;
  upd_rto_count (!*cs).landc_state 0ul;
  pop_frame()

(** Handshake has been lost.  Retransmit. *)
let retransmitAllHandshakePackets (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  print_string "retransmitAllHandshakePackets NYI\n"

let sendOnePacket (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  print_string "sendOnePacket NYI\n"

let sendTwoPackets (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  print_string "sendTwoPackets NYI\n"

(** Alarm callback, when the loss-timer fires. *)
let onLossDetectionAlarm (ignore1:intptr_t) (cs:pointer connection) (ignore2:intptr_t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let l = landc_get_mutable cs in
  if l.handshake_packets_outstanding then (
    // Handshake retransmission alarm.
    retransmitAllHandshakePackets cs
  ) else if l.loss_time <> 0L then (
    // Early retransmit or Time Loss Detection
    detectLostPackets cs l.largest_acked_packet
  ) else if U32.lt l.tlp_count kMaxTLPs then (
    // Tail loss probe
    sendOnePacket cs;
    upd_tlp_count (!*cs).landc_state U32.(l.tlp_count +^ 1ul)
  ) else (
    // RTO
    if l.rto_count = 0ul then (
      upd_largest_sent_before_rto (!*cs).landc_state l.largest_sent_packet
    );
    sendTwoPackets cs;
    upd_rto_count (!*cs).landc_state U32.(l.rto_count +^ 1ul)
  );
  setLossDetectionAlarm cs;
  monitorExit (!*cs).monitor;
  pop_frame()

(** If there are ACKs pending in a packet space, allow transmission of an ACK-only packet *)
let setAllowAckOnlyIfNeeded (cs:pointer connection)  (ps:packet_space): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let pss = getPacketSpaceState cs ps in
  if pss.outgoingAckCount <> 0ul then
    upd_sendAckOnlyIfNeeded cs ps true;
  pop_frame()

(** Ping callback, when the ping-timer fires.  This may cause a ping packet to be
    transmitted, to keep the connection alive. *)
let onPingAlarm (ignore1:intptr_t) (cs:pointer connection) (ignore2:intptr_t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  setAllowAckOnlyIfNeeded cs HandshakeSpace;
  setAllowAckOnlyIfNeeded cs ApplicationSpace;
  upd_pingPending (!*cs).csm_state true;
  setHasReadyToSend cs;
  monitorExit (!*cs).monitor;
  pop_frame()

(** Initialize the LossAndCongestion state *)
let makeLossAndCongestion(useTimeLossDetection:bool): ST (pointer lossAndCongestion_mutable)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let max64 = U64.(0UL -^ 1UL) in
  let rt = if useTimeLossDetection then max64 else kReorderingThreshold in
  let trfn = if useTimeLossDetection then kTimeReorderingFractionNumerator else 0L in
  let trfd = if useTimeLossDetection then kTimeReorderingFractionDenominator else 0L in
  let landcm = {
    loss_detection_alarm = nullptr;
    ping_alarm = nullptr;
    
    handshake_count = 0ul;
    tlp_count = 0ul;
    rto_count = 0ul;
    largest_sent_before_rto = 0UL;
    time_of_last_sent_packet = 0L;
    largest_sent_packet = 0UL;
    largest_acked_packet = 0UL;
    latest_rtt = 0L;
    smoothed_rtt = 0L;
    rttvar = 0L;
    reordering_threshold = rt;
    time_reordering_fraction_numerator = trfn;
    time_reordering_fraction_denominator = trfd;
    loss_time = 0L;
    sent_packets = empty_list;
    retransmittable_packets_outstanding = 0ul;
    handshake_packets_outstanding = false;
    bytes_in_flight = 0UL;
    end_of_recovery = 0UL;
    congestion_window = kInitialWindow;
    ssthresh = 0xffffffffffffffffUL;
  } in
  let landcmr = B.malloc HyperStack.root landcm 1ul in
  pop_frame();
  landcmr

(** Second phase of initialization, after the connection object has been initialized. *)
let initializeLossAndCongestion (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let loss_detection_alarm = createTimer cs onLossDetectionAlarm in
  let ping_alarm = createTimer cs onPingAlarm in
  upd_loss_detection_alarm (!*cs).landc_state loss_detection_alarm;
  upd_ping_alarm (!*cs).landc_state ping_alarm;
  pop_frame()
