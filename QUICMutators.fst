(**

QUIC Mutators - helper functions to mutate data within the QUIC state

@summary - Mutator helper functions
*)
module QUICMutators

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST
open C
open LowStar.Buffer
open LowStar.BufferOps
open QUICTypes

module I64 = FStar.Int64
module I32 = FStar.Int32
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module B = LowStar.Buffer
module Cast = FStar.Int.Cast

module DLL = DoublyLinkedListIface

open HeapOps

//
// quic_stream
//

(** Get a readonly copy of the mutable part of a quic_stream *)
let strm_get_mutable (strm: quic_stream): ST (quic_stream_mutable)
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  let strm' = DLL.node_val strm in
  !*(strm'.qsm_state)

let upd_recvstate (strmm:pointer quic_stream_mutable) (newstate:quic_recv_stream_state): ST unit
   (requires (fun _ -> true)) (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with recvState=newstate }

let upd_sendstate (strmm:pointer quic_stream_mutable) (newstate:quic_send_stream_state): ST unit
   (requires (fun _ -> true)) (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with sendState=newstate }

let upd_segments (strmm:pointer quic_stream_mutable) (v:qstream_segment_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with segments = v }

let upd_readysegments (strmm:pointer quic_stream_mutable) (v:qstream_segment_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with readysegments = v }

let upd_partialsegments (strmm:pointer quic_stream_mutable) (v:qstream_segment_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with partialsegments = v }

let upd_nextReadOffset (strmm:pointer quic_stream_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with nextReadOffset = v }

let upd_maxStreamData (strmm:pointer quic_stream_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with maxStreamData = v }

let upd_nextWriteOffset (strmm:pointer quic_stream_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with nextWriteOffset = v }

let upd_error_code (strmm:pointer quic_stream_mutable) (v:U16.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  strmm *= { !*strmm with error_code = v }

//
// lossAndCongestion
//
(** Get a readonly view of the mutable LossAndCongestion state *)
let landc_get_mutable (cs: pointer connection): ST (lossAndCongestion_mutable)
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  let cs' = !*cs in
  !*(cs'.landc_state)

let upd_handshake_packets_outstanding (lm:pointer lossAndCongestion_mutable) (v:bool): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with handshake_packets_outstanding = v }

let upd_largest_acked_packet (lm:pointer lossAndCongestion_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with largest_acked_packet = v }

let upd_latest_rtt (lm:pointer lossAndCongestion_mutable) (v:I64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with latest_rtt = v }

let upd_smoothed_rtt (lm:pointer lossAndCongestion_mutable) (v:I64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with smoothed_rtt = v }

let upd_rttvar (lm:pointer lossAndCongestion_mutable) (v:I64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with rttvar = v }

let upd_time_of_last_sent_packet (lm:pointer lossAndCongestion_mutable) (v:I64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with time_of_last_sent_packet = v }

let upd_largest_sent_packet (lm:pointer lossAndCongestion_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with largest_sent_packet = v }

let upd_sent_packets (lm:pointer lossAndCongestion_mutable) (v:sentPacket_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with sent_packets = v }

let upd_bytes_in_flight (lm:pointer lossAndCongestion_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with bytes_in_flight = v }

let upd_congestion_window (lm:pointer lossAndCongestion_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with congestion_window = v }

let upd_handshake_count (lm:pointer lossAndCongestion_mutable) (v:U32.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with handshake_count = v }

let upd_tlp_count (lm:pointer lossAndCongestion_mutable) (v:U32.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with tlp_count = v }

let upd_rto_count (lm:pointer lossAndCongestion_mutable) (v:U32.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with rto_count = v }

let upd_loss_time (lm:pointer lossAndCongestion_mutable) (v:I64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with loss_time = v }

let upd_end_of_recovery (lm:pointer lossAndCongestion_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with end_of_recovery = v }

let upd_ssthresh (lm:pointer lossAndCongestion_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with ssthresh = v }

let inc_retransmittable_packets_outstanding (lm:pointer lossAndCongestion_mutable): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  let current = (!*lm).retransmittable_packets_outstanding in
  let inc = U32.(current+^1ul) in
  lm *= { !*lm with retransmittable_packets_outstanding = inc }

let dec_retransmittable_packets_outstanding (lm:pointer lossAndCongestion_mutable): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  let current = (!*lm).retransmittable_packets_outstanding in
  let inc = U32.(current-^1ul) in
  lm *= { !*lm with retransmittable_packets_outstanding = inc }

let upd_loss_detection_alarm (lm:pointer lossAndCongestion_mutable) (v:intptr_t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with loss_detection_alarm = v }

let upd_ping_alarm (lm:pointer lossAndCongestion_mutable) (v:intptr_t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with ping_alarm = v }

let upd_largest_sent_before_rto  (lm:pointer lossAndCongestion_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  lm *= { !*lm with largest_sent_before_rto = v }

//
// connection
//

(** Get a readonly view of the mutable connection state *)
let conn_get_mutable (cs: pointer connection):
  ST (connection_mutable)
    (requires (fun h0 -> B.live h0 cs /\ B.live h0 (cs@h0).csm_state))
    (ensures (fun h0 _ h1 -> h0 == h1)) =
  let cs' = !*cs in
  !*(cs'.csm_state)

let upd_defaultMaxStreamData (csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with defaultMaxStreamData = v }

let upd_maxDataPeer (csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with maxDataPeer = v }

let upd_maxDataLocal (csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with maxDataLocal = v }

(* Update dataSent by adding a value to it. *)
let upd_dataSentAdd (csm:pointer connection_mutable) (v:U32.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  let v64 = Cast.uint32_to_uint64 v in
  let result = U64.( (!*csm).dataSent +^ v64) in
  csm *= { !*csm with dataSent = result }

let upd_dataSentSub(csm:pointer connection_mutable) (v:U32.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  let v64 = Cast.uint32_to_uint64 v in
  let result = U64.( (!*csm).dataSent -^ v64) in
  csm *= { !*csm with dataSent = result }

let upd_dataReceived (csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with dataReceived = v }

let upd_maxStreamID_BIDIPeer (csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with maxStreamID_BIDIPeer = v }

let upd_maxStreamID_UNIPeer (csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with maxStreamID_UNIPeer = v }

let upd_maxStreamID_BIDILocal(csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with maxStreamID_BIDILocal = v }

let upd_maxStreamID_UNILocal (csm:pointer connection_mutable) (v:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with maxStreamID_UNILocal = v }

let upd_mitls_state (csm:pointer connection_mutable) (v:intptr_t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with mitls_state = v }

let upd_cstate (csm:pointer connection_mutable) (v:connection_state): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  csm *= { !*csm with cstate = v }

let upd_streams (csm:pointer connection_mutable) (v:quic_stream_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with streams = v }

let upd_readystreams (csm:pointer connection_mutable) (v:stream_holder_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with readystreams = v }

let upd_shortHeaderPackets (csm:pointer connection_mutable) (v:packet_holder_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with shortHeaderPackets = v }

let upd_dest_connectionID (csm:pointer connection_mutable) (v:connectionid_t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  B.free (!*csm).dest_connectionID.cid;
  csm *= { !*csm with dest_connectionID = v }

let upd_pingPending (csm:pointer connection_mutable) (v:bool): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with pingPending = v }

let upd_app_state (csm:pointer connection_mutable) (v:intptr_t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with app_state = v }

let upd_tls_ticket (csm:pointer connection_mutable) (v:pointer mitls_ticket): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with tls_ticket = v; }

let upd_fixedframes (csm:pointer connection_mutable) (v:fixedframe_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with fixedframes = v; }

let upd_mitls_keys (csm:pointer connection_mutable) (reader:I32.t) (writer:I32.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with mitls_reader_key=reader; mitls_writer_key=writer; }

let upd_epoch (csm:pointer connection_mutable) (v:epoch): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  csm *= { !*csm with epoch = v; }


//
// QUICEngine
//
let upd_connections (eng:pointer engine) (v:connectionholder_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  eng *= { !*eng with connections = v }

let upd_readyconnections (eng:pointer engine) (v:connectionholder_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  eng *= { !*eng with readyconnections = v }

let upd_versionreplies (eng:pointer engine) (v:versionreply_list): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  eng *= { !*eng with versionreplies = v }

//
// Packet spaces
//
let upd_outgoingAckCount (cs:pointer connection) (ps:packet_space) (v:U32.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  let psn = indexOfPacketSpace ps in
  let p = (!*cs).packetSpaces.(psn) in
  (!*cs).packetSpaces.(psn) <- { p with outgoingAckCount = v }

let inc_packetNumber (cs:pointer connection) (ps:packet_space): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true)) =
  let psn = indexOfPacketSpace ps in
  let p = (!*cs).packetSpaces.(psn) in
  let inc = U64.(p.packetNumber+^1UL) in
  (!*cs).packetSpaces.(psn) <- { p with packetNumber = inc }

(** Update the max received packet number with max(v,current) *)
let upd_maxReceivedPacketNumber (cs:pointer connection) (ps:packet_space) (cur:U64.t): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  let psn = indexOfPacketSpace ps in
  let p = (!*cs).packetSpaces.(psn) in
  let oldmax = p.maxReceivedPacketNumber in
  let newmax = if U64.(oldmax >^ cur) then oldmax else cur in
  (!*cs).packetSpaces.(psn) <- { p with maxReceivedPacketNumber = newmax }

let upd_sendAckOnlyIfNeeded (cs:pointer connection) (ps:packet_space) (v:bool): ST unit
   (requires (fun _ -> true))   (ensures (fun _ _ _ -> true))=
  let psn = indexOfPacketSpace ps in
  let p = (!*cs).packetSpaces.(psn) in
  (!*cs).packetSpaces.(psn) <- { p with sendAckOnlyIfNeeded = v }
