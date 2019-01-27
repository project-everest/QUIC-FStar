(**

QUIC Connection - the packet-level layer that exchanges messages with a remote peer.

@summary:  Packet-level communication with a remote peer.
*)
module QUICConnection

open FStar
open FStar.HyperStack
open FStar.HyperStack.IO
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.Int
open FStar.Printf
open C
open C.Failure
open C.String
open LowStar.Buffer
open LowStar.BufferOps
open QUICTypes
open QUICMutators
open QUICStream
open QUICFFI
open QUICStream
open QUICFrame
open QUICLossAndCongestion
open QUICUtils
open QUICTLS

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module I64 = FStar.Int64
module Cast = FStar.Int.Cast
module B = LowStar.Buffer

(** Get the writer key for a given epoch. *)
let getEpochWriterKey (cs:pointer connection) (epoch: epoch): ST quic_key
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let e = indexOfEpoch epoch in
  let epoch_keys = (!*cs).keys.(e) in
  let key = epoch_keys.writer in
  pop_frame();
  key

(** Get the reader key for a given epoch *)
let getEpochReaderKey (cs:pointer connection) (epoch: epoch) : ST quic_key
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let e = indexOfEpoch epoch in
  let epoch_keys = (!*cs).keys.(e) in
  let key = epoch_keys.reader in
  pop_frame();
  key

(** Get the appropriate writer key for the connection. *)
let getCurrentWriterKey (cs:pointer connection): ST quic_key
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let e = indexOfEpoch csm.epoch in
  let epoch_keys = (!*cs).keys.(e) in
  let key = epoch_keys.writer in
  pop_frame();
  key

(** Get the appropriate reader key for the connection. *)
let getCurrentReaderKey (cs:pointer connection): ST quic_key
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let e = indexOfEpoch csm.epoch in
  let epoch_keys = (!*cs).keys.(e) in
  let key = epoch_keys.reader in
  pop_frame();
  key

(** Get a partial packet number from the packet, then compute the true number.  The
     buffer contents are modified, starting at 'offset', as the packet number is
     unprotected in-place, allowing for downstream decryption to succeed.
     Returns the 64-bit packet number, and the next read offset, *)
let getPacketNumber (readerkey:quic_key) (buffer:buffer_t) (length:U32.t) (offset:U32.t) (largest_pn:U64.t): ST (err (U64.t * U32.t))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let mask = B.alloca 0uy 4ul in
  getPacketProtectionMask mask readerkey buffer length offset;

  b0 <-- (getu8_s buffer length offset);
  b1 <-- (getu8_s buffer length U32.(offset +^ 1ul));
  b2 <-- (getu8_s buffer length U32.(offset +^ 2ul));
  b3 <-- (getu8_s buffer length U32.(offset +^ 3ul));
  let b0 = U8.(b0 ^^ mask.(0ul)) in // remove Packet Number Protection
  results <-- (
    if U8.(b0 &^ 0x80uy) = 0uy then (
      let nextoffset = U32.(offset+^1ul) in
      B.upd buffer offset b0; // write back the unprotected value
      let truncated_pn = Cast.uint8_to_int64 b0 in
      return (truncated_pn, 7ul, nextoffset)
    ) else if U8.(b0 &^ 0xc0uy) = 0x80uy then (
      let nextoffset = U32.(offset+^2ul) in
      let b1 = U8.(b1 ^^ mask.(1ul)) in // remove Packet Number Protection
      B.upd buffer offset b0; // Write back the unprotected value
      B.upd buffer U32.(offset+^1ul) b1;
      let t16 = getu16 buffer offset in
      let t16 = U16.(t16 &^ 0x3fffus) in
      let truncated_pn = Cast.uint16_to_int64 t16 in
      return (truncated_pn, 14ul, nextoffset)
    ) else (
      let nextoffset = U32.(offset+^4ul) in
      let b1 = U8.(b1 ^^ mask.(1ul)) in // remove Packet Number Protection
      let b2 = U8.(b2 ^^ mask.(2ul)) in // remove Packet Number Protection
      let b3 = U8.(b3 ^^ mask.(3ul)) in // remove Packet Number Protection
      B.upd buffer offset b0; // Write back the unprotected value
      B.upd buffer U32.(offset+^1ul) b1;
      B.upd buffer U32.(offset+^2ul) b2;
      B.upd buffer U32.(offset+^3ul) b3;
      let t32 = getu32 buffer offset in
      let t32 = U32.(t32 &^ 0x3ffffffful) in
      let truncated_pn = Cast.uint32_to_int64 t32 in
      return (truncated_pn, 30ul, nextoffset)
      )
    );
  let truncated_pn,pn_nbits,nextoffset = results in

  let expected_pn_unsigned = U64.(largest_pn +^ 1UL) in
  let expected_pn = Cast.uint64_to_int64 expected_pn_unsigned in
  let pn_win = I64.(1L <<^ pn_nbits) in
  let pn_hwin = I64.(pn_win >>^ 1ul) in
  let pn_mask = I64.(pn_win -^ 1L) in
  let not_pn_mask = I64.lognot pn_mask in
  let candidate_pn = I64.((expected_pn &^ not_pn_mask) |^ truncated_pn) in
  let pn =
    if I64.(candidate_pn <=^ (expected_pn -^ pn_hwin)) then
      I64.(candidate_pn +^ pn_win)
    else if I64.(candidate_pn >^ (expected_pn +^ pn_hwin)) && I64.(candidate_pn >^ pn_win) then
      I64.(candidate_pn -^ pn_win)
    else
      candidate_pn
  in
  let pnUnsigned:U64.t = Cast.int64_to_uint64 pn in
  return (pnUnsigned, nextoffset)

(** Determine the number of bytes needed to encode the packet number *)
let getPacketNumberLength (pn:U64.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  (* bugbug: encode more efficiently by determining the number
     of significant bits required, based on the largest ack'd
     packet number and the current pn *)
  4ul

(** Append the variable-length packet number *)
let appendPacketNumber (b:buffer_t) (offset:U32.t) (pn:U64.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 4))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  (* bugbug: encode more efficiently by determining the number
     of significant bits required, based on the largest ack'd
     packet number and the current pn *)
  let v32 = Cast.uint64_to_uint32 pn in
  let v32 = U32.(v32 |^ 0xc0000000ul) in
  let ret = append32 b offset v32 in
  pop_frame();
  ret

(** Generate a new pseudo-random connection ID of length 8 for the handshake. *)
let generateConnectionID (cil:cil_t): ST connectionid_t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let cil32 = Cast.uint8_to_uint32 cil in
  let cid = B.malloc HyperStack.root 0uy cil32 in
  C.Loops.for 0ul cil32  (fun _ _ -> True) (fun i ->
    let r = C.rand() in
    let b = Cast.int32_to_uint8 r in
    B.upd cid i b
    );
  { cil = cil;
    cid = cid; }

let makeStatelessResetToken(): ST buffer_t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let t = B.malloc HyperStack.root 0uy 16ul in
  C.Loops.for 0ul 16ul (fun _ _ -> True) (fun i ->
    let r = C.rand() in
    t.(i) <- Cast.int32_to_uint8 r
    );
  pop_frame();
  t

(** memcmp() *)
let rec eqb (b1:buffer_t) (b2:buffer_t) (len:U32.t): ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if U32.(len =^ 0ul) then true
  else
    let len' = U32.(len -^ 1ul) in
    if index b1 len' = index b2 len' then
      eqb b1 b2 len'
    else
      false

(** Determine if two connectionid_t instances are equal or not *)
let connectionIDs_equal (c1:connectionid_t) (c2:connectionid_t) : ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if c1.cil <> c2.cil then false
  else eqb c1.cid c2.cid (Cast.uint8_to_uint32 c1.cil)

(** Initialize the state used to manage packet spaces *)
let initializePacketSpaces() : ST (pointer packet_space_state)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let pssInitial: packet_space_state = {
    packetNumber = 0UL;
    numberNotYetAcked = 0UL;
    maxReceivedPacketNumber = 0UL;
    outgoingAcks = B.malloc HyperStack.root 0UL maxoutgoingAcks;
    outgoingAckCount = 0ul;
    sendAckOnlyIfNeeded = false;
    crypto_stream = createStream 0UL 0xffffffffUL;
    } in
  let pss = B.malloc HyperStack.root pssInitial 3ul in
  (* Mutate elements 1 and 2 so their outgoingAcks are separate heap allocations,
     rather than clones of element 0's pointer *)
  let pss1 = {pssInitial with outgoingAcks = B.malloc HyperStack.root 0UL maxoutgoingAcks;
                              crypto_stream = createStream 0UL 0xffffffffUL;  } in
  pss.(1ul) <- pss1;
  let pss2 = {pssInitial with outgoingAcks = B.malloc HyperStack.root 0UL maxoutgoingAcks;
                              crypto_stream = createStream 0UL 0xffffffffUL;  } in
  pss.(2ul) <- pss2;
  pop_frame();
  pss

let copyConnectionID (c:connectionid_t): ST connectionid_t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let cil32 = Cast.uint8_to_uint32 c.cil in
  let cid = B.malloc HyperStack.root 0uy cil32 in
  B.blit c.cid 0ul cid 0ul cil32;
  pop_frame();
  { cil = c.cil; cid = cid; }

(** Create a new 'connection' instance.  The returned pointer is heap-allocated. *)
let initializeConnection (eng:pointer engine) (hostname:C.String.t) (is_client:bool) (true_cid:connectionid_t) (plaintext_cid:connectionid_t): ST (pointer connection)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if is_client && true_cid <> plaintext_cid then failwith (of_literal "Clients must pass the same value for both CIDs");
  let csm:connection_mutable = { cstate = Start;
                                 epoch = EpochInitial;
                                 mitls_reader_key = -1l;
                                 mitls_writer_key = -1l;
                                 app_state = nullptr;
                                 dest_connectionID = true_cid;
                                 mitls_state = nullptr;
                                 defaultMaxStreamData = 0UL;
                                 maxDataPeer = 0UL;
                                 maxStreamID_BIDIPeer = 0UL;
                                 maxStreamID_UNIPeer = 0UL;
                                 maxDataLocal =16777216UL; // 16mb
                                 maxStreamID_BIDILocal = 0x10UL;
                                 maxStreamID_UNILocal = 0x10UL;
                                 maxPayloadSize = U32.(1280ul-^62ul);  // QUIC requires a min MTU of 1280.  Less 62 bytes for UDP IPv6 overhead.  Less for IPv4 (42 bytes)
                                 dataSent = 0UL;
                                 dataReceived = 0UL;
                                 pingPending = false;
                                 streams = empty_list;
                                 readystreams = empty_list;
                                 shortHeaderPackets = empty_list;
                                 tls_ticket = null;
                                 fixedframes = empty_list;
                                 closedReason = (C.String.of_literal "");
                                 } in
  let csmr = B.malloc HyperStack.root csm 1ul in
  let landc = makeLossAndCongestion(false) in
  let statelessResetToken = makeStatelessResetToken() in
  let keysEmpty = { reader=nullptr; writer=nullptr; } in
  let keys = B.malloc HyperStack.root keysEmpty 4ul in
  let keysInitial = derive_initial_secrets plaintext_cid is_client in
  B.upd keys 0ul keysInitial;
  let pss = initializePacketSpaces () in
  let source_ConnectionID = copyConnectionID true_cid in
  let cs:connection = { monitor = monitorAlloc();
                        keys = keys;
                        is_client = is_client;
                        hostname = hostname;
                        landc_state = landc;
                        csm_state = csmr;
                        statelessResetToken = statelessResetToken;
                        handshakeComplete = createEvent 0l 0l;
                        streamDataAvailable = createEvent 1l 0l;
                        eng = to_engine_t eng;
                        source_connectionID = source_ConnectionID;
                        packetSpaces = pss;
    } in
  B.malloc HyperStack.root cs 1ul



(**  Public API:  Initiate the TLS handshake from client to server. *)
let quic_Handshake (cs:pointer connection): ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let csm = conn_get_mutable cs in
  let ret =
    if csm.cstate <> Start then
      false
    else if initializemiTLS cs then (
      upd_handshake_packets_outstanding (!*cs).landc_state true;
      let maxlen = 1300ul in
      let outbuf = B.malloc HyperStack.root 0uy maxlen in

      let outbuf_cur = B.alloca outbuf 1ul in
      let outbuf_cur_length = B.alloca 0ul 1ul in

      C.Loops.do_while
      (fun h break -> live h outbuf /\ (break ==> False))
      (fun _ ->
        let csm = conn_get_mutable cs in
        let output_remaining = U32.(maxlen -^ (!*outbuf_cur_length)) in
        let ctx:quic_process_ctx = {
          input = outbuf; // this argument is ignored.  Just pass a type-correct value.
          input_len = nullptr;
          output = (!*outbuf_cur);
          output_len = (uint32_to_intptr_t output_remaining);
          tls_error = 0us;
          consumed_bytes = nullptr;
          to_be_written = nullptr;
          tls_error_desc = nullptr;
          cur_reader_key = -1l;
          cur_writer_key = -1l;
          flags = 0us;
        } in
        let pctx = B.alloca ctx 1ul in
        let result = ffi_mitls_quic_process (csm.mitls_state) pctx in
        if result = 0l then failwith (of_literal "FFI_mitls_quic_process failed");

        let new_output_len = intptr_t_to_uint32 (!*pctx).output_len in
        outbuf_cur_length *= U32.( !*outbuf_cur_length +^ new_output_len);
        outbuf_cur *= B.offset !*outbuf_cur new_output_len;

        let bReadKeyChanged = (!*pctx).cur_reader_key <> csm.mitls_reader_key  in
        let bWriteKeyChanged = (!*pctx).cur_writer_key <> csm.mitls_writer_key in
        let finished = (new_output_len = 0ul) &&
                       (not bReadKeyChanged) &&
                       (not bWriteKeyChanged) in
        upd_mitls_keys (!*cs).csm_state (!*pctx).cur_reader_key (!*pctx).cur_writer_key;
        if bWriteKeyChanged then (
          print_string("Write key changed");
          upd_epoch (!*cs).csm_state Epoch0RTT;
          let keys = getTLSKeys cs (!*pctx).cur_writer_key in
          B.upd (!*cs).keys epochIndex0RTT keys
        );

        finished
        );
      upd_cstate (!*cs).csm_state Running;
      monitorExit (!*cs).monitor;
      let pss = getPacketSpaceState cs InitialSpace in
      sendStream cs pss.crypto_stream outbuf !*outbuf_cur_length false;
      B.free outbuf;

      // Now wait for the handshake to complete...
      waitForSingleObject (!*cs).handshakeComplete 0xfffffffful;

      monitorEnter (!*cs).monitor;
      upd_handshake_packets_outstanding (!*cs).landc_state false;
      monitorExit (!*cs).monitor;
      true
    ) else (
      monitorExit (!*cs).monitor;
      false
    ) in
  pop_frame();
  ret

let appendConnectionID (packet:buffer_t) (p:U32.t) (cid:connectionid_t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if cid.cil = 0uy then
    p
  else
    appendbytes packet p cid.cid (Cast.uint8_to_uint32 cid.cil)

let protectPacketNumber (cs:pointer connection) (epoch:epoch) (packet:buffer_t) (length:U32.t) (pnOffset:U32.t) (pnLength:U32.t) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let mask = B.alloca 0uy 4ul in
  let key = getEpochWriterKey cs epoch in
  getPacketProtectionMask mask key packet length pnOffset;
  C.Loops.for 0ul pnLength (fun h1 i -> true) (fun i ->
    let pb = B.offset packet U32.(pnOffset +^ i) in
    let pm = B.offset mask i in
    pb *= U8.( (!*pb) ^^ (!*pm))
  );
  pop_frame()

let unprotectPacketNumber (cs:pointer connection) (epoch:epoch) (packet:buffer_t) (length:U32.t) (pnOffset:U32.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let mask = B.alloca 0uy 4ul in
  let key = getEpochWriterKey cs epoch in
  getPacketProtectionMask mask key packet length pnOffset;
//  C.Loops.for 0ul 4ul (fun h1 i -> true) (fun i ->
 //   let pb = B.offset packet U32.(pnOffset +^ i) in
 //   let pm = B.offset mask i in
  //  pb *= U8.( (!*pb) ^^ (!*pm))
  //);
  pop_frame()

(** Prepare a protected packet for transmission *)
let prepareProtected (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let lrlist:lossRecoveryTracker_list = empty_list in
  let csm = conn_get_mutable cs in
  let pss = getPacketSpaceState cs ApplicationSpace in
  if hasMoreToSend pss.crypto_stream then failwith (of_literal "Unexpected CRYPTO frame in ApplicationSpace");
  let p = append8 packet 0ul 0x70uy in // 0/K=1/1/1/0/R=0/R=0/R=0
  let p = appendConnectionID packet p csm.dest_connectionID in
  let pnOffset = p in
  let pnLength = getPacketNumberLength pss.packetNumber in
  let p = appendPacketNumber packet p pss.packetNumber in
  print_string (csprintf "prepareProtected pn=%uL\n" pss.packetNumber);

  (* Now the variable-length part of the header is known, compute how much
     space is available for frames.
   *)
  let plainlength = U32.(packetlen -^ p -^ cleartextHashSize) in
  let plain = B.malloc HyperStack.root 0uy plainlength in
  let plainp,lrlist = prepareAckFrame cs ApplicationSpace plain 0ul plainlength lrlist in
  let ackend = plainp in
  let plainp = if csm.pingPending then (
    upd_pingPending (!*cs).csm_state false;
    preparePingFrame plain plainlength plainp
    ) else plainp
    in
  let plainp,lrlist = if not (is_null csm.fixedframes.lhead) then (
      let ppff = B.alloca csm.fixedframes.lhead 1ul in
      let pplainp = B.alloca plainp 1ul in
      let plrlist = B.alloca lrlist 1ul in
      C.Loops.do_while
      (fun h break -> live h ppff /\ (break ==> False))
      (fun _ ->
        let pff = (!*ppff) in
        let plainp,lrlist = prepareFixedFrame cs plain plainlength (!*pplainp) (!*plrlist) pff in
        pplainp *= plainp;
        plrlist *= lrlist;
        let next = (!*pff).flink in
        B.free pff;
        ppff *= next;
        is_null next // loop while !is_null next
      );
      upd_fixedframes (!*cs).csm_state empty_list;
      (!*pplainp, !*plrlist)
    ) else (
      (plainp, lrlist)
    ) in
  let str = findReadyStream cs in
  let plainp,lrlist = if not (is_null str) then (
      prepareStreamFrame cs str plain plainlength plainp lrlist
    ) else (
      (plainp, lrlist)
    ) in
  // encrypt
  let cipher = B.offset packet p in
  let key = getCurrentWriterKey cs in
  let result = quic_crypto_encrypt key cipher pss.packetNumber packet p plain plainp in
  B.free plain;
  if result = 0l then failwith (of_literal "quic_crypto_encrypt failure in PrepareProtected");
  let length = U32.(p +^ plainp +^ cleartextHashSize) in
  protectPacketNumber cs Epoch1RTT packet length pnOffset pnLength;
  let tracked_packet_length = if plainp = ackend then 0ul else length in
  onPacketSent cs ApplicationSpace pss.packetNumber tracked_packet_length lrlist;
  inc_packetNumber cs ApplicationSpace;
  pop_frame();
  length

(** Protect a long-header packet *)
let protectLongHeaderPacket (cs:pointer connection) (sn:U64.t) (epoch:epoch) (packet:buffer_t) (packetlen:U32.t) (headerlen:U32.t) (payload:buffer_t) (payloadlen:U32.t) : ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let key = getEpochWriterKey cs epoch in
  let r = quic_crypto_encrypt key (B.offset packet headerlen) sn packet headerlen payload payloadlen in
  if r = 0l then failwith (of_literal "quic_crypto_encrypt failed\n");
  pop_frame();
  U32.(headerlen+^payloadlen+^cleartextHashSize)

(** Unprotect a long-header packet *)
let unprotectLongHeaderPacket (decryptkey:quic_key) (packetnumber:U64.t) (packet:buffer_t) (packetlen:U32.t) (headerlen:U32.t) (plain:buffer_t) (maxplainlen:U32.t) : ST (err U32.t)
   (requires (fun _ -> (U32.v packetlen >= 23)))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let payloadlen = U32.(packetlen -^ headerlen -^ cleartextHashSize) in
  let r = quic_crypto_decrypt decryptkey
                              plain       // plain, to write into
                              packetnumber  // sn
                              packet headerlen   // ad and ad_len
                              (B.offset packet headerlen) U32.(packetlen-^headerlen) in
  let ret =
    if r = 0l then
      fail !$"quic_crypto_decrypt_failed (long header)"
    else
      return payloadlen
  in
  pop_frame();
  ret

(** Get the wire format of a connection ID length *)
let getCIL (cid:connectionid_t): U8.t
=
  if cid.cil = 0uy then
    0uy
  else
    U8.(cid.cil -^ 3uy)

(** Append a token length and token *)
let appendToken (b:buffer_t) (offset:U32.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 1))))
   (ensures (fun _ _ _ -> true))
=
  // bugbug: implement tokens
  appendvar b offset 0UL

(** Prepare an Initial packet for transmission *)
let prepareInitial (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let pss = getPacketSpaceState cs InitialSpace in

  // Prepare the header
  let h = append8  packet 0ul 0xffuy in // Long-form | Initial
  let h = append32 packet h quicVersion in // Copy in 4-byte Version
  let dcil = getCIL csm.dest_connectionID in
  let scil = getCIL (!*cs).source_connectionID in
  let h = append8 packet h U8.( (dcil <<^ 4ul) |^ scil) in // DCIL/SCIL byte
  let h = appendConnectionID packet h csm.dest_connectionID in // Copy in destination ConnectionID
  let h = appendConnectionID packet h (!*cs).source_connectionID in // Copy in source ConnectionID
  let h = appendToken packet h in
  let pnLength = getPacketNumberLength pss.packetNumber in
  // Now the variable-length part of the header is known, compute how much
  // space is available for the handshake itself.
  print_string (sprintf "prepareInitial pn=%uL\n" pss.packetNumber);

  let plainlength = U32.(packetlen -^ h -^ cleartextHashSize) in
  let plain = B.malloc HyperStack.root 0uy plainlength in

  // Produce a CRYPTO frame
  let lrlist:lossRecoveryTracker_list = empty_list in
  let (segmentOffset, plainp, lrlist) = prepareCryptoFrame pss.crypto_stream plain plainlength 0ul lrlist in
  let plainp,lrlist = if ((!*cs).is_client && segmentOffset = 0UL) then (
    // Sending the first Initial packet, containing ClientHello.
    let packetOverhead = U32.(h +^ pnLength +^ cleartextHashSize) in
    // The UDP packet body must be at least 1200 bytes.
    if U32.((plainp +^ packetOverhead) <^ 1200ul) then
      // The remainder of the bytes, up to the end, are 0, which are PADDING frames.  Handy!
      // bugbug: if there is 0-RTT data, this packet can be abbreviated, to make space
      //         for a 0-RTT packet inside this same UDP packet.
      (U32.(1200ul -^ packetOverhead), lrlist)
    else
      (plainp, lrlist)
  ) else (
    // Either server preparing for client, or client preparing something other than the first Initial packet
    if not (is_null csm.fixedframes.lhead) then (
      let ppff = B.alloca csm.fixedframes.lhead 1ul in
      let pplainp = B.alloca plainp 1ul in
      let plrlist = B.alloca lrlist 1ul in
      C.Loops.do_while
      (fun h break -> live h ppff /\ (break ==> False))
      (fun _ ->
        let pff = (!*ppff) in
        let plainp,lrlist = prepareFixedFrame cs plain plainlength (!*pplainp) (!*plrlist) pff in
        pplainp *= plainp;
        plrlist *= lrlist;
        let next = (!*pff).flink in
        B.free pff;
        ppff *= next;
        is_null next // loop while !is_null next
      );
      upd_fixedframes (!*cs).csm_state empty_list;
      (!*pplainp, !*plrlist)
    ) else (
      (plainp, lrlist)
    )
  ) in

  let length = U32.(plainp +^ pnLength +^ cleartextHashSize) in // value to write into the header's Length field
  let h = appendvar packet h (Cast.uint32_to_uint64 length) in
  let pnOffset = h in
  let headerlen = appendPacketNumber packet h pss.packetNumber in

  let length = protectLongHeaderPacket cs pss.packetNumber EpochInitial packet packetlen headerlen plain plainp in
  B.free plain;
  protectPacketNumber cs EpochInitial packet length pnOffset pnLength;
  onPacketSent cs InitialSpace pss.packetNumber length lrlist;
  inc_packetNumber cs InitialSpace;
  pop_frame();
  length

(** Prepare a Handshake packet for transmission *)
let prepareHandshake (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  // bugbug: this only bundles one CRYPTO segment at a time into a packet.  it should
  //         do alot more, to reduce the number of transmitted packets.
  push_frame();
  let lrlist:lossRecoveryTracker_list = empty_list in
  let csm = conn_get_mutable cs in
  let pss = getPacketSpaceState cs HandshakeSpace in
  
  // Fill in the variable-length long header
  let h = append8 packet 0ul 0xfduy in // Long-form | Handshake
  let h = append32 packet h quicVersion in // Copy in 4-byte Version
  let dcil = getCIL csm.dest_connectionID in
  let scil = getCIL (!*cs).source_connectionID in
  let h = append8 packet h U8.( (dcil <<^ 4ul) |^ scil) in // DCIL/SCIL byte
  let h = appendConnectionID packet h csm.dest_connectionID in // Copy in destination ConnectionID
  let h = appendConnectionID packet h (!*cs).source_connectionID in // Copy in source ConnectionID
  let pnLength = getPacketNumberLength pss.packetNumber in
  let payloadlength = U32.(csm.maxPayloadSize-^h-^2ul-^pnLength-^cleartextHashSize) in  // The packet may be this long (account for the 2-byte payload length and packet# length)
  let payload = B.malloc HyperStack.root 0uy payloadlength in
  print_string (sprintf "prepareHandshake pn=%uL\n" pss.packetNumber);

  // Allowable frames are CRYPTO, ACK, PADDING, CONNECTION_CLOSE and APPLICATION_CLOSE only.

  let p,lrlist = prepareAckFrame cs HandshakeSpace payload 0ul payloadlength lrlist in
  let ackend = p in

  let segment_offset,payloadlength,lrlist =
    if hasMoreToSend pss.crypto_stream then
      prepareCryptoFrame pss.crypto_stream payload payloadlength p lrlist
    else
      (1UL,p,lrlist)
    in

  let length = U32.(payloadlength +^ pnLength +^ cleartextHashSize) in
  let h = appendvar packet h (Cast.uint32_to_uint64 length) in
  let pnOffset = h in
  let headerlen = appendPacketNumber packet h pss.packetNumber in // Copy in Packet Number

  let length = protectLongHeaderPacket cs pss.packetNumber EpochHandshake packet packetlen headerlen payload payloadlength in
  B.free payload;
  protectPacketNumber cs EpochHandshake packet length pnOffset pnLength;
  let tracked_packet_length = if payloadlength = ackend then 0ul else length in
  onPacketSent cs HandshakeSpace pss.packetNumber tracked_packet_length lrlist;
  inc_packetNumber cs HandshakeSpace;
  pop_frame();
  length

(**  Prepare a new packet for transmission.  The packet is an OUT buffer of
     length packetlen.  The return value is the number of bytes of data present in then
     packet buffer. The cs monitor must be owned by the caller.  *)
let preparePacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let result = (
    match connectionHasMoreToSend cs with
    | None -> 0ul
    | Some InitialSpace -> prepareInitial cs packet packetlen
    | Some HandshakeSpace -> prepareHandshake cs packet packetlen
    | Some ApplicationSpace -> prepareProtected cs packet packetlen
  ) in
  if connectionHasMoreToSend cs <> None then
    setHasReadyToSend cs;
  pop_frame();
  result

(** Read the DCIL value out of a long-header packet (decoded into an actual byte length) *)
let get_dcil (packet:buffer_t) (packetlen:U32.t): ST (err cil_t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  dcil_scil <-- (getu8_s packet packetlen 5ul);
  let dcil = U8.((dcil_scil >>^ 4ul) &^ 0x0fuy) in
  let dcil = if dcil=0uy then 0uy else U8.(dcil+^3uy) in
  pop_frame();
  return dcil

(** Read the DCIL value out of a long-header packet (decoded into an actual byte length) *)
let get_dcil_scil (packet:buffer_t) (packetlen:U32.t): ST (err (cil_t * cil_t))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  dcil_scil <-- (getu8_s packet packetlen 5ul);
  let dcil = U8.((dcil_scil >>^ 4ul) &^ 0x0fuy) in
  let dcil = if dcil=0uy then 0uy else U8.(dcil+^3uy) in
  let scil = U8.(dcil_scil &^ 0x0fuy) in
  let scil = if scil=0uy then 0uy else U8.(scil+^3uy) in
  pop_frame();
  return (dcil, scil)

(** Parse a connectionID from the packet *)
let getConnectionID (packet:buffer_t) (packetlen:U32.t) (p:U32.t) (cil:cil_t): ST (err connectionid_t)
   (requires (fun _ -> (UInt32.v packetlen >= 13)))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let cil32 = Cast.uint8_to_uint32 cil in
  let cid = B.malloc HyperStack.root 0uy cil32 in
  res <-- (getbytes_s packet packetlen p cid cil32);
  pop_frame();
  let connectionID = { cil = cil; cid = cid; } in
  return connectionID

(** Destructor for a connectionid_t *)
let deleteConnectionID (cid:connectionid_t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  B.free cid.cid

(** workaround for F* 1319 - Incompatible version for unification variable
  getpayloadlen should end with "return (payloadlen32, p)" but F* errors out
  due to the above bug.  This makepair helper is a temporary workaround.
*)
inline_for_extraction
let makepair (p:U32.t) (q:U32.t) : (U32.t * U32.t)
=
  (p, q)

(** Read and validate Payload Length from an untrusted buffer *)
let getpayloadlen (b:buffer_t) (length:U32.t) (offset:U32.t): ST (err (U32.t * U32.t))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  payloadlen_p <-- (getvar_s b length offset);
  let payloadlen,p = payloadlen_p in
  if U64.(payloadlen >^ 65535UL) then // avoid integer overflow risk below
    fail !$"Invalid payload length"
  else (
    let payloadlen32 = Cast.uint64_to_uint32 payloadlen in
    if U32.(p +^ payloadlen32 >^ length) then
      fail !$"Invalid payload length"
    else (
      return (makepair payloadlen32 p)
      )
  )

(** Process a received Initial packet *)
let processInitial (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> (UInt32.v packetlen >= 13)))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    dcil_scil <-- (get_dcil_scil packet packetlen);
    let dcil,scil = dcil_scil in
    let p = 6ul in (* skip packet type, version number, dcil/scil bytes *)
    dest_connectionID <-- (getConnectionID packet packetlen p dcil);
    let p = U32.(p +^ (Cast.uint8_to_uint32 dcil)) in
    //this is ignored, so don't bother fetching it:  
    //  source_connectionID <-- (getConnectionID packet packetlen p scil);
    let p = U32.(p +^ (Cast.uint8_to_uint32 scil)) in
    tokenlength_p <-- (getvar_s packet packetlen p);
    let tokenlength,p = tokenlength_p in
    // bugbug: validate tokenlength and capture the token itself
    let p = U32.(p +^ (Cast.uint64_to_uint32 tokenlength)) in
    length_p <-- (getpayloadlen packet packetlen p);
    let length,p = length_p in
    packetlen <-- ( (* Reduce packetlen down to the true packet length *)
      if U32.((length +^ p) >^ packetlen) then
        fail !$"Packet length is too large"
      else
        return U32.(length +^ p)
    );
    let key = getEpochReaderKey cs EpochInitial in
    let pnOffset = p in
    pn_p <-- (
      // bugbug: pass expected largest_pn value instead of 0 here
      getPacketNumber key packet packetlen p 0UL
      );
    let packetNumber,p = pn_p in
    let pnLength = U32.(p -^ pnOffset) in
    let headerlen = p in
    print_string (sprintf "processInitial pn=%uL\n" packetNumber);
    plainlen <-- (
      if U32.(length <^ (pnLength +^ cleartextHashSize)) then
        fail !$"Packet length is too small"
      else
        return U32.(length -^ pnLength -^ cleartextHashSize)
    );
    let plain = B.malloc HyperStack.root 0uy plainlen in
    plainlen <-- unprotectLongHeaderPacket key packetNumber packet packetlen headerlen plain plainlen;
    offset <-- (
      if (!*cs).is_client then
        upd_dest_connectionID (!*cs).csm_state dest_connectionID // update the ConnectionID with the server's ID
      else
        deleteConnectionID dest_connectionID;
      processInitialFrames cs plain 0ul plainlen
      );
    B.free plain;
    registerAck cs InitialSpace packetNumber;
    upd_maxReceivedPacketNumber cs InitialSpace packetNumber;
    return U32.(headerlen +^ offset +^ cleartextHashSize)
  end in
  pop_frame();
  ret

(** Process a received Handshake packet *)
let processHandshake (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> (UInt32.v packetlen >= 13)))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    dcil_scil <-- (get_dcil_scil packet packetlen);
    let dcil,scil = dcil_scil in
    let p = 6ul in (* skip packet type, version number, dcil/scil bytes *)
    //not needed:  dest_connectionID <-- (getConnectionID packet packetlen p dcil);
    let p = U32.(p +^ (Cast.uint8_to_uint32 dcil)) in
    //not needed:  source_connectionID <-- (getConnectionID packet packetlen p scil);
    let p = U32.(p +^ (Cast.uint8_to_uint32 scil)) in
    length_p <-- (getpayloadlen packet packetlen p);
    let length,p = length_p in
    packetlen <-- ( (* Reduce packetlen down to the true packet length *)
      if U32.((length +^ p) >^ packetlen) then
        fail !$"Packet length is too large"
      else
        return U32.(length +^ p)
    );
    let key = getEpochReaderKey cs EpochHandshake in
    let pnOffset = p in
    pn_p <-- (
      // bugbug: pass expected largest_pn value instead of 0 here
      getPacketNumber key packet packetlen p 0UL
      );
    let packetNumber,p = pn_p in
    let pnLength = U32.(p -^ pnOffset) in
    let headerlen = p in
    print_string (sprintf "processHandshake pn=%uL\n" packetNumber);
    plainlen <-- (
      if U32.(length <^ (pnLength +^ cleartextHashSize)) then
        fail !$"Packet length is too small"
      else
        return U32.(length -^ pnLength -^ cleartextHashSize)
    );
    let plain = B.malloc HyperStack.root 0uy length in
    plainlen <-- unprotectLongHeaderPacket key packetNumber packet packetlen headerlen plain plainlen;
    offset <-- (
      processHandshakeFrames cs plain 0ul plainlen
      );
    B.free plain;
    registerAck cs HandshakeSpace packetNumber;
    upd_maxReceivedPacketNumber cs HandshakeSpace packetNumber;
    return U32.(headerlen +^ offset +^ cleartextHashSize)
  end in
  pop_frame();
  ret

(** respond to a client's request for version nego by queuing a nego packet for transmission *)
let negotiateVersion (eng:pointer engine) (cid:connectionid_t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "negotiateVersion\n";
  let appstate = (!*eng).newconnection (!*eng).newconnection_state null in
  let v = { replyid=cid; replyapp_state=appstate } in
  let p = B.malloc HyperStack.root (empty_entry v) 1ul in
  monitorEnter (!*eng).emonitor;
  let list = insertTailList (!*eng).versionreplies p in
  upd_versionreplies eng list;
  setEvent (!*eng).dataReadyToSend;
  monitorExit (!*eng).emonitor;
  pop_frame()

let prepareNegotiationPacket (cid:connectionid_t) (packet:buffer_t) (packetlen:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "prepareNegotiationpacket\n";
  let p = append8 packet 0ul 0x80uy in // top bit must be 1, other bits are selected randomly by the server
  let p = append32 packet p 0ul in // append Version hard-coded to 0
  let cil = getCIL cid in
  let p = append8 packet p U8.( (cil <<^ 4ul) |^ cil) in // DCIL/SCIL byte
  let p = appendConnectionID packet p cid in // Copy in the source cid as destination
  let p = appendConnectionID packet p cid in // Copy in the source cid as source also
  let p = append32 packet p 0x0a0a0a7aul in // append a test version value
  let p = append32 packet p quicVersion in // append our supported version
  pop_frame();
  p


(** Process an Initial sent from a client to a server *)
let processClientInitial (eng:pointer engine) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "processClientInitial\n";
  let ret = begin
    if U32.(packetlen <^ 1200ul) then
      fail !$"Initial packet must be at least 1200 bytes long"
    else (
      // The fixed fields can be safely read without bounds-check due to the packetlen check above
      let version = getu32 packet 1ul in
      dcil_scil <-- (get_dcil_scil packet packetlen);
      let dcil,scil = dcil_scil in
      let p = 6ul in
      // not needed: dest_connectionID <-- (getConnectionID packet packetlen p dcil);
      let p = U32.(p +^ (Cast.uint8_to_uint32 dcil)) in
      source_connectionID <-- (getConnectionID packet packetlen p scil);
      let p = U32.(p +^ (Cast.uint8_to_uint32 scil)) in
      tokenlength_p <-- (getvar_s packet packetlen p);
      let tokenlength,p = tokenlength_p in
      // bugbug: validate tokenlength and capture the token itself
      let p = U32.(p +^ (Cast.uint64_to_uint32 tokenlength)) in
      length_p <-- (getpayloadlen packet packetlen p);
      let length,p = length_p in
      let keysInitial = derive_initial_secrets source_connectionID false in
      let pnOffset = p in
      pn_pnLength_p <-- (
        let key = keysInitial.reader in
        getPacketNumber key packet packetlen p 0xffffffffffffffffUL
        );
      let pn,p = pn_pnLength_p in
      let pnLength = U32.(p -^ pnOffset) in
      let headerlen = p in

      if version <> quicVersion then (
        // Respond with version negotiation packet
        negotiateVersion eng source_connectionID;
        return 0ul
      ) else (
        plainlen <-- (
           if U32.(length <^ (pnLength +^ cleartextHashSize)) then
            fail !$"Packet length is too small"
          else
            return U32.(length -^ pnLength -^ cleartextHashSize)
         );
        let plain = B.malloc HyperStack.root 0uy plainlen in
        plainlen <-- (unprotectLongHeaderPacket keysInitial.reader pn packet packetlen headerlen plain plainlen);
        let r = processClientInitialFrames eng plain plainlen source_connectionID pn in
        B.free plain;
        deleteConnectionID source_connectionID;
        match r with
        | Ok offset -> return U32.(offset +^ cleartextHashSize)
        | Fail m -> fail m
      )
    )
  end in
  pop_frame();
  ret

(** Process a Version Negotation packet *)
let processVersionNegotiation (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> (UInt32.v packetlen >= 6))) // connectionFromHeader ensures the long header is present
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "Received Version Negotation Packet:\n";
  dcil_scil <-- (get_dcil_scil packet packetlen);
  let dcil,scil = dcil_scil in
  let p = 6ul in (* skip packet type, version number, dcil/scil bytes *)
  //not needed: dest_connectionID <-- (getConnectionID packet packetlen p dcil);
  let p = U32.(p +^ (Cast.uint8_to_uint32 dcil)) in
  //not needed: source_connectionID <-- (getConnectionID packet packetlen p scil);
  let p = U32.(p +^ (Cast.uint8_to_uint32 scil)) in
  let pp = B.alloca p 1ul in
  let inv h = B.live h pp in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    U32.( !*pp <^ packetlen)
  in
  let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    let supportedVersion = getu32 packet !*pp in
    print_string (sprintf "  Supported version: %ul\n" supportedVersion);
    pp *= U32.( !*pp +^ 4ul)
  in
  C.Loops.while test body;
  pop_frame();
  fail !$"Unsupported QUIC version from the peer"

(** Process a received long-header packet *)
let processLongHeaderPacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> (UInt32.v packetlen >= 6))) // connectionFromHeader ensures the long header is present
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let r = begin
    version <-- (
      let v = getu32 packet 1ul in
      if v = quicVersion then
        return v
      else if v = 0ul then
        processVersionNegotiation cs packet packetlen
      else
        // v=0ul should have been handled by processClientInitial, for the handshake.
        // connection resumption might mean we have to renegotiate version here too.
        fail !$"Unexpected QUIC version"
    );
    chk1 <-- (
      match !*packet with
      | 0xffuy -> processInitial cs packet packetlen // Initial
      | 0xfeuy -> fail !$"Unsupported - Retry" // Retry
      | 0xfduy -> processHandshake cs packet packetlen // Handshake
      | 0xfcuy -> fail !$"Unsupported - 0-RTT Protected" // 0-RTT Protected
      | _ -> fail !$"Unsupported long header type"
    );
    return chk1
  end in
  pop_frame();
  r

(** Process a received short-header packet.  This may be called only after the 1RTT keys
    have arrived. *)
let processShortHeaderPacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> (U32.v packetlen >= 1)))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
  let csm = conn_get_mutable cs in
  let first = getu8 packet 0ul in
  let k = U8.(first &^ 0x40uy) in // key phase (zero/nonzero)
  let cil = (!*cs).source_connectionID.cil in
  let cil32 = Cast.uint8_to_uint32 cil in
  let p = U32.(1ul +^ cil32) in // Skip past the dest Connection ID, which has already been handled
  packetnumber_p <-- (
    let key = getEpochReaderKey cs Epoch1RTT in
    // bugbug: pass largest PN here instead of 0:
    getPacketNumber key packet packetlen p 0UL
    );
  let packetnumber, p = packetnumber_p in
  print_string (sprintf "processShortHeaderPacket pn=%uL\n" packetnumber);
  // protected payload follows
  let plainlength = U32.(packetlen-^p-^cleartextHashSize) in
  let plain = B.malloc HyperStack.root 0uy plainlength in
  let cipher = B.offset packet p in
  let cipherlength = U32.(packetlen-^p) in
  chk1 <-- (
    let key = getCurrentReaderKey cs in
    let result = quic_crypto_decrypt key plain packetnumber packet p cipher cipherlength in
    if result = 0l then fail !$"quic_crypto_decrypt failed (short header)" else return true
  );
  chk2 <-- (
    let r = processProtectedFrames cs plain 0ul plainlength in
    B.free plain;
    r
  );
  registerAck cs ApplicationSpace packetnumber;
  upd_maxReceivedPacketNumber cs ApplicationSpace packetnumber;
  return 0ul
  end in
  pop_frame();
  ret

(** 1RTT key is available, so the short-header packets can now be
     processed.  Do that now. *)
let catchUpWithShortHeaderPackets (cs:pointer connection) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let key = getCurrentReaderKey cs in
  let keys = B.index (!*cs).keys epochIndex1RTT in
  let key = keys.reader in
  let shortHeaderPackets = (!*((!*cs).csm_state)).shortHeaderPackets in
  if (key <> nullptr) && (not (is_null shortHeaderPackets.lhead)) then (
    print_string "Catching up with buffered key1 packets\n";
    upd_shortHeaderPackets (!*cs).csm_state empty_list;
    let packet = B.alloca shortHeaderPackets.lhead 1ul in
    C.Loops.do_while
      (fun h break -> live h packet /\ (break ==> False))
      (fun _ ->
        let pkt = !*packet in
        let result = processShortHeaderPacket cs (!*pkt).p.packet (!*pkt).p.packetlen in
        B.free (!*pkt).p.packet;
        match result with
        | Ok x -> true
        | Fail s -> print_string (csprintf "Catching up with short header packet Fail: %XC\n" s);
        packet *= (!*pkt).flink;
        let pval = !*packet in
        is_null pval  // do... while !is_null pval
      )
   );
   pop_frame()

(** Determines a connection given a destination connection ID value, or returns NULL
    if there is no match. *)
let connectionFromID (eng:pointer engine) (connectionID:connectionid_t): ST (pointer_or_null connection)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let pcs = B.alloca null 1ul in
  monitorEnter (!*eng).emonitor;
  let head = (!*eng).connections.lhead in
  let pp = B.alloca head 1ul in
  let headisnull = is_null head in
  let pstop = B.alloca headisnull 1ul in
  let inv h = B.live h pp in
  let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
    not !*pstop
  in
  let body (): Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
    let cs = (!*(!*pp)).p in
    let csm = conn_get_mutable cs in
    let found = connectionIDs_equal csm.dest_connectionID connectionID in
    if found then (
      pcs *= cs
      );
    pp *= (!*(!*pp)).flink;
    pstop *= ((is_null !*pp) || found)
  in
  C.Loops.while test body;
  let cs = !*pcs in
  monitorExit (!*eng).emonitor;
  if (is_null cs) then (
    // bugbug: log the connection ID.  It needs a pretty-print helper.
    print_string (sprintf "connectionFromID: connection not found!\n")
  );
  pop_frame();
  cs

(** Read the dest connectionID from a header (long or short form) and either return
    the associated connection pointer, or null if there is no match *)
let connectionFromHeader (eng:pointer engine) (packet:buffer_t) (packetlen:U32.t): ST (err (pointer_or_null connection))
   (requires (fun _ -> (U32.v packetlen >= 1)))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let pcs =
    if (!*eng).eis_client && !*packet = 0xffuy then (
      // Initial received from a server, to a client.  The server's choice of
      // connection ID supercedes ours.
      dcil <-- (get_dcil packet packetlen);
      connectionID <-- (getConnectionID packet packetlen 6ul dcil);
      monitorEnter (!*eng).emonitor;
      let head = (!*eng).connections.lhead in
      monitorExit (!*eng).emonitor;
      let cs = (!*head).p in
      // bugbug: only update this if the packet has the highest-numbered PN seen so far.
      //                  otherwise out-of-order updates may cause a stale CID to be used.
      monitorEnter (!*cs).monitor;
      upd_dest_connectionID (!*cs).csm_state connectionID;
      monitorExit (!*cs).monitor;
      return cs
    ) else (
      if U8.(!*packet &^ 0x80uy) = 0x80uy then ( // long header
        dcil <-- (get_dcil packet packetlen);
        connectionID <-- (getConnectionID packet packetlen 6ul dcil);
        let r = connectionFromID eng connectionID in
        deleteConnectionID connectionID;
        return r
        )
      else ( // short header
        connectionID <-- (getConnectionID packet packetlen 1ul (!*eng).eng_cil);
        let r = connectionFromID eng connectionID in
        deleteConnectionID connectionID;
        return r
      )
    ) in
  pop_frame();
  pcs

let conn_is_closed (cs:pointer connection): ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let csm = conn_get_mutable cs in
  csm.cstate = Closed

(** Process multiple QUIC packets within a single UDP packet.  There can be one or more
     long header packets followed by a single short header packet, all together. *)
let processLongHeaderPackets (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
    push_frame();
    let pp = B.alloca 0ul 1ul in
    let pret = B.alloca (return 0ul) 1ul in
    C.Loops.do_while
    (fun h break -> live h packet /\ (break ==> False))
    (fun _ ->
        let newPacket = B.offset packet !*pp in
        let newPacketLen = U32.(packetlen -^ (!*pp)) in
        if U8.(!*newPacket &^ 0x80uy) = 0uy then
            true // stop looping, as a short packet has been found
        else (
            let ret = processLongHeaderPacket cs newPacket newPacketLen in
            pret *= ret;
            match ret with
            | Ok p -> (
                pret *= return U32.( !*pp +^ p);
                pp *= U32.(p +^ (!*pp));
                U32.( (!*pp) >=^ packetlen)
                )
            | Fail s -> true // Finished
            )
        );
       
    let ret = !*pret in
    pop_frame();
    ret

let processOneShortHeaderPacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
 =
    push_frame();
        let csm = conn_get_mutable cs in
        let keys = B.index (!*cs).keys epochIndex1RTT in
        let key = keys.reader in
        let ret =
          if key = nullptr then (
            print_string "Buffering key1 packet for later\n";
            let packetcopy = B.malloc HyperStack.root 0uy packetlen in
            B.blit packet 0ul packetcopy 0ul packetlen;
            let t:packet_holder_fixed = { packet=packetcopy; packetlen=packetlen} in
            let holder = empty_entry t in
            let pholder = B.malloc HyperStack.root holder 1ul in
            let list = insertTailList csm.shortHeaderPackets pholder in
            upd_shortHeaderPackets (!*cs).csm_state list;
            return 0ul
          ) else (
            processShortHeaderPacket cs packet packetlen
          ) in
      pop_frame();
      ret

(** Public API: Process a received packet.  Returns 0xffffffff if there is an error. *)
let quic_ProcessPacket (eng:pointer engine) (packet:buffer_t) (packetlen:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  print_string "Enter QUIC_ProcessPacket\n";
  let ret =
    if packetlen=0ul then (
      fail !$"0-length packet"
    ) else (
      cs <-- (connectionFromHeader eng packet packetlen);
      if is_null cs then (
        if (not ((!*eng).eis_client)) && !*packet = 0xffuy then (
          // Running as server, and received an Initial.  There is no connection
          // instance for this connection ID.  To reduce impact of DoS attacks, this codepath
          // should be as lightweight, in terms of resource utilization, as possible.
          //bugbug: the client may have grouped multiple long, and up to 1 short packet
          //        inside this UDP packet.  Process them all.
          processClientInitial eng packet packetlen
        ) else
          fail !$"unexpected connectionid in short packet" // bugbug: implement
      ) else if conn_is_closed cs then (
        Ok 0ul // silently drop the packet
      ) else if U8.(!*packet &^ 0x80uy) = 0uy then (  // Short header
        monitorEnter (!*cs).monitor;
        let ret = processOneShortHeaderPacket cs packet packetlen in
        updateReadyToSend cs;
        monitorExit (!*cs).monitor;
        ret
      ) else ( // Long header
        monitorEnter (!*cs).monitor;
        let lhret = processLongHeaderPackets cs packet packetlen in
        let ret = match lhret with
          | Ok p -> if U32.(p <^ packetlen) then
              let sp = B.offset packet p in
              let splen = U32.(packetlen -^ p) in
              processOneShortHeaderPacket cs sp splen
            else
              return p
          | Fail _ -> lhret
        in        
        catchUpWithShortHeaderPackets cs;
        updateReadyToSend cs;
        monitorExit (!*cs).monitor;
        ret
      )
    )
  in
  print_string "Leave QUIC_ProcessPacket\n";
  pop_frame();
  match ret with
  | Ok a -> 0ul
  | Fail s -> (
      print_string (csprintf "Fail: %XC\n" s);
      0xfffffffful
      )

(**  Public API:  Get the associated application state for this connection *)
let quic_GetAppState (cs:pointer connection): ST intptr_t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let app_state = csm.app_state in
  pop_frame();
  app_state

(**  Public API:  Set the associated application state for this connection, returning the previous value *)
let quic_SetAppState (cs:pointer connection) (new_state:intptr_t) : ST intptr_t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let csm = conn_get_mutable cs in
  let old_state = csm.app_state in
  upd_app_state (!*cs).csm_state new_state;
  monitorExit (!*cs).monitor;
  pop_frame();
  old_state

(** Public API: Get the 0-rtt ticket.  This may return null immediately after the
    handshake completes, then later become non-null.  The caller should retry
    periodically until a non-null return value *)
let quic_GetTicket (cs:pointer connection): ST (pointer_or_null mitls_ticket)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let ticket = csm.tls_ticket in
  pop_frame();
  ticket

(** Public API: Set the 0-rtt ticket.  This must be called before quic_Handshake() *)
let quic_SetTicket (cs:pointer connection) (ticket:pointer_or_null mitls_ticket): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  upd_tls_ticket (!*cs).csm_state ticket;
  pop_frame()

let enqueueMaxStreamID (cs:pointer connection) (v:U64.t): ST intptr_t (* a waitable handle *)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let len = 9ul in
  let data = B.malloc HyperStack.root 0uy len in
  let offset = append8 data 0ul 6uy in //  MAX_STREAM_ID
  let offset = appendvar data offset v in
  let hWait = enqueueFixedFrame cs data offset in
  updateReadyToSend cs;
  pop_frame();
  hWait

let enqueueMaxData (cs:pointer connection) (v:U64.t): ST intptr_t (* a waitable handle *)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let len = 9ul in
  let data = B.malloc HyperStack.root 0uy len in
  let offset = append8 data 0ul 4uy in //  MAX_DATA
  let offset = appendvar data offset v in
  let hWait = enqueueFixedFrame cs data offset in
  updateReadyToSend cs;
  pop_frame();
  hWait

(** Public API: Close the connection *)
let quic_CloseConnection (cs:pointer connection): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  enqueueConnectionClose cs 0us; (* close, NO_ERROR *)
  monitorExit (!*cs).monitor;
  pop_frame()

(** Public API:  Set the maximum stream ID.  It supports setting both UNI and BIDI streams.
      If it is called ahead of the handshake, it influences the initial transport_parameters block.
      Otherwise, it sends updated data via frames. *)
let quic_SetMaxStreamID (cs:pointer connection) (maxid:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let csm = conn_get_mutable cs in
  let hWait =
  if isStreamBidi maxid then (
    if U64.(csm.maxStreamID_BIDILocal <^ maxid) then (
      upd_maxStreamID_BIDILocal (!*cs).csm_state maxid;
      if csm.cstate <> Start then (
        enqueueMaxStreamID cs maxid
      ) else nullptr
    ) else nullptr
  ) else (
    if U64.(csm.maxStreamID_UNILocal <^ maxid) then (
      upd_maxStreamID_UNILocal (!*cs).csm_state maxid;
      if csm.cstate <> Start then (
        enqueueMaxStreamID cs maxid
      ) else nullptr
    ) else nullptr
  ) in
  monitorExit (!*cs).monitor;
  if hWait <> nullptr then (
    waitForSingleObject hWait 0xfffffffful;  (* block until the message is ACK'd *)
    closeHandle hWait
  );
  pop_frame()

(** Public API:  Set the maximum data size
      If it is called ahead of the handshake, it influences the initial transport_parameters block.
      Otherwise, it sends updated data via frames. *)
let quic_SetMaxData (cs:pointer connection) (maxdata:U64.t): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*cs).monitor;
  let csm = conn_get_mutable cs in
  let hWait =
  if U64.(csm.maxDataLocal <^ maxdata) then (
    upd_maxDataLocal (!*cs).csm_state maxdata;
    if csm.cstate <> Start then (
      enqueueMaxData cs maxdata
    ) else nullptr
  ) else
    nullptr
  in
  monitorExit (!*cs).monitor;
  if hWait <> nullptr then (
    waitForSingleObject hWait 0xfffffffful; (* block until the message is ACK'd *)
    closeHandle hWait
  );
  pop_frame()
