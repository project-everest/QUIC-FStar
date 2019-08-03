(*

QUIC TLS - the CRYPTO stream implementation

@summary:  CRYPTO frame producer and consumer
*)
module QUICTLS

open FStar
open FStar.HyperStack
open FStar.HyperStack.IO
open FStar.HyperStack.ST
open FStar.Int
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

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module I32 = FStar.Int32
module Cast = FStar.Int.Cast
module B = LowStar.Buffer

let quic_transport_parameter_extension_type = 0xffa5us

(** Kinds of configuration options for quic_transport_parameters *)
type transportParameterId =
     | INITIAL_MAX_STREAM_DATA_BIDI_LOCAL
     | INITIAL_MAX_DATA
     | INITIAL_MAX_BIDI_STREAMS
     | IDLE_TIMEOUT
     | PREFERRED_ADDRESS
     | MAX_PACKET_SIZE
     | STATELESS_RESET_TOKEN
     | ACK_DELAY_EXPONENT
     | INITIAL_MAX_UNI_STREAMS
     | DISABLE_MIGRATION
     | INITIAL_MAX_STREAM_DATA_BIDI_REMOTE
     | INITIAL_MAX_STREAM_DATA_UNI
     | MAX_ACK_DELAY
     | ORIGINAL_CONNECTION_ID

(** Map a transportParameterid to its integer value for encoding purposes *)
let valOfTransportParameterId (id:transportParameterId): Tot U16.t
=
  match id with
     | INITIAL_MAX_STREAM_DATA_BIDI_LOCAL -> 0us
     | INITIAL_MAX_DATA -> 1us
     | INITIAL_MAX_BIDI_STREAMS -> 2us
     | IDLE_TIMEOUT -> 3us
     | PREFERRED_ADDRESS -> 4us
     | MAX_PACKET_SIZE -> 5us
     | STATELESS_RESET_TOKEN -> 6us
     | ACK_DELAY_EXPONENT -> 7us
     | INITIAL_MAX_UNI_STREAMS -> 8us
     | DISABLE_MIGRATION -> 9us
     | INITIAL_MAX_STREAM_DATA_BIDI_REMOTE -> 10us
     | INITIAL_MAX_STREAM_DATA_UNI -> 11us
     | MAX_ACK_DELAY -> 12us
     | ORIGINAL_CONNECTION_ID -> 13us

(** Encode a quic_transport_parameters field, of a 32-bit unsigned integer *)
let encodeTransportParam32 (buf:buffer_t) (off:U32.t) (id:transportParameterId) (v:U32.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let idval = valOfTransportParameterId id in
  let p = append16 buf off idval in
  let p = append16 buf p 4us in
  append32 buf p v

(** Encode a quic_transport_parameters field, of a 16-bit unsigned integer *)
let encodeTransportParam16 (buf:buffer_t) (off:U32.t) (id:transportParameterId) (v:U16.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let idval = valOfTransportParameterId id in
  let p = append16 buf off idval in
  let p = append16 buf p 2us in
  append16 buf p v

(** Encode a quic_transport_parameters field, of a buffer of bytes *)
let encodeTransportParam (buf:buffer_t) (off:U32.t) (id:transportParameterId) (v:buffer_t) (vlen:U16.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  let idval = valOfTransportParameterId id in
  let p = append16 buf off idval in
  let p = append16 buf p vlen in
  appendbytes buf p v (Cast.uint16_to_uint32 vlen)

(** This is called by miTLS when the 0-RTT ticket is available *)
let onTicketReady (cs:pointer connection) (sni:Prims.string) (ticket:pointer mitls_ticket): ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  upd_tls_ticket (!*cs).csm_state ticket;
  pop_frame()

(** Parse one peer paramter from the block.   *)
let parsePeerParameter (cs:pointer connection) (tp_buf:buffer_t) (tp_len:U32.t) (p:U32.t) (pParamBits:pointer U16.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let p = begin  
  id <-- (getu16_s tp_buf tp_len p); // read TransportParameterid
  len <-- (getu16_s tp_buf tp_len U32.(p +^ 2ul)); // read length
  let p = U32.(p+^4ul) in // skip them
  let shiftAmount = if U16.(id <^ 16us) then Cast.uint16_to_uint32 id else 15ul in
  let bit = U16.(1us<<^ shiftAmount) in
  chk1 <-- (if U16.(!*pParamBits &^ bit) <> 0us then fail !$"Peer Parameter specified more than once"  else Ok 0ul);
  pParamBits *= U16.(!*pParamBits |^ bit);
  (match id with
    | 0us -> // INITIAL_MAX_STREAM_DATA_BIDI_LOCAL
        if len <> 4us then fail !$"INITIAL_MAX_STREAM_DATA_BIDI_LOCAL invalid length"
        else (
          v <-- (getu32_s tp_buf tp_len p);
          let max_stream_data = Cast.uint32_to_uint64 v in
          //bugbug: upd_defaultMaxStreamData (!*cs).csm_state max_stream_data;
          return U32.(p+^4ul)
        )
    | 1us -> // INITIAL_MAX_DATA
        if len <> 4us then fail !$"INITIAL_MAX_DATA invalid length"
        else (
          v <-- (getu32_s tp_buf tp_len p);
          let max_data = Cast.uint32_to_uint64 v in
          upd_maxDataPeer (!*cs).csm_state max_data;
          return U32.(p+^4ul)
        )
    | 2us -> // INITIAL_MAX_BIDI_STREAMS
        if len <> 2us then fail !$"INITIAL_MAX_BIDI_STREAMS invalid length"
        else (
          v <-- (getu16_s tp_buf tp_len p);
          let max_id = Cast.uint16_to_uint64 v in
          upd_maxStreamID_BIDIPeer (!*cs).csm_state max_id;
          return U32.(p+^2ul)
        )
    | 3us -> // IDLE_TIMEOUT
        if len <> 2us then fail !$"IDLE_TIMEOUT invalid length"
        else (
          v <-- (getu16_s tp_buf tp_len p);
          // bugbug: implement
          return U32.(p+^2ul)
          )
    | 4us -> // PREFERRED_ADDRESS
        // bugbug: implement.  It has a variable-length PreferredAddress structure
        fail !$"PREFERRED_ADDRESS extension is NYI"
    | 5us -> // MAX_PACKET_SIZE
        if len <> 2us then fail !$"MAX_PACKET_SIZE invalid length"
        else (
          v <-- (getu16_s tp_buf tp_len p);
          // bugbug: ensure this value is >= 1200.
          // bugbug: implement.  It applies only to protected packets
          return U32.(p+^2ul)
          )
    | 6us -> // STATELESS_RESET_TOKEN
        if len <> 16us then fail !$"STATELESS_RESET_TOKEN invalid length"
        else (
          // bugbug: fail if running as a server
          // bugbug: implement support for stateless reset
          return U32.(p+^16ul)
          )
    | 7us -> // ACK_DELAY_EXPONENT
        if len <> 1us then fail !$"ACK_DELAY_EXPONENT invalid length"
        else (
          v <-- (getu8_s tp_buf tp_len p);
          // bugbug: ensure this value is < 20.
          // bugbug: implement
          return U32.(p+^1ul)
          )
    | 8us -> // INITIAL_MAX_UNI_STREAMS
        if len <> 2us then fail !$"ACK_DELAY_EXPONENT invalid length"
        else (
          v <-- (getu16_s tp_buf tp_len p);
          let max_id = Cast.uint16_to_uint64 v in
          upd_maxStreamID_UNIPeer (!*cs).csm_state max_id;
          return U32.(p+^2ul)
          )
    | 9us -> // DISABLE_MIGRATION
        if len <> 0us then fail !$"ACK_DELAY_EXPONENT invalid length"
        else (
          // bugbug: implement
          return p
          )
    | 10us -> // INITIAL_MAX_STREAM_DATA_BIDI_REMOTE
        if len <> 4us then fail !$"INITIAL_MAX_STREAM_DATA_BIDI_REMOTE invalid length"
        else (
          v <-- (getu32_s tp_buf tp_len p);
          let max_stream_data = Cast.uint32_to_uint64 v in
          //bugbug: implement
          return U32.(p+^4ul)
          )
    | 11us -> // INITIAL_MAX_STREAM_DATA_UNI
        if len <> 4us then fail !$"INITIAL_MAX_STREAM_DATA_UNI invalid length"
        else (
          v <-- (getu32_s tp_buf tp_len p);
          let max_stream_data = Cast.uint32_to_uint64 v in
          //bugbug: implement
          return U32.(p+^4ul)
          )
    | 12us -> // MAX_ACK_DELAY
        if len <> 1us then fail !$"MAX_ACK_DELAY invalid length"
        else (
          // bugbug: implement
          return U32.(p+^1ul)
          )
    | 13us -> // ORIGINAL_CONNECTION_ID
       fail !$"ORIGINAL_CONNECTION_ID is NYI"
    | _ -> fail !$"unsupported TransportParameterid"
    )
  end in
  pop_frame();
  p
  

(** Parse a TransportParameters extension and update the local connection
    state with its value *)
let updatePeerParameters (cs:pointer connection) (buf:buffer_t) (len:intptr_t): ST (err bool)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let b = begin
    let len = intptr_t_to_uint32 len in
    quicVersion <-- (getu32_s buf len 0ul);
    p <-- (
      if (!*cs).is_client then (
        versionListSize <-- (getu8_s buf len 4ul); // in bytes, must be a multiple of 4
        let versionListSize = Cast.uint8_to_uint32 versionListSize in
        return U32.(5ul +^ versionListSize) // skip over the list of versions
      ) else (
        return 4ul // start after the quic_version
      )
    );
    tpLength <-- (getu16_s buf len p); // bugbug: validate that this is <= (len-p)
    let p = U32.(p +^ 2ul) in

    let p = B.alloca p 1ul in
    let pParamBits = B.alloca 0us 1ul in (* Bit array of parameters parsed *)
    let pResult = B.alloca (Ok 0ul) 1ul in
    let pKeepGoing = B.alloca true 1ul in
    let inv h = B.live h p in
    let test (): Stack bool (requires inv) (ensures (fun _ _ -> inv)) =
      !*pKeepGoing
    in
    let body() : Stack unit (requires inv) (ensures (fun _ _ -> inv)) =
      pResult *= parsePeerParameter cs buf len (!*p) pParamBits;
      pKeepGoing *= (match !*pResult with
        | Ok newp -> (
            p *= newp;
            U32.(newp <^ len))
        | Fail _ -> false
        )
    in
    C.Loops.while test body;
    !*pResult
  end in
  pop_frame();
  match b with
  | Ok _ -> return true
  | Fail str -> fail str

(* Create a transport_parameters block *)
let createTransportParameters (cs:pointer connection): ST (pointer mitls_extension)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let is_client = (!*cs).is_client in
  let tp = B.malloc HyperStack.root 0uy 256ul in
  (* Write in quic_verion *)
  let p = append32 tp 0ul quicVersion in
  let p = if is_client then
    p
  else ( (* Write out the supported_versions list *)
    let p = append8 tp p 4uy in
    append32 tp p quicVersion
  ) in
  let tpLengthOffset = p in
  let p = U32.(p +^ 2ul) in (* leave space for the 2-byte length to be written later *)
  (* Write in the TransportParameters *)
  let csm = conn_get_mutable cs in
  (* bugbug: if maxDataLocal is > 0xffffffff then send a separate MAX_DATA frame later *)
  let maxDataLocal = minu64 0xffffffffUL csm.maxDataLocal in
  let maxDataLocal32 = Cast.uint64_to_uint32 maxDataLocal in
  let p = encodeTransportParam32 tp p INITIAL_MAX_DATA maxDataLocal32 in
  (* bugbug: if maxStreamID_BIDILocal is > 0xffff then send a separate MAX_ frame later *)
  let maxStreamID_BIDILocal = minu64 0xffffffffUL csm.maxStreamID_BIDILocal in
  let maxStreamID_BIDILocal16 = Cast.uint64_to_uint16 maxStreamID_BIDILocal in
  let p = encodeTransportParam16 tp p INITIAL_MAX_BIDI_STREAMS maxStreamID_BIDILocal16 in
  let maxStreamID_UNILocal = minu64 0xffffffffUL csm.maxStreamID_UNILocal in
  let maxStreamID_UNILocal16 = Cast.uint64_to_uint16 maxStreamID_UNILocal in
  let p = encodeTransportParam16 tp p INITIAL_MAX_UNI_STREAMS maxStreamID_UNILocal16 in
  let p = encodeTransportParam32 tp p INITIAL_MAX_STREAM_DATA_BIDI_LOCAL 0x00100000ul in
  let p = encodeTransportParam32 tp p INITIAL_MAX_STREAM_DATA_BIDI_REMOTE 0x00100000ul in
  let p = encodeTransportParam32 tp p INITIAL_MAX_STREAM_DATA_UNI 0x00100000ul in
  // bugbug: encode more values when they are implemented

  let p = if is_client then
      p
    else (
      upd_defaultMaxStreamData (!*cs).csm_state (Cast.uint32_to_uint64 0x00100000ul);
      encodeTransportParam tp p STATELESS_RESET_TOKEN (!*cs).statelessResetToken 16us
      )
  in

  let tpLen = U32.(p -^ tpLengthOffset -^ 2ul) in
  let _ = append16 tp tpLengthOffset (Cast.uint32_to_uint16 tpLen) in // write in the length of the Transport Parameters
  let exts_local = { ext_type=quic_transport_parameter_extension_type; ext_data=tp; ext_data_len = uint32_to_intptr_t p; } in
  let exts = B.malloc HyperStack.root exts_local 1ul in
  pop_frame();
  exts

(** Callback from miTLS during the handshake *)
let onNegoInternal (cs:pointer connection) (vers:mitls_version) (exts:buffer_t) (exts_len:intptr_t): ST (err mitls_nego_action)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = begin
    chk1 <-- (
      if vers <> TLS_1p3 then
        fail !$"Invalid TLS version"
      else
        return TLS_nego_accept
      );
    chk2 <-- (
      let ptp = B.alloca (null) 1ul in
      let ptp_len = B.alloca (uint32_to_intptr_t 0ul) 1ul in
      let csm = conn_get_mutable cs in
      let r = ffi_mitls_find_custom_extension 1l (* is_server=1 *) exts exts_len quic_transport_parameter_extension_type ptp ptp_len in
      if r = 0l then 
        fail !$"Failed to find the TransportParameters extension"
      else (
        b <-- (updatePeerParameters cs !*ptp !*ptp_len);
        return TLS_nego_accept
        )
      );
      return chk2
  end in
  pop_frame();
  ret

(** Callback from miTLS during negotiation. *)
let onNego (cs:pointer connection) (vers:mitls_version) (exts:buffer_t) (exts_len:intptr_t) (custom_exts:pointer (pointer mitls_extension)) (custom_exts_len: pointer intptr_t) (cookie:pointer buffer_t) (cookie_len:pointer intptr_t): ST mitls_nego_action
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret = onNegoInternal cs vers exts exts_len in
  let csm = conn_get_mutable cs in
  let is_client = (!*cs).is_client in
  let ret =
  match ret with
  | Ok r -> (
    if not is_client then (
      let tp_ext = createTransportParameters cs in
      custom_exts *= tp_ext;
      custom_exts_len *= uint32_to_intptr_t 1ul
    );
    r
    )
  | Fail s -> (
    print_string (csprintf "Nego failed: %XC\n" s);
    TLS_nego_abort
    )
  in
  pop_frame();
  ret
  
(** Initialize miTLS for a connection.  This is separate from initializing the
    connection, to allow clients and servers an opportunity to specify configuration
    options to miTLS. *)
let initializemiTLS (cs:pointer connection): ST bool
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let is_client = (!*cs).is_client in
    
  let exts = createTransportParameters cs in
  let exts_count = if is_client then 1ul else 0ul in  
  let signature_algorithms = if is_client
      then (C.String.of_literal "ECDSA+SHA256:ECDSA+SHA384:ECDSA+SHA512:RSAPSS+SHA256:RSAPSS+SHA384:RSAPSS+SHA512")
      else (C.String.of_literal "RSAPSS+SHA512:RSAPSS+SHA384:RSAPSS+SHA256") in
  let named_groups = if is_client
      then (C.String.of_literal "X25519")
      else (C.String.of_literal  "X25519") in
  let is_server=if is_client then 0l else 1l in
  let hostname = (!*cs).hostname in
  let tkt = csm.tls_ticket in
  let alpns : mitls_alpn = {
    alpn_str = C.String.of_literal "hq-15"; // QUIC-HTTP version 15
    alpn_str_len = uint32_to_intptr_t 5ul;
  } in
  let alpns = B.alloca alpns 1ul in
  let cfg : quic_config = {
    is_server=is_server;

    alpn = alpns;
    alpn_count = uint32_to_intptr_t 1ul;
    cipher_suites = C.String.of_literal "TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256";
    signature_algorithms = signature_algorithms;
    named_groups = named_groups;
    enable_0rtt = 1l;
    
    host_name = hostname;
    server_ticket = tkt;
    exts = exts;
    exts_count = uint32_to_intptr_t exts_count;

    callback_state = cs;
    ticket_callback = onTicketReady;
    nego_callback = onNego;
    cert_callbacks = nullptr;
    
    ticket_enc_alg = nullptr;
    ticket_key = nullptr;
    ticket_key_len = nullptr;
    } in
  let qstate = B.alloca nullptr 1ul in
  let r = ffi_mitls_quic_create qstate cfg in
  let retval =
    if r <> 1l then (
        print_string "FFI_mitls_quic_create failed\n";
        // bugbug: free(connection)
        false
      ) else (
        upd_mitls_state (!*cs).csm_state !*qstate;
        true
      ) in
  pop_frame();
  retval

(** Derive the miTLS/quiccrypto keys for a given miTLS epoch (different than a QUICConnection
      epoch). Returns a reader and a writer key. *)
let getTLSKeys (cs:pointer connection) (mitls_epoch:I32.t) : ST key_pair
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let csm = conn_get_mutable cs in
  let recordKey = B.alloca 0uy U32.(4ul+^32ul+^12ul+^32ul) in (* quic_raw_key *)

  let r = ffi_mitls_quic_get_record_key csm.mitls_state recordKey mitls_epoch quicWriter in
  if r = 0l then failwith (C.String.of_literal "ffi_mitls_quic_get_record_key Write");

  let alg = load32_le recordKey in
  let aead_key = B.offset recordKey 4ul in
  let aead_iv = B.offset recordKey U32.(4ul+^32ul) in
  let pne_key = B.offset recordKey U32.(4ul+^32ul+^12ul) in

  let encrypt_key = B.alloca nullptr 1ul in
  let r = quic_crypto_create encrypt_key alg aead_key aead_iv pne_key in
  if r = 0l then failwith (C.String.of_literal "ffi_quic_crypto_create encrypt");
  
  let r = ffi_mitls_quic_get_record_key csm.mitls_state recordKey mitls_epoch quicReader in
  if r = 0l then failwith (C.String.of_literal "ffi_mitls_quic_get_record_key Read");

  let decrypt_key = B.alloca nullptr 1ul in
  let r = quic_crypto_create decrypt_key alg aead_key aead_iv pne_key in
  if r = 0l then failwith (C.String.of_literal "ffi_quic_crypto_create decrypt");

  let keys = {reader = !*decrypt_key; writer = !*encrypt_key} in
  pop_frame();
  keys

(** Writes the 4-byte protection mask computed by miTLS/quiccrypto into 'mask' *)
let getPacketProtectionMask (mask:buffer_t) (key:quic_key) (packet:buffer_t) (length:U32.t) (pnOffset:U32.t) : ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let sample_length = 16ul in // bugbug: the crypto algorithm changes this, for aes128/256/chachapoly
  let sample_offset = if U32.((pnOffset +^ 4ul +^ sample_length) >^ length) then
    U32.(length -^ sample_length)
  else
    U32.(pnOffset +^ 4ul) in
  let r = quic_crypto_packet_number_otp key (B.offset packet sample_offset) mask in
  if r = 0l then failwith (C.String.of_literal "quic_crypto_packet_number_otp failed!");
  pop_frame()
