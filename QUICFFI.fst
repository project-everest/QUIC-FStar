(**

QUIC FFI - Calls from QUIC code into miTLS, libquiccrypto, or Windows APIs.

@summary:  Make calls into Everest and Windows APIs
*)
module QUICFFI

open FStar
open FStar.HyperStack
open FStar.HyperStack.IO
open FStar.HyperStack.ST
open FStar.Printf
open C
open C.Failure
open C.String
open LowStar.Buffer
open LowStar.BufferOps
open QUICTypes
open QUICUtils
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8  = FStar.UInt8
module I32 = FStar.Int32
module I64 = FStar.Int64
module B = LowStar.Buffer

(** FFI helper - cast an intptr_t to a UInt32.t.  Use with care, as it will truncate the value *)
assume val intptr_t_to_uint32: intptr_t -> U32.t
assume val uint32_to_intptr_t: U32.t -> intptr_t

assume val ffi_mitls_init: unit -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

type pfn_ffi_ticket_cb = (pointer connection -> Prims.string -> pointer mitls_ticket -> ST unit
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true)))

type mitls_version =
  | TLS_SSL3
  | TLS_1p0
  | TLS_1p1
  | TLS_1p2
  | TLS_1p3

type mitls_nego_action =
  | TLS_nego_abort
  | TLS_nego_accept
  | TLS_nego_retry

type mitls_extension = {
  ext_type: U16.t;
  ext_data: pointer U8.t;
  ext_data_len: intptr_t;
}

type pfn_ffi_nego_cb = (pointer connection -> mitls_version -> buffer_t -> intptr_t -> pointer (pointer mitls_extension) -> pointer intptr_t -> pointer buffer_t -> pointer intptr_t -> ST mitls_nego_action
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true)))

type mitls_alpn = {   
  alpn_str: C.String.t;
  alpn_str_len: intptr_t;
}

type quic_config = {
  is_server: I32.t;

  alpn: pointer_or_null mitls_alpn;
  alpn_count: intptr_t;
  cipher_suites: C.String.t;
  signature_algorithms: C.String.t;
  named_groups: C.String.t;
  enable_0rtt: I32.t;

  // only used by the client
  host_name: C.String.t;
  server_ticket: pointer_or_null quic_ticket;
  exts: pointer_or_null mitls_extension;
  exts_count: intptr_t;

  callback_state: pointer connection; // passed back as the first argument of callbacks, may be null
  ticket_callback: pfn_ffi_ticket_cb; // May be null
  nego_callback: pfn_ffi_nego_cb;    // May be null
  cert_callbacks: intptr_t; // bugbug: these are temporarily handled in QUICFStar.c

  // only used by the server
  ticket_enc_alg: intptr_t;
  ticket_key: intptr_t;
  ticket_key_len: intptr_t;
}

//extern int MITLS_CALLCONV FFI_mitls_configure_custom_extensions(/* in */ mitls_state *state, const mitls_extension *exts, size_t exts_count);
assume val ffi_mitls_configure_custom_extensions: intptr_t -> pointer mitls_extension -> intptr_t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

//extern int MITLS_CALLCONV FFI_mitls_find_custom_extension(/*in*/int is_server, const unsigned char *exts, size_t exts_len, uint16_t ext_type, /*out*/ unsigned char **ext_data, /*out*/ size_t *ext_data_len);
assume val ffi_mitls_find_custom_extension: I32.t -> buffer_t -> intptr_t -> U16.t -> pointer (pointer U8.t) -> pointer intptr_t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// extern int MITLS_CALLCONV FFI_mitls_quic_create(/* out */ quic_state **state, quic_config *cfg);
assume val ffi_mitls_quic_create: (pointer intptr_t) ->  quic_config -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// Flags
inline_for_extraction let qflag_complete=0x01us
inline_for_extraction let qflag_application_key=0x02us
inline_for_extraction let qflag_rejected_0rtt=0x10us

type quic_process_ctx = {
  // Inputs
  input: buffer_t; // can be NULL, a TLS message fragment read by QUIC
  input_len: intptr_t;  // Size of input buffer (can be 0)
  output: buffer_t;  // can be NULL, a buffer to store handshake data to send
  
  // Input/Output
  output_len: intptr_t;  // In: size of output buffer (can be 0), Out: bytes written to output
  
  // Outputs:
  tls_error: U16.t; // alert code of a locally-generated TLS alert
  consumed_bytes: intptr_t; // how many bytes of the input have been processed - leftover bytes must be processed in the next call
  to_be_written: intptr_t; // how many bytes are left to write (after writing *output)
  tls_error_desc: intptr_t; // meaningful description of the local error (actually const char*)
  cur_reader_key: I32.t; // current reader epoch, if incremented by TLS, QUIC must switch key BEFORE processing further packets.
  cur_writer_key: I32.t; // current writer epoch, if incremented by TLS, QUIC must switch key AFTER writing *output
  flags: U16.t; // Bitfield of return flags (see above)
}

// extern int MITLS_CALLCONV FFI_mitls_quic_process(/* in */ quic_state *state, /* inout */ quic_process_ctx *ctx);
assume val ffi_mitls_quic_process: intptr_t -> pointer quic_process_ctx -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// extern void MITLS_CALLCONV FFI_mitls_quic_free(/* in */ quic_state *state);
assume val ffi_mitls_quic_free: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
  
// quic_direction enum
let quicWriter = 0ul
let quicReader = 1ul

// extern int MITLS_CALLCONV FFI_mitls_quic_get_record_key(quic_state *state, quic_raw_key *key, int32_t epoch, quic_direction rw);
assume val ffi_mitls_quic_get_record_key: intptr_t -> buffer_t -> I32.t -> U32.t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// extern void MITLS_CALLCONV FFI_mitls_global_free(/*in*/ void* pv);
assume val ffi_mitls_global_free: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

// extern int MITLS_CALLCONV quic_derive_intial_secrets(/*out*/ quic_secret *client_hs, /*out*/ quic_secret *server_hs, const char *con_id, size_t con_id_len, const char *salt, size_t salt_len);
assume val quic_derive_initial_secrets: (pointer UInt8.t) -> (pointer UInt8.t) -> (pointer UInt8.t) -> intptr_t -> (pointer UInt8.t) -> intptr_t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// extern int MITLS_CALLCONV quic_crypto_derive_key(quic_key& key, byte[] secret);
assume val quic_crypto_derive_key: (buffer intptr_t) -> (buffer UInt8.t) -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// int MITLS_CALLCONV quic_crypto_tls_derive_secret(/*out*/ quic_secret *derived, const quic_secret *secret, const char *label);
assume val quic_crypto_tls_derive_secret: (buffer UInt8.t) -> (buffer UInt8.t) -> (C.String.t) -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// extern int MITLS_CALLCONV quic_crypto_encrypt(quic_key key, byte* cipher, uint64 sn, byte* ad, uint32 ad_len, byte* plain, uint32 plain_len);
assume val quic_crypto_encrypt: quic_key -> (buffer UInt8.t) -> U64.t -> (buffer UInt8.t) -> U32.t -> (buffer UInt8.t) -> U32.t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// int MITLS_CALLCONV quic_crypto_decrypt(quic_key *key, /*out*/ unsigned char *plain, uint64_t sn, const unsigned char *ad, uint32_t ad_len, const unsigned char *cipher, uint32_t cipher_len);
assume val quic_crypto_decrypt: quic_key -> (buffer UInt8.t) -> U64.t ->  (buffer UInt8.t) -> U32.t -> (buffer UInt8.t) -> U32.t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

//int MITLS_CALLCONV quic_crypto_create(quic_key **key, mitls_aead alg, const unsigned char *raw_key, const unsigned char *iv, const unsigned char *pne_key);
assume val quic_crypto_create: (buffer quic_key) -> U32.t -> buffer_t -> buffer_t -> buffer_t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

// int MITLS_CALLCONV quic_crypto_packet_number_otp(quic_key *key, const unsigned char *sample, unsigned char *mask);
assume val quic_crypto_packet_number_otp: quic_key -> buffer_t -> buffer_t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun _ _ _ -> true))

inline_for_extraction
let secret_size = U32.(4ul+^4ul+^64ul)

let derive_initial_secrets (con_id:connectionid_t) (is_client:bool): ST key_pair
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let clientSecret = B.alloca 0uy secret_size in
  let serverSecret = B.alloca 0uy secret_size in
  let salt = B.alloca_of_list [
    0x9cuy;0x10uy;0x8fuy;0x98uy;0x52uy;0x0auy;0x5cuy;0x5cuy;0x32uy;0x96uy;0x8euy;0x95uy;0x0euy;0x8auy;0x2cuy;0x5fuy;0xe0uy;0x6duy;0x6cuy;0x38uy
    ] in

  let cil = uint32_to_intptr_t (FStar.Int.Cast.uint8_to_uint32 con_id.cil) in
  let r = quic_derive_initial_secrets clientSecret serverSecret con_id.cid cil salt (uint32_to_intptr_t 20ul) in
  if r = 0l then
    failwith(of_literal "quic_derive_initial_secrets failed\n");
  let encryptKey = B.alloca nullptr 1ul in
  let decryptKey = B.alloca nullptr 1ul in
  let encryptsecret = if is_client then clientSecret else serverSecret in
  let r = quic_crypto_derive_key encryptKey encryptsecret in
  if r = 0l then
    failwith (of_literal "quic_crypto_derive_key encryptKey failed\n");
  let decryptsecret = if is_client then serverSecret else clientSecret in
  let r = quic_crypto_derive_key decryptKey decryptsecret in
  if r = 0l then
    failwith (of_literal "quic_crypto_derive_key decryptKey failed\n");
  let ek = !*encryptKey in
  let dk = !*decryptKey in
  pop_frame();
  {reader=dk; writer=ek}

//HANDLE CreateEvent(_In_ BOOL bManualReset,_In_ BOOL bInitialState)
(** This is implemented in QUICFStar.c and calls CreateEventW with a NULL name and default security*)
assume val createEvent: I32.t -> I32.t -> ST intptr_t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

//void CloseHandle(_In_ HANDLE h)
assume val closeHandle: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Implemented in QUICFStar.c, calls InitializeCriticalsection *)
assume val monitorAlloc: unit -> ST intptr_t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Implemented in QUICFStar.c, calls EnterCriticalsection *)
assume val monitorEnter: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Implemented in QUICFStar.c, calls LeaveCriticalsection *)
assume val monitorExit: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Call Windows WaitForSingleObject, with a timeout in milliseconds *)
assume val waitForSingleObject: intptr_t -> U32.t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Call Windows SetEvent() *)
assume val setEvent: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Call Windows ResetEvent() *)
assume val resetEvent: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Get the system time, in UTC, measured in Windows FILETIME units (10,000ns)
    The absolute value doesn't matter, as all computation is relative. *)
assume val getSystemTime: unit -> ST I64.t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

type comparator = (pointer U64.t -> pointer U64.t -> ST I32.t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))
)

(** Use the CRT qsort() to sort an array of UInt64.t in-place *)
assume val qsort64: (pointer U64.t) -> (U32.t) -> comparator -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Type of a timer callback function.
    First argument is a TP_CALLBACK_INSTANCE, and should be ignored
    Third argument is the PTP_TIMER that fired *)
type timercallback = intptr_t -> (pointer connection) -> intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Create a timer with callback *)
assume val createTimer: (pointer connection) -> timercallback -> ST intptr_t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Set a one-shot timer.  Positive times are absolute, negative are relative, in 100ns ticks *)
assume val setOneShotTimer: intptr_t -> Int64.t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Cancel a timer.  *)
assume val cancelTimer: intptr_t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(** Set a repeating timer, with period specified in milliseconds *)
assume val setRepeatingTimer: intptr_t -> U32.t -> ST unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

assume val from_engine_t: engine_t -> ST (pointer engine)
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

assume val to_engine_t: (pointer engine) -> ST engine_t
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> modifies_none h0 h1))

(* a small cheat - this C function simply calls
   QUICEngine_createServerconnection, allowing QUICStream to call "down"
   into QUICEngine, without support for a forward declaration in F* *)
assume val createServerConnection: (pointer engine) -> connectionid_t -> ST (pointer connection)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
