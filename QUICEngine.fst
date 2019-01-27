(**

QUIC Engine - the top-level API for QUIC clients and servers

@summary:  Top-level QUIC API
*)
module QUICEngine

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
open QUICFFI
open QUICTLS
open QUICLossAndCongestion
open QUICConnection
module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Cast = FStar.Int.Cast
module B = LowStar.Buffer

(**  Public API:  Return the one connection pointer stored inside a client engine instance *)
let quic_GetClient (eng:pointer engine): ST (pointer connection)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret =
    if (!*eng).eis_client then (
      let csh = (!*eng).connections.lhead in
      (!*csh).p
    ) else
      null
  in
  pop_frame();
  ret
  
let initializeEngine (hostname:C.String.t) (is_client:bool) (cb:newConnectionCallback) (cbstate:intptr_t) (cil:cil_t): ST (pointer_or_null engine)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let st = getSystemTime() in
  let seed = Cast.int64_to_uint32 st in
  C.srand seed;
  let e = {
    eis_client=is_client;
    emonitor=monitorAlloc();
    ehostname=hostname;
    connections=empty_list;
    dataReadyToSend=createEvent 1l 0l;
    readyconnections=empty_list;
    versionreplies=empty_list;
    newconnection=cb;
    newconnection_state=cbstate;
    eng_cil=cil;
    } in
  let eng = B.malloc HyperStack.root e 1ul in
  pop_frame();
  eng

(** Default callback when new connections are made, when the host doesn't
    specify one, such as for client apps *)
let defaultNewConnectionCallback (state:intptr_t) (cs:pointer_or_null connection): intptr_t
=
  nullptr

(**  Public API:  Initialize the QUIC client code.  Returns a pointer, or NULL on failure. *)
let quic_InitializeClient (hostname:C.String.t) (cil:cil_t): ST (pointer_or_null engine)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let eng = initializeEngine hostname true defaultNewConnectionCallback nullptr cil in
  if not (is_null eng) then (
    let cid = generateConnectionID cil in
    let cs = initializeConnection eng hostname true cid cid in
    initializeLossAndCongestion cs;
    let connID = (!*cs).source_connectionID in
    let pholder = B.malloc HyperStack.root (empty_entry cs) 1ul in
    let list = insertHeadList (!*eng).connections pholder in
    upd_connections eng list
  );
  pop_frame();
  eng

(**  Public API:  Initialize the QUIC client code.  Returns a pointer, or NULL on failure. *)
let quic_InitializeServer (hostname:C.String.t) (cb:newConnectionCallback) (cbstate:intptr_t) (cil:cil_t): ST (pointer_or_null engine)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  initializeEngine hostname false cb cbstate cil

type eng_packet = {
  packet_len:U32.t;
  app_data:intptr_t;
  }

(**  Public API:  Prepare a new packet for transmission.  The packet is an OUT buffer of
     length packetlen.  The return value is the number of bytes of data present in then
     packet buffer. This API blocks (non-alertable) until a new packet is ready for 
     transmission. *)
let quic_PreparePacket (eng:pointer engine) (packet:buffer_t) (packetlen:U32.t): ST eng_packet
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  waitForSingleObject (!*eng).dataReadyToSend 0xfffffffful;

  monitorEnter (!*eng).emonitor;
  print_string "Enter QUIC_PreparePacket\n";

  let csholder = (!*eng).readyconnections.lhead in
  let vr = (!*eng).versionreplies.lhead in
  let result,cbstate =
    if not (is_null csholder) then (
      // Remove the first ready connection from the list
      let list = removeEntryList (!*eng).readyconnections csholder in
      upd_readyconnections eng list;
      if (is_null list.lhead) && (is_null vr) then (
        resetEvent (!*eng).dataReadyToSend
      );
      monitorExit (!*eng).emonitor;
      let cs = (!*csholder).p in
      B.free csholder;

      // Call the Connection, to prepare that packet
      monitorEnter (!*cs).monitor;
      let result = preparePacket cs packet packetlen in
      let csm = conn_get_mutable cs in
      let cbstate = csm.app_state in
      monitorExit (!*cs).monitor;
      (result,cbstate)
    ) else if not (is_null vr) then (
      // Remove the version nego request from the list
      let list = removeEntryList (!*eng).versionreplies vr in
      upd_versionreplies eng list;
      let isempty = is_null list.lhead in
      if isempty then (
        resetEvent (!*eng).dataReadyToSend
      );
      monitorExit (!*eng).emonitor;
      let result = prepareNegotiationPacket (!*vr).p.replyid packet packetlen in
      let cbstate = (!*vr).p.replyapp_state in
      B.free vr;
      (result,cbstate)
    ) else (
      // Both lists were null.  No work to do.
      resetEvent (!*eng).dataReadyToSend;
      let cbstate = uint32_to_intptr_t 0ul in
      (0ul,cbstate)
    ) in
  print_string (sprintf "Leave QUIC_PreparePacket - %ul bytes\n" result);
  pop_frame();
  { packet_len = result; app_data = cbstate; }

(** Create a new server-side connection object, in response to
    a ClientHello message.  The returned connection's monitor is
    locked.  The caller must exit the monitor.*)
let createServerConnection (eng:pointer engine) (plaintext_cid:connectionid_t): ST (pointer connection)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  monitorEnter (!*eng).emonitor;
  let true_cid = generateConnectionID (!*eng).eng_cil in
  let cs = initializeConnection eng (!*eng).ehostname false true_cid plaintext_cid in
  monitorEnter (!*cs).monitor;
  initializeLossAndCongestion cs;
  let b = initializemiTLS cs in
  if b <> true then failwith (of_literal "initializemiTLS failed!");
  let connID = (!*cs).source_connectionID in
  let pholder = B.malloc HyperStack.root (empty_entry cs) 1ul in
  let list = insertHeadList (!*eng).connections pholder in
  upd_connections eng list;
  let appstate = (!*eng).newconnection (!*eng).newconnection_state cs in
  upd_app_state (!*cs).csm_state appstate;
  monitorExit (!*eng).emonitor;
  pop_frame();
  cs
