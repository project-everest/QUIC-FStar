# module QUICConnection
Top-level QUIC API, for packet-level communication with a remote peer.



QUIC Connection - the packet-level layer that exchanges messages with a remote peer.



```fsharp
let ((showError (e:quic_errmsg)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):if <>(e, nullptr) then C.String.print (C.String.of_literal "MITLS ShowError() is NYI
") else (); ffi_mitls_free_msg e
```


 Report any errors returned by miTLS 

```fsharp
let ((computePacketNumber (cs:pointer connection) (pn:U64.t) (pn_bytesize:U32.t)):(Stack U64.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):if =(pn_bytesize, 8) then pn else _
```


 Compute the 64-bit packet number given a partial packet number.  pn_bytesize is the
    number of bytes of packet number present in pn.  The remaining bits are computed
    based on prior knowledge stored in the connection object. 

```fsharp
let ((generateConnectionID ()):(Stack U64.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):let  r1 = C.rand () in let  r2 = C.rand () in let  rl1 = Cast.int32_to_uint64 r1 in let  rl2 = Cast.int32_to_uint64 r2 in _
```


 Generate a new pseudo-random connection ID for the handshake.  It will be replaced
    by the server-generated connection ID later. 

```fsharp
let ((generateInitialPacketNumber ()):(Stack U64.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):let  r = C.rand () in _
```


 Generate a new pseudo-random initial packet number 

```fsharp
let ((initializeConnection ()):(Stack (pointer connection) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):let  cid = generateConnectionID () in let  maxoutgoingAcks = 256 in let  (encryptkey, decryptkey) = derive_plaintext_secrets cid in let  (csm:connection_mutable) = {cstate=Start connectionID=cid connectionID0RTT=cid mitls_state=nullptr packetNumber=0 maxReceivedPacketNumber=0 key1rttEncrypt=nullptr key1rttDecrypt=nullptr key0rtt=nullptr stream0BytesReceived=0 defaultMaxStreamData=0 maxData=0 maxStreamID=0 maxPayloadSize=_ pingPending=false streams=empty_list shortHeaderPackets=empty_list outgoingAckCount=0} in let  csmr = FStar.Buffer.rcreate FStar.HyperHeap.root csm 1 in let  landc = makeLossAndCongestion (false) in let  (cs:connection) = {monitor=monitorAlloc () encryptkey=encryptkey decryptkey=decryptkey dataReadyToSend=createEvent 1 0 maxoutgoingAcks=maxoutgoingAcks outgoingAcks=FStar.Buffer.rcreate FStar.HyperHeap.root 0 maxoutgoingAcks landc_state=landc csm_state=csmr} in FStar.Buffer.rcreate FStar.HyperHeap.root cs 1
```


 Create a new 'connection' instance.  The returned pointer is heap-allocated. 

```fsharp
let ((updateExportKey (cs:pointer connection) (is1rtt:bool) (encrypt_label:C.String.t) (decrypt_label:C.String.t)):(Stack bool ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  csm = conn_get_mutable cs in let  secret = Buffer.create 0 secret_size in let  early = if is1rtt then 0 else 1 in let  errmsg = Buffer.create nullptr 1 in let  result = ffi_mitls_quic_get_exporter csm.mitls_state early secret errmsg in let  retval = if =(result, 0) then (C.String.print (C.String.of_literal "FFI_mitls_quic_get_exported failed!
"); false) else let  derived = Buffer.create 0 secret_size in let  result = quic_crypto_tls_derive_secret derived secret encrypt_label in if =(result, 0) then (C.String.print (C.String.of_literal "quic_crypto_derive_secret failed!
"); false) else let  key = Buffer.create nullptr 1 in let  result = quic_crypto_derive_key key derived in if =(result, 0) then (C.String.print (C.String.of_literal "quic_crypto_derive_key(encrypt) failed!
"); false) else (if is1rtt then (upd_key1rttEncrypt (!*(cs)).csm_state !*(key); let  result = quic_crypto_tls_derive_secret derived secret decrypt_label in if =(result, 0) then (C.String.print (C.String.of_literal "quic_crypto_derive_key(decrypt) failed!
"); false) else (let  key1rtt = Buffer.create nullptr 1 in let  result = quic_crypto_derive_key key1rtt derived in if =(result, 0) then (C.String.print (C.String.of_literal "quic_crypto_derive_key(decrypt) failed!
"); false) else (upd_key1rttDecrypt (!*(cs)).csm_state !*(key1rtt); true))) else (upd_key0rtt (!*(cs)).csm_state !*(key); true)) in pop_frame (); retval
```


 Update the encryption/decryption keys based on updated data from the server 

```fsharp
let ((updatePeerParameters (cs:pointer connection)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  errmsg = Buffer.create nullptr 1 in let  zero128 = _ in let  (qp:quic_transport_parameters) = {max_stream_data=0 max_data=0 max_stream_id=0 idle_timeout=0 others_len=nullptr others0=zero128 others1=zero128 others2=zero128 others3=zero128 others4=zero128 others5=zero128 others6=zero128 others7=zero128 others8=zero128 others9=zero128 others10=zero128 others11=zero128 others12=zero128 others13=zero128 others14=zero128 others15=zero128 others16=zero128 others17=zero128 others18=zero128 others19=zero128 others20=zero128 others21=zero128 others22=zero128 others23=zero128 others24=zero128 others25=zero128 others26=zero128 others27=zero128 others28=zero128 others29=zero128 others30=zero128 others31=zero128 others32=zero128 others33=zero128 others34=zero128 others35=zero128 others36=zero128 others37=zero128 others38=zero128 others39=zero128 others40=zero128 others41=zero128 others42=zero128 others43=zero128 others44=zero128 others45=zero128 others46=zero128 others47=zero128 others48=zero128 others49=zero128 others50=zero128 others51=zero128 others52=zero128 others53=zero128 others54=zero128 others55=zero128 others56=zero128 others57=zero128 others58=zero128 others59=zero128 others60=zero128 others61=zero128 others62=zero128 others63=zero128} in let  qp' = Buffer.create qp 1 in let  csm = conn_get_mutable cs in let  result = ffi_mitls_quic_get_peer_parameters csm.mitls_state qp' errmsg in if =(result, 0) then C.String.print (C.String.of_literal "FFI_mitls_quic_get_peer_parameters failed
") else (); showError !*(errmsg); let  max_data = (!*(qp')).max_data in let  max_data64 = Cast.uint32_to_uint64 max_data in let  max_stream_data = (!*(qp')).max_stream_data in let  max_stream_data64 = Cast.uint32_to_uint64 max_stream_data in upd_defaultMaxStreamData (!*(cs)).csm_state max_stream_data64; upd_maxData (!*(cs)).csm_state _; upd_maxStreamID (!*(cs)).csm_state (!*(qp')).max_stream_id; pop_frame ()
```


 Parse the server's peer parameters structure and update the local connection
    state with its value 

```fsharp
let ((processHandshake (cs:pointer connection) (inbuf:buffer_t) (len:U32.t)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); monitorEnter (!*(cs)).monitor; let  csm = conn_get_mutable cs in let  inbuflen = Buffer.create (uint32_to_intptr_t len) 1 in let  handshakesize = 1200 in let  outbuf = FStar.Buffer.rcreate FStar.HyperHeap.root 0 handshakesize in let  outbuflen = Buffer.create (uint32_to_intptr_t handshakesize) 1 in let  errmsg = Buffer.create nullptr 1 in let  result = ffi_mitls_quic_process (csm.mitls_state) inbuf inbuflen outbuf outbuflen errmsg in showError !*(errmsg); let  t = !*(outbuflen) in let  outbuflen = intptr_t_to_uint32 t in (match result with TLS_would_block  -> if <>(len, 0) then updatePeerParameters cs else (); monitorExit (!*(cs)).monitor; let  stream0 = quic_OpenStream cs 0 in if <>(outbuflen, 0) then quic_SendStream cs stream0 outbuf outbuflen false else (); let  receivedlen = quic_RecvStream cs stream0 outbuf handshakesize in processHandshake cs outbuf receivedlen | TLS_client_complete  -> updatePeerParameters cs; let  b = updateExportKey cs true (C.String.of_literal "EXPORTER-QUIC client 1-RTT Secret") (C.String.of_literal "EXPORTER-QUIC server 1-RTT Secret") in if =(b, false) then C.String.print (C.String.of_literal "miTLS failure updating the export key
") else (); let  _ = if <>(outbuflen, 0) then (monitorExit (!*(cs)).monitor; let  stream0 = quic_OpenStream cs 0 in quic_SendStream cs stream0 outbuf outbuflen false; monitorEnter (!*(cs)).monitor; ()) else () in upd_cstate (!*(cs)).csm_state Protected; monitorExit (!*(cs)).monitor; enablePingTimer cs | TLS_error_alert  -> C.String.print (C.String.of_literal "FFI_mitls_quic_process failed!") | _  -> C.String.print (C.String.of_literal "Other result")); pop_frame ()
```


 Process a received TLS handshake message by calling into miTLS and preparing
    the stream0 response, if needed. 

```fsharp
let ((quic_Handshake (cs:pointer connection)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  inbuf = Buffer.create 0 1 in upd_handshake_packets_outstanding (!*(cs)).landc_state true; processHandshake cs inbuf 0; upd_handshake_packets_outstanding (!*(cs)).landc_state false; pop_frame ()
```


  Public API:  Initiate the TLS handshake from client to server. 

```fsharp
let ((findNextReadyStream (strm:pointer_or_null quic_stream)):(Stack (pointer_or_null quic_stream) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  ret = if is_null strm then null quic_stream else if hasMoreToSend strm then strm else findNextReadyStream (!*(strm)).flink in pop_frame (); strm
```


 Helper, to walk the list of streams, stopping on the first one that has ready data 

```fsharp
let ((findReadyStream (cs:pointer connection)):(Stack (pointer quic_stream) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  strm = findNextReadyStream (!*(((!*(cs)).csm_state))).streams.lhead in pop_frame (); strm
```


 Find a quic_stream that has data ready for transmission.  The caller must ensure
    that at least one stream actually has ready data. 

```fsharp
let ((prepareProtected (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  (lrlist:lossRecoveryTracker_list) = empty_list in let  csm = conn_get_mutable cs in let  p = append8 packet 0 0x63 in let  p = append64 packet p csm.connectionID in let  p = append32 packet p (Cast.uint64_to_uint32 csm.packetNumber) in if <>(p, 13) then C.String.print (C.String.of_literal "Invalid short-form packet
") else (); let  aeadOverhead = 16 in let  plainlength = _ in let  plain = Buffer.rcreate FStar.HyperHeap.root 0 plainlength in let  (plainp, lrlist) = prepareAckFrame cs plain 0 plainlength lrlist in let  ackend = plainp in let  p = if csm.pingPending then (upd_pingPending (!*(cs)).csm_state false; append8 plain plainp 0x07) else plainp in let  str = findReadyStream cs in let  (plainp, lrlist) = if not (is_null str) then (prepareStreamFrame str plain plainlength plainp lrlist) else (((FStar.Pervasives.Native.Mktuple2 plainp lrlist))) in let  cipher = Buffer.offset packet p in let  result = quic_crypto_encrypt csm.key1rttEncrypt cipher csm.packetNumber packet p plain plainp in if <>(result, 0) then C.String.print (C.String.of_literal "quic_crypto_encrypt failure in PrepareProtected") else (); let  length = _ in let  tracked_packet_length = if =(plainp, ackend) then 0 else length in onPacketSent cs csm.packetNumber tracked_packet_length lrlist; inc_packetNumber (!*(cs)).csm_state; pop_frame (); length
```


 Prepare a protected packet for transmission 

```fsharp
let ((protectCleartext (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t) (payload:buffer_t) (payloadlength:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  csm = conn_get_mutable cs in let  sn = csm.packetNumber in let  r = quic_crypto_encrypt ((!*(cs)).encryptkey) (Buffer.offset packet 17) sn packet 17 payload payloadlength in if =(r, 0) then C.String.print (C.String.of_literal "quic_crypto_encrypt failed
") else (); pop_frame (); _
```


 Protect a QUIC packet using the QUIC AEAD construction 

```fsharp
let ((unprotectCleartext (cs:pointer connection) (packetnumber:U64.t) (packet:buffer_t) (packetlen:U32.t) (plain:buffer_t) (maxplainlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  payloadlength = _ in let  r = quic_crypto_decrypt ((!*(cs)).decryptkey) plain packetnumber packet 17 (Buffer.offset packet 17) _ in if =(r, 0) then C.String.print (C.String.of_literal "quic_crypto_decrypt_failed
") else (); pop_frame (); payloadlength
```


 Unprotect a "cleartext" QUIC packet using the QUIC AEAD construction 

```fsharp
let ((prepareClientInitial (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); upd_cstate (!*(cs)).csm_state Cleartext; upd_packetNumber (!*(cs)).csm_state (generateInitialPacketNumber ()); let  payloadlength = _ in let  payload = FStar.Buffer.rcreate FStar.HyperHeap.root 0 payloadlength in let  (lrlist:lossRecoveryTracker_list) = empty_list in let  (_, lrlist) = prepareClientHelloFrame cs payload payloadlength lrlist in let  csm = conn_get_mutable cs in let  p = append8 packet 0 0x82 in let  p = append64 packet p csm.connectionID in let  p = append32 packet p (Cast.uint64_to_uint32 csm.packetNumber) in let  p = append32 packet p quicVersion in if <>(p, 17) then C.String.print (C.String.of_literal "Invalid long-form packet
") else (); let  length = protectCleartext cs packet packetlen payload payloadlength in onPacketSent cs csm.packetNumber length lrlist; inc_packetNumber (!*(cs)).csm_state; pop_frame (); length
```


 Prepare a ClientInitial packet for transmission 

```fsharp
let ((prepareCleartext (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  (lrlist:lossRecoveryTracker_list) = empty_list in let  csm = conn_get_mutable cs in let  payloadlength = _ in let  payload = FStar.Buffer.rcreate FStar.HyperHeap.root 0 payloadlength in let  (p, lrlist) = prepareAckFrame cs payload 0 payloadlength lrlist in let  ackend = p in let  p = if csm.pingPending then (upd_pingPending (!*(cs)).csm_state false; append8 payload p 0x07) else p in let  str = findReadyStream cs in let  (payloadlength, lrlist) = if not (is_null str) then (prepareStreamFrame str payload payloadlength p lrlist) else (((FStar.Pervasives.Native.Mktuple2 payloadlength lrlist))) in let  p = append8 packet 0 0x85 in let  p = append64 packet p csm.connectionID in let  p = append32 packet p (Cast.uint64_to_uint32 csm.packetNumber) in let  p = append32 packet p quicVersion in if <>(p, 17) then C.String.print (C.String.of_literal "Invalid long-form packet
") else (); let  length = protectCleartext cs packet packetlen payload payloadlength in let  tracked_packet_length = if =(payloadlength, ackend) then 0 else length in onPacketSent cs csm.packetNumber tracked_packet_length lrlist; inc_packetNumber (!*(cs)).csm_state; pop_frame (); length
```


 Prepare a Client Cleartext packet for transmission 

```fsharp
let ((quic_PreparePacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); waitForSingleObject (!*(cs)).dataReadyToSend 0xffffffff; monitorEnter (!*(cs)).monitor; C.String.print (C.String.of_literal "Enter QUIC_PreparePacket
"); let  csm = conn_get_mutable cs in let  result = match csm.cstate with Start  -> 0xffffffff | ClientInitial  -> prepareClientInitial cs packet packetlen | ServerStatelessRetry  -> 0xffffffff | Cleartext  -> prepareCleartext cs packet packetlen | Protected  -> prepareProtected cs packet packetlen | _  -> 0xffffffff in if (connectionHasMoreToSend cs) then (setEvent (!*(cs)).dataReadyToSend) else (resetEvent (!*(cs)).dataReadyToSend); C.String.print (C.String.of_literal "Leave QUIC_PreparePacket
"); monitorExit (!*(cs)).monitor; pop_frame (); result
```


  Public API:  Prepare a new packet for transmission.  The packet is an OUT buffer of
     length packetlen.  The return value is the number of bytes of data present in then
     packet buffer. This API blocks (non-alertable) until a new packet is ready for 
     transmission. 

```fsharp
let ((readShortPacketNumber (cs:pointer connection) (packet:buffer_t) (offset:U32.t) (t:U8.t)):(Stack (*(U64.t, U32.t)) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  result = (match t with 1  -> let  pn = getu8 packet offset in let  pn64 = Cast.uint8_to_uint64 pn in let  cpn = computePacketNumber cs pn64 1 in ((FStar.Pervasives.Native.Mktuple2 cpn _)) | 2  -> let  pn = getu16 packet offset in let  pn64 = Cast.uint16_to_uint64 pn in let  cpn = computePacketNumber cs pn64 2 in ((FStar.Pervasives.Native.Mktuple2 cpn _)) | 3  -> let  pn = getu32 packet offset in let  pn64 = Cast.uint32_to_uint64 pn in let  cpn = computePacketNumber cs pn64 4 in ((FStar.Pervasives.Native.Mktuple2 cpn _)) | _  -> C.String.print (C.String.of_literal "Unexpected short packet type"); ((FStar.Pervasives.Native.Mktuple2 0 0xffffffff))) in pop_frame (); result
```


 Parse the packet number in the short-packet format 

```fsharp
let ((processServerCleartext (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  connectionID = getu64 packet 1 in let  pnpart = getu32 packet 9 in let  packetNumber = computePacketNumber cs (Cast.uint32_to_uint64 pnpart) 4 in let  plain = Buffer.create 0 1500 in let  plainlen = unprotectCleartext cs packetNumber packet packetlen plain 1500 in upd_connectionID (!*(cs)).csm_state connectionID; let  offset = processCleartextFrames cs plain 0 plainlen in registerAck cs packetNumber; let  csm = conn_get_mutable cs in if U64.lt csm.maxReceivedPacketNumber packetNumber then (upd_maxReceivedPacketNumber (!*(cs)).csm_state packetNumber) else (); pop_frame (); offset
```


 Process a received Server Cleartext packet 

```fsharp
let ((processLongHeaderPacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  version = getu32 packet 13 in if <>(version, quicVersion) then C.String.print (C.String.of_literal "Unexpected QUIC version
") else (); let  ret = match .()(packet, 0) with 0x81  -> C.String.print (C.String.of_literal "Unsupported - Version nego
"); 0 | 0x82  -> C.String.print (C.String.of_literal "Unsupported - ClientInitial
"); 0 | 0x83  -> C.String.print (C.String.of_literal "Unsupported - Server Stateless Retry
"); 0 | 0x84  -> processServerCleartext cs packet packetlen | 0x85  -> C.String.print (C.String.of_literal "Unsupported - Client Cleartext
"); 0 | 0x86  -> C.String.print (C.String.of_literal "Unsupported - 0-RTT Protected
"); 0 | _  -> C.String.print (C.String.of_literal "Unsupported long header type
"); 0 in pop_frame (); 0
```


 Process a received long-header packet 

```fsharp
let ((processShortHeaderPacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  csm = conn_get_mutable cs in let  first = getu8 packet 0 in let  c = _ in let  k = _ in let  typ = _ in let  (connectionID, p) = if <>(c, 0) then ((FStar.Pervasives.Native.Mktuple2 (getu64 packet 1) 9)) else ((FStar.Pervasives.Native.Mktuple2 csm.connectionID 1)) in let  (packetnumber, p) = readShortPacketNumber cs packet p typ in let  aeadOverhead = 16 in let  plainlength = _ in let  plain = Buffer.rcreate FStar.HyperHeap.root 0 plainlength in let  cipher = Buffer.offset packet p in let  cipherlength = _ in let  result = quic_crypto_decrypt csm.key1rttDecrypt plain packetnumber packet p cipher cipherlength in if =(result, 0) then C.String.print (C.String.of_literal "quic_crypto_decrypt failed
") else (); let  offset = processProtectedFrames cs plain 0 plainlength in registerAck cs packetnumber; if U64.lt csm.maxReceivedPacketNumber packetnumber then (upd_maxReceivedPacketNumber (!*(cs)).csm_state packetnumber) else (); pop_frame (); 0
```


 Process a received short-header packet.  This may be called only after the 1RTT keys
    have arrived. 

```fsharp
let ((quic_ProcessPacket (cs:pointer connection) (packet:buffer_t) (packetlen:U32.t)):(Stack U32.t ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); monitorEnter (!*(cs)).monitor; C.String.print (C.String.of_literal "Enter QUIC_ProcessPacket
"); let  result = if =(_, 0) then (let  csm = conn_get_mutable cs in if =(csm.key1rttDecrypt, nullptr) then (let  (t:packet_holder_fixed) = {packet=packet packetlen=packetlen} in let  holder = empty_entry t in let  pholder = Buffer.rcreate FStar.HyperHeap.root holder 1 in let  list = insertTailList csm.shortHeaderPackets pholder in upd_shortHeaderPackets (!*(cs)).csm_state list; 0) else (processShortHeaderPacket cs packet packetlen)) else (processLongHeaderPacket cs packet packetlen) in let  key1rttDecrypt = (!*(((!*(cs)).csm_state))).key1rttDecrypt in let  shortHeaderPackets = (!*(((!*(cs)).csm_state))).shortHeaderPackets in if &&((<>(key1rttDecrypt, nullptr)), (not (is_null shortHeaderPackets.lhead))) then (upd_shortHeaderPackets (!*(cs)).csm_state empty_list; let  packet = Buffer.create shortHeaderPackets.lhead 1 in C.Loops.do_while ((fun h break -> /\(live h packet, (==>(break, False))))) ((fun _ -> let  pkt = !*(packet) in let  _ = processShortHeaderPacket cs (!*(pkt)).p.packet (!*(pkt)).p.packetlen in .()<-(packet, 0, (!*((!*(packet)))).flink); let  pval = !*(packet) in is_null pval))) else (); C.String.print (C.String.of_literal "Leave QUIC_ProcessPacket
"); monitorExit (!*(cs)).monitor; pop_frame (); result
```


 Public API: Process a received packet.  Returns 0xffffffff if there is an error. 

```fsharp
let ((quic_InitializeClient (hostname:C.String.t)):(Stack (pointer_or_null connection) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):push_frame (); let  cs = initializeConnection () in let  suppversions = Buffer.create quicVersion 1 in let  zero128 = _ in let  (tp:quic_transport_parameters) = {max_stream_data=_ max_data=_ max_stream_id=10 idle_timeout=100 others_len=nullptr others0=zero128 others1=zero128 others2=zero128 others3=zero128 others4=zero128 others5=zero128 others6=zero128 others7=zero128 others8=zero128 others9=zero128 others10=zero128 others11=zero128 others12=zero128 others13=zero128 others14=zero128 others15=zero128 others16=zero128 others17=zero128 others18=zero128 others19=zero128 others20=zero128 others21=zero128 others22=zero128 others23=zero128 others24=zero128 others25=zero128 others26=zero128 others27=zero128 others28=zero128 others29=zero128 others30=zero128 others31=zero128 others32=zero128 others33=zero128 others34=zero128 others35=zero128 others36=zero128 others37=zero128 others38=zero128 others39=zero128 others40=zero128 others41=zero128 others42=zero128 others43=zero128 others44=zero128 others45=zero128 others46=zero128 others47=zero128 others48=zero128 others49=zero128 others50=zero128 others51=zero128 others52=zero128 others53=zero128 others54=zero128 others55=zero128 others56=zero128 others57=zero128 others58=zero128 others59=zero128 others60=zero128 others61=zero128 others62=zero128 others63=zero128} in let  (ticket:quic_ticket) = {ticket_len=0 ticket=null C.char session_len=0 session=null C.char} in let  (ticketptr:pointer quic_ticket) = Buffer.create ticket 1 in let  (cfg:quic_config) = {is_server=0 supported_versions=suppversions supported_versions_len=uint32_to_intptr_t 1 qp=tp alpn=nullptr cipher_suites=nullptr signature_algorithms=C.String.of_literal "ECDSA+SHA256:RSAPSS+SHA256" named_groups=C.String.of_literal "X25519" enable_0rtt=1 host_name=hostname ca_file=C.String.of_literal "test.ca" server_ticket=null quic_ticket certificate_chain_file=nullptr private_key_file=nullptr ticket_enc_alg=nullptr ticket_key=nullptr ticket_key_len=nullptr} in initializeLossAndCongestion cs; let  qstate = FStar.Buffer.create nullptr 1 in let  errmsg = FStar.Buffer.create nullptr 1 in let  _ = ffi_mitls_thread_register () in let  r = ffi_mitls_quic_create qstate cfg errmsg in showError !*(errmsg); let  retval = if <>(r, 1) then (C.String.print (C.String.of_literal "FFI_mitls_quic_create failed
"); null connection) else (upd_mitls_state (!*(cs)).csm_state !*(qstate); upd_cstate (!*(cs)).csm_state ClientInitial; cs) in pop_frame (); retval
```


  Public API:  Initialize the QUIC client code.  Returns a pointer, or NULL on failure. 

