# Source Code
All of the QUIC-F* code is in one flat directory:

* [QUICTypes.fst](./QUICTypes.fst) - the common types used across all modules
* [QUICMutators.fst](./QUICMutators.fst) - helper code to mutate fields within types defined by QUICTypes.fst
* [QUICUtils.fst](./QUICUtils.fst) - common helper code
* [QUICTLS.fst](./QUICTLS.fst) - manages the TLS handshake
* [QUICStream.fst](./QUICStream.fst) - implements the application-level stream abstraction
* [QUICLossAndCongestion.fst](./QUICLossAndCongestion.fst) - implements packet pacing, loss detection, and recovery
* [QUICFrame.fst](./QUICFrame.fst) - parses and formats frames within QUIC network packets
* [QUICConnection.fst](./QUICConnection.fst) - parses and formats QUIC network packets.
* [QUICEngine.fst](./QUICEngine.fst) - server support for a server that listens on one UDP port and handles multiple clients.
* [QUICFStar.h](./QUICFStar.h) - hand-written C code that is included into each extracted C file from the .fst sources.  It helps inteface with miTLS's C interface and with the OS APIs.
* [QUICFStar.c](./QUICFStar.c) - hand-written C code wrappers on OS APIs, such as timers and thread synchronization.
* [Makefile](./Makefile) - GNU make Makefile.  Invoke this on GNU/Linux or Cygwin, to compile the F* code to .c and build test binaries with gcc or mingw-gcc on Windows.
* [makefile.vs](./makefile.vs) - Visual Studio makefile.  Invoke this after using Makefile, to use the MSVC compiler and linker to build native Windows test binaries.

# Key Datastructures
## Doubly Linked List
The `dlist` of type `t`, defined in [QUICTypes.fst](./QUICTypes.fst), is the core datastructure.  It is an element in a doubly-linked list, made up of:
- `flink: pointer_or_null (dlist t)` - the forward link, or null if the element is the first in the list
- `blink: pointer_or_null (dlist t)` - the backward link, or null if the element is the end of the list
- `p: t` - the payload, which is held by-value inside the dlist entry.

Each list has a head, the `dlisthead`, also defined in in [QUICTypes.fst](./QUICTypes.fst.  It has `lhead` and `ltail` fields only, which are the forward and backward links.

With this structure, it isn't easy to have a single payload present on multiple lists.  On occasions where this happens, use a `dlist pointer t` to separate the `dlist` from the payload of type `t`.

## Automated failure propagation:  `return` and `fail` and `type err a`
The `err` type, defined in [QUICTypes.fst](./QUICTypes.fst), enables rich return types from functions, as well as automated error propagation.  Without this, the code would filled with cascaded `if/else` expressions to check for errors at each step.  Instead, make function's return type be `ST (err U32.t)`, to say that the function either returns `Ok` and an unsigned int32, or it returns `Fail` and a diagnostic error string.

Within that function, use `return 3ul` to report success and a value of 3.  Or use `fail "invalid argument"` to report a failure.

The calling function can then use the following notation to invoke the call to the child and automatically propagate the failure along:
```
return_value <-- (child_function child_args);
```
After this statement completes, the value in return_value has UInt32.t type in this example, or else the remainder of the function aborts and propagates the failing return value up.

In practice, this monad works well unless the function returns multiple values in a tuple, such as `ST (er (U32.t U8.t))`.  Ideally we would like to write this:
```
value1,value2 <-- (child_function child args);
```
but it doesn't compile.  Instead, write this:
```
value1_value2 <-- (child_function child args);
let value1,value2 = value1_value2 in
```

## engine
The `engine`, defined in [QUICTypes.fst](./QUICTypes.fst) is the root object for QUIC-F*.  There should be one per process in the normal case.  Its fields include:
- `eis_client:bool` - whether the engine is acting as a QUIC client or server
- `emontor:intptr_t` - a C pointer to the monitor object used to serialize acces to the engine
- `connections` - a doubly-linked list of pointers to `connection` objects.  For clients, there is exactly one element in the list.  For servers, there is one per client, created as part of processing the Initial packet.
- `dataReadyToSend:intptr_t` - a Windows HANDLE representing a manual-reset event.  This event is set when one or more connection objects have data ready to send on the network.
- `newconnection: newConnectionCallback` - a callback function pointer.  It is invoked by the engine whenever a new `connection` object is created in response to a succesful handling of an Initial packet.

## connection
The `connection`, defined in [QUICTypes.fst](./QUICTypes.fst) represents a QUIC peer - a remote client or server.  The object is ummutable.  Its fields include:
- `monitor:intptr_t` - a C pointer to the monitor object used to serialize acces to the connection
- `is_client:bool` - whether the local side of the connection is a client or a server
- `streamDataAvailable:intptr_t` - a Windows HANDLE representing a manual-reset event.  This event is set when this connection is ready to send data.  It is used to unblock the thread that sends socket data.
- `engine:engine_t` - this breaks F*'s type DAG by having a pointer back to the engine that contains this connection.  It must be resolved into a true `engine` type via a call to a C helper function.
- `keys: B.buffer(key_pair)` - the set of crypto keys used by Initial, Handshake, and Application packets.  The array has length 3 always, but some of the keys may be nullptr_t.
- `csm_state: (pointer connection_mutable)` - pointer to the mutable portion of a connection.
- `landc_state: (pointer lossAndCongestion_mutable)` - pointer to the mutable state of the Loss and Congestion data

### connection_mutable
This object contains all of the mutable state associated with a connection.  Fields can be read directly, but writes are always done via mutators implemented in [QUICMutators.fst](./QUICMutators.fst).  The mutators create a new local instance with one field updated, then overwrite the entire original instance.  Later, KreMLin may optimize this into direct mutation of struct fields in C.
- `dest_connectionID:connectionid_t` - the peer's current ConnectionID
- `mitls_state: quic_state` - a native pointer to the miTLS state object, used during the TLS handshake.
- `streams: quic_stream_list` - the list of active QUIC streams
- `readystreams: stream_holder_list` - list of pointers to steams that have data ready to be sent to the peer
- `fixedframes: fixedframe_list` - list of "fixed frame" data waiting to be sent to the peer.  These are QUIC frame types other than CRYPTO or STREAM or ACK.

To access the field 'mitls_state' given `(cs:pointer connection)`, use code like this:
```
let csm = conn_get_mutable cs in
let s = csm.state in
...
```
To modify state, use the "upd_" helpers in QUICMutators.fst, like this:
```
upd_cstate (!*cs).csm_state Running;
```
Note that this update invalidates any previously stashed mutable state objects, such as `csm` from the previous example.  Refresh via another `let csm = conn_get_mustable cs in` call.

# Hosting QUIC-F* in a Client Application
See [httpclient.c](./httpclient.c) for an example.
1. Call `FFI_mitls_init` to initialize miTLS
2. Call `QUICEngine_quic_InitializeClient`, passing in a destination server name string, and the byte-length to use for QUIC Connection IDs.  8 is a good number.  This returns a `QUICTypes_engine*`, a pointer to the engine object.
3. Call `QUICEngine_quic_GetClient` to construct a  `UICTypes_connection*` instance, representing a connection to the remote server.
4. Call `QUICConnection_quic_Handshake()` to do the handshake with the remote server.  On return, the connection is ready for 1RTT data.
5. Call `QUICStream_quic_OpenStream()` to open a stream instance, passing in the stream number to use.
6. Call `QUICStream_quic_SendStream()` to send data on that stream.  Arguments are a buffer, its length in bytes, and whether this is a 'fin' message which closes the stream or not.
7. Call `QUICConnection_quic_GetTicket()` to retrieve the Ticket.  This can be used on subsequent calls to QUIC-F* to initiate 0-RTT.
8. Call `QUICStream_quic_RecvStream()` to block until data arrives on a stream.  The return is a `QUICStream_stream_recv*` that contains the fresh data buffer or failure information, including stream-reset.
9. Call `QUICConnection_quic_CloseConnection()` to close the connection.

In addition, the client must create two threads that run in the background.  One handles incoming UDP packets and one handles outgoing.
```
SendThread
{
    while (true) {
        // Block until QUIC-F* has data ready to send
        QUICEngine_quic_PreparePacket(...)
        // Send it
        sendto(...)
    }
}
```
and
```
RecvThread
{
    while (true) {
        // Block until data arrives
        recvfrom(...)
        // Hand it to QUIC-F* to process
        QUICConnection_quic_ProcessPacket(...)
    }
}
```

# Hosting QUIC-F* in a Server Application
See [httpserver.c](./httpserver.c) for an example.
1. Call `FFI_mitls_init` to initialize miTLS
2. Call `QUICEngine_quic_InitializeServer` to initialize QUIC-F*, passing the address of a callback function to be invoked when new clients connect.  It returns a `QUICTypes_engine*`.
3. Create UDP send and receive threads, same as the client app.

For each newly arrived client, create a processing thread:
```
ClientRecvThread
{
    while (client is connected) {
        QUICStream_stream_recv data = QUICStream_quic_RecvStream()
        // then process stream data

    }
}
```
This thread unblocks whenever stream data arrives from the client.  The return value indicates which stream number is active, and contains the data.  The server can then use `QUICStream_quic_SendStream()` to send its reply.

# Code Walkthrough
## [QUICEngine.fst](./QUICEngine.fst)
The engine is responsible for multiplexing multiple `connection` objects into a single UDP port, by Connection ID.  For server apps, they call the engine to wait for incoming data, and the engine returns a pointer to the connection that received incoming data.

At present, the client side is limited to a single connection per engine instance.  Create multiple engine instances to connect to multiple servers at once.  This can be fixed via a small code change.

### Public APIs
Create an engine instance as a QUIC client.  cil is the lenght, in bytes,
of the connection ID that the client should send to the server.  It can
be 0 if the server supports the feature.
```
let quic_InitializeClient (hostname:C.String.t) (cil:cil_t): ST (pointer_or_null engine)
```
Create an engine instance as a QUIC server.  The callback function is invoked whenever a new client successfully handshakes.  cbstate is
opaque data to associate with the server instance, and is passed to the
callback.  cil is the length, in bytes, of the connection ID that the
server should send to clients.  It can be 0.
```
let quic_InitializeServer (hostname:C.String.t) (cb:newConnectionCallback) (cbstate:intptr_t) (cil:cil_t): ST (pointer_or_null engine)
```

## [QUICConnection.fst](./QUICConnection.fst)
`quic_ProcessPacket` is responsible for handling incoming UDP network packets.  It walks the engine's list of ConnectionID/connection pairs to find the correct connection instance, then hands processing off to the connection itself.  It calls `processClientInitial`, `processInitial`, `processHandshake` and `processLongHeaderPacket` to do the bulk of the work.  These functions validate the packet header, remove protection, then call into QUICFrame to parse individual data frames.


`preparePacket` is responsible for assembling a new UDP packet for transmission.  It writes the new data into a caller-supplied buffer.  It determines the packet kind to write, then calls `prepareInitial`, `prepareHandshake`, or `prepareProtected` to prepare the actual packet.  These functions are responsible for the packet header and protection.  They call into QUICFrame to prepare individual data frames.

### Public APIs
Initiate the TLS handshake from client to server.
```
let quic_Handshake (cs:pointer connection): ST bool
```
Process a received packet.  Returns 0xffffffff if there is an error.
```
let quic_ProcessPacket (eng:pointer engine) (packet:buffer_t) (packetlen:U32.t): ST U32.t
```
Get the associated application state for this connection
```
let quic_GetAppState (cs:pointer connection): ST intptr_t
```
Set the associated application state for this connection, returning the previous value
```
let quic_SetAppState (cs:pointer connection) (new_state:intptr_t) : ST intptr_t
```
Get the 0-rtt ticket.  This may return null immediately after the
    handshake completes, then later become non-null.  The caller should retry
    periodically until a non-null return value
```
let quic_GetTicket (cs:pointer connection): ST (pointer_or_null mitls_ticket)
```
Set the 0-rtt ticket.  This must be called before quic_Handshake()
```
let quic_SetTicket (cs:pointer connection) (ticket:pointer_or_null mitls_ticket): ST unit
```
Set the maximum allowed stream ID.  This can be called with both unidirectional and bidirectional stream IDs.  It can be called before the handshake, which will influence the transport_parameters.  After the
handshake, it results in a QUIC frame being sent to the peer.  This API 
will block until that frame has been ACK'd.
```
let quic_setMaxStreamID (cs:pointer connection) (maxid:U64.t): ST unit
```
Set the maximum allowed data size for the connection.  It can be called before the handshake, which will influence the transport_parameters.  After
the handshake, it results in a QUIC frame being sent to the peer.  This API 
will block until that frame has been ACK'd.
```
let quic_setMaxData (cs:pointer connection) (maxdata:U64.t): ST unit
```
Close the connection
```
let quic_CloseConnection (cs:pointer connection): ST unit
```


## [QUICFrame.fst](./QUICFrame.fst)
Most of this code is called by QUICConnection, and is responsible for parsing or preparing QUIC frames.  STREAM, CRYPTO and ACK frames are the most complex, as they deal with variable-length data.

## [QUICStream.fst](./QUICStream.fst)
On the receive side of a stream, much of the work is around arrival of out-of-order or retransmitted frames.  The stream code must buffer out-of-order data.  And retransmission does not have to send same-sized chunks of data as the original transmission, so regions of data can overlap.

On the send side, the calling application's data must be chunked to fit
inside the variable amount of space available within a UDP frame that contains a QUIC packet.

QUIC streams also have flow control and quotas.  These are NYI in QUIC-F* at present.

The CRYPTO stream is implemented as three separate stream object instances, one for each kind of QUIC packet:  Initial, Handshake, and Application.  The CRYPTO stream doesn't have a number:  it is referenced as a `pointer quic_stream`.

### Datastructures
The `quic_stream_fixed` is a pair:  the 64-bit stream ID and a pointer to a `quic_stream_mutable`.
A `quic_stream` is a dlist of `quic_stream_fixed`.  This allows the connection to hold onto a doubly-linked list of quic_stream objects representing opened streams.
A `quic_stream_mutable` holds all of the stream data.  Although the QUIC spec calls out state separately for recieve-stream and send-stream, QUIC-F* stores them both together in one structure.  This simplifies the higher-level code, which doesn't care whether a stream is uni- or bi- directional.

### Public APIs
Open a QUIC stream.  Returns NULL on failure.
```
let quic_OpenStream (cs:pointer connection) (stream:U64.t) : ST (pointer_or_null quic_stream)
```
Send data on a stream.
```
let quic_SendStream (cs:pointer connection) (strm: pointer quic_stream) (data:buffer_t) (datalength:U32.t) (fin:bool) : ST (err bool)
```
Close a stream.
```
let quic_CloseStream (cs:pointer connection) (strm:pointer quic_stream): ST unit
```
Receive data on a stream.  This will block until data arrives.  It returns the number of bytes written into the buffer.
```
let quic_RecvStream (cs:pointer connection) : ST stream_recv
```
Query if the 'fin' marker has been received, for end of the stream.
```
let quic_StreamIsFin (cs:pointer connection) (strm:pointer quic_stream): ST bool
```

## [QUICTLS.fst](./QUICTLS.fst)
This is glue code to interface with miTLS.  It is responsible for parsing and formating the QUIC transport_parameters, handling nego callbacks, deriving crypto keys and the packet protection mask.

The actual TLS handshake is implemented in QUICFrame.fst's `processCryptoSegment` and QUICConnection.fst's `quic_Handshake`.

## [QUICUtils.fst](./QUICUtils.fst)
This code is common utility code.  Most of these helpers marshal data into and out of buffers in network byte order.
- Functions with the name 'append' write data to the buffer and return an updated write offset.
- Functions with the name 'get' read data from the buffer and return it.  They do not perform bounds checking, and require the caller to be sure they are safe.
- Functions with the name 'get' and end in "_s" are the "safe" versions and perform bounds checking.  They either return the data or an error state.
