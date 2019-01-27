# module QUICMutators
- Mutator helper functions



QUIC Mutators - helper functions to mutate data within the QUIC state



```fsharp
let ((strm_get_mutable (strm:pointer quic_stream)):(Stack (quic_stream_mutable) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):let  strm' = !*(strm) in !*((strm'.p.qsm_state))
```


 Get a readonly copy of the mutable part of a quic_stream 

```fsharp
let ((upd_state (strmm:pointer quic_stream_mutable) (newstate:quic_stream_state)):(Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):.()<-(strmm, 0, {.()(strmm, 0) with state=newstate})
```


 Update the 'state' field 

```fsharp
let ((landc_get_mutable (cs:pointer connection)):(Stack (lossAndCongestion_mutable) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):let  cs' = !*(cs) in .()(cs'.landc_state, 0)
```


 Get a readonly view of the mutable LossAndCongestion state 

```fsharp
let ((conn_get_mutable (cs:pointer connection)):(Stack (connection_mutable) ((requires ((fun _ -> true)))) ((ensures ((fun _ _ _ -> true)))))):let  cs' = !*(cs) in .()(cs'.csm_state, 0)
```


 Get a readonly view of the mutable connection state 

