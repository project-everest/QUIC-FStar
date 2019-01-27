# module QUICFFI
Make calls into Everest and Windows APIs



QUIC FFI - Calls from QUIC code into miTLS, libquiccrypto, or Windows APIs.



```fsharp
val createEvent:Unidentified product: [Int32.t] Unidentified product: [Int32.t] (Stack intptr_t ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 This is implemented in QUICFStar.c and calls CreateEventW with a NULL name and default security

```fsharp
val monitorAlloc:Unidentified product: [unit] (Stack intptr_t ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Implemented in QUICFStar.c, calls InitializeCriticalsection 

```fsharp
val monitorEnter:Unidentified product: [intptr_t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Implemented in QUICFStar.c, calls EnterCriticalsection 

```fsharp
val monitorExit:Unidentified product: [intptr_t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Implemented in QUICFStar.c, calls LeaveCriticalsection 

```fsharp
val waitForSingleObject:Unidentified product: [intptr_t] Unidentified product: [U32.t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Call Windows WaitForSingleObject, with a timeout in milliseconds 

```fsharp
val setEvent:Unidentified product: [intptr_t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Call Windows SetEvent() 

```fsharp
val resetEvent:Unidentified product: [intptr_t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Call Windows ResetEvent() 

```fsharp
val getSystemTime:Unidentified product: [unit] (Stack I64.t ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Get the system time, in UTC, measured in Windows FILETIME units (10,000ns)
    The absolute value doesn't matter, as all computation is relative. 

```fsharp
val qsort64:Unidentified product: [(pointer U64.t)] Unidentified product: [(U32.t)] Unidentified product: [comparator] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Use the CRT qsort() to sort an array of UInt64.t in-place 

```fsharp
type abbrev 
```


 Type of a timer callback function.
    First argument is a TP_CALLBACK_INSTANCE, and should be ignored
    Third argument is the PTP_TIMER that fired 

```fsharp
val createTimer:Unidentified product: [(pointer connection)] Unidentified product: [timercallback] (Stack intptr_t ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Create a timer with callback 

```fsharp
val setOneShotTimer:Unidentified product: [intptr_t] Unidentified product: [Int64.t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Set a one-shot timer.  Positive times are absolute, negative are relative, in 100ns ticks 

```fsharp
val cancelOneShotTimer:Unidentified product: [intptr_t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Cancel a one-shot timer.  

```fsharp
val setRepeatingTimer:Unidentified product: [intptr_t] Unidentified product: [U32.t] (Stack unit ((requires ((fun _ -> true)))) ((ensures ((fun h0 _ h1 -> modifies_none h0 h1)))))
```


 Set a repeating timer, with period specified in milliseconds 

