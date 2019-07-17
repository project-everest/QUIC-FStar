module QUICUtils

open FStar
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt32
open FStar.Int.Cast
open FStar.Printf
open C
open LowStar.Buffer
open LowStar.BufferOps
open C.Failure
open C.String
open QUICTypes

module U64 = FStar.UInt64
module U32 = FStar.UInt32
module U16 = FStar.UInt16
module U8 = FStar.UInt8
module I64 = FStar.Int64
module I32 = FStar.Int32
module Cast = FStar.Int.Cast
module B = LowStar.Buffer

(** Append a uint64 value to the buffer. Returns the next write offset. *)
let append64 (b:buffer_t) (offset:U32.t) (value:U64.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 8))))
   (ensures (fun _ _ _ -> true))
=
   store64_be (B.offset b offset) value;
   offset +^ 8ul
  
(** Append a uint32 value to the buffer.  Returns the next write offset. *)
let append32 (b:buffer_t) (offset:U32.t) (value:U32.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 4))))
   (ensures (fun _ _ _ -> true))
=
   store32_be (B.offset b offset) value;
   offset +^ 4ul
  
(** Append a uint16 value to the buffer.  Returns the next write offset. *)
let append16 (b:buffer_t) (offset:U32.t) (value:U16.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 2))))
   (ensures (fun _ _ _ -> true))
=
   store16_be (B.offset b offset) value;
   offset +^ 2ul
  
(** Append a uint8 value to the buffer.  Returns the next write offset. *)
let append8 (b:buffer_t) (offset:U32.t) (value:U8.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 1))))
   (ensures (fun _ _ _ -> true))
=
   B.upd b offset value;
   offset +^ 1ul

// No polymorphic "append()" in F*... depends on "match value with" followed by type names

(** Append raw bytes to a buffer.  Returns the next write offset. *)
let appendbytes (b:buffer_t) (offset:U32.t) (value:buffer_t) (valuelength:U32.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - U32.v valuelength))))
   (ensures (fun _ _ _ -> true))
= 
   B.blit value 0ul b offset valuelength;
   offset+^valuelength

 (** getbytes "safe" - read out of buffer 'b' with length 'l' at offset 'offset' into value/valuelength.
      Returns the next write offset. *)
let getbytes_s (b:buffer_t) (l:U32.t) (offset:U32.t) (value:buffer_t) (valuelength:U32.t): ST (err U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
   if U32.(offset+^valuelength >^ l) then
     fail !$"Insufficient buffer"
   else (
     B.blit b offset value 0ul valuelength;
     return U32.(offset +^ valuelength)
     )

(** Read a uint64 from the buffer *)
let getu64 (b:buffer_t) (offset:U32.t): ST U64.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 8))))
   (ensures (fun _ _ _ -> true))
=
   load64_be (B.offset b offset)

(** Read a uint32 from the buffer *)
let getu32 (b:buffer_t) (offset:U32.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 4))))
   (ensures (fun _ _ _ -> true))
=
   load32_be (B.offset b offset)

 (** Read "safely" a uint32 from the buffer.  Returns the value or an 
       error if the read is past the end of the buffer. *)
let getu32_s (b:buffer_t) (l:U32.t) (offset:U32.t): ST (err U32.t)
   (requires (fun _ -> (UInt32.v offset < (B.length b - 4))))
   (ensures (fun _ _ _ -> true))
=
   if U32.(offset+^4ul >^ l) then
     fail !$"Insufficient buffer"
   else
     return (load32_be (B.offset b offset))

(** Read a uint16 from the buffer *)
let getu16 (b:buffer_t) (offset:U32.t): ST U16.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 2))))
   (ensures (fun _ _ _ -> true))
=
   load16_be (B.offset b offset)

 (** Read "safely" a uint16 from the buffer.  Returns the value or an 
       error if the read is past the end of the buffer. *)
let getu16_s (b:buffer_t) (l:U32.t) (offset:U32.t): ST (err U16.t)
   (requires (fun _ -> (UInt32.v offset < (B.length b - 2))))
   (ensures (fun _ _ _ -> true))
=
   if U32.(offset+^2ul >^ l) then
     fail !$"Insufficient buffer"
   else
     return (load16_be (B.offset b offset))

(** Read a uint8 from the buffer *)
let getu8 (b:buffer_t) (offset:U32.t): ST U8.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 1))))
   (ensures (fun _ _ _ -> true))
=
   B.index b offset
   
(** Read "safely" a uint8 from the buffer.  Returns the value or an 
       error if the read is past the end of the buffer. *)
let getu8_s (b:buffer_t) (l:U32.t) (offset:U32.t): ST (err U8.t)
   (requires (fun _ -> (UInt32.v offset < (B.length b - 1))))
   (ensures (fun _ _ _ -> true))
=
   if U32.(offset+^1ul >^ l) then
     fail !$"Insufficient buffer"
   else
     return (B.index b offset)
   
(* Compute max of two values *)
let maxi64 (x:I64.t) (y:I64.t): I64.t =
  if I64.gt x y then x else y 

(* Compute max of two values *)
let maxu64 (x:U64.t) (y:U64.t): U64.t =
  if U64.gt x y then x else y 

(* Compute min of two values *)
let minu32 (x:U32.t) (y:U32.t): U32.t =
  if U32.gt x y then y else x 

(* Compute min of two values *)
let minu64 (x:U64.t) (y:U64.t): U64.t =
  if U64.gt x y then y else x 

(** Write a variable-length U64.t.  The top 2 bits of the first byte will indicate the length of the full value. *)
let appendvar (b:buffer_t) (offset:U32.t) (value:U64.t): ST U32.t
   (requires (fun _ -> (UInt32.v offset < (B.length b - 8))))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let ret =
    if U64.(value <^ 0x40UL) then (
      let v8 = Cast.uint64_to_uint8 value in
      append8 b offset v8
    ) else if U64.(value <^ 0x4000UL) then (
      let v16 = Cast.uint64_to_uint16 value in
      let v16 = U16.(v16 |^ 0x4000us) in
      append16 b offset v16
    ) else if U64.(value <^ 0x40000000UL) then (
      let v32 = Cast.uint64_to_uint32 value in
      let v32 = U32.(v32 |^ 0x80000000ul) in
      append32 b offset v32
    ) else if U64.(value <^ 0x4000000000000000UL) then (
      let v64 = U64.(value |^ 0xc000000000000000UL) in
      append64 b offset v64
    ) else failwith (of_literal "Value must be < 2^62")
    in
  pop_frame();
  ret

(** Given a value, determine the number of bytes its encoding requires *)
let encodedsize (value:U64.t): ST U32.t
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  if U64.(value <^ 0x40UL) then 1ul
  else if U64.(value <^ 0x4000UL) then 2ul
  else if U64.(value <^ 0x40000000UL) then 4ul
  else if U64.(value <^ 0x4000000000000000UL) then 8ul
  else failwith (of_literal "Value must be < 2^62")

(** Read a variable-length U64.t.  The top 2 bits of the first byte indicate the length of the full value. *)
let getvar (b:buffer_t) (offset:U32.t): ST (U64.t * U32.t)
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  push_frame();
  let firstbyte:U8.t = getu8 b offset in
  let len:U8.t = U8.(firstbyte &^ 0xc0uy) in
  let ret = (
    if len = 0x00uy then (
      let t64 = Cast.uint8_to_uint64 firstbyte in
      (t64, U32.(offset+^1ul))
    ) else if len = 0x40uy then (
      let t16 = getu16 b offset in
      let t16 = U16.(t16 &^ 0x3fffus) in
      let t64 = Cast.uint16_to_uint64 t16 in
      (t64, U32.(offset+^2ul))
    ) else if len = 0x80uy then (
      let t32 = getu32 b offset in
      let t32 = U32.(t32 &^ 0x3ffffffful) in
      let t64 = Cast.uint32_to_uint64 t32 in
      (t64, U32.(offset+^4ul))
    ) else (
      let t64 = getu64 b offset in
      let t64 = U64.(t64 &^ 0x3fffffffffffffffUL) in
      (t64, U32.(offset+^8ul))
    )
  ) in
  pop_frame();
  ret

(** Get a variable-length integer, or return failure if the read crosses the
   end of the buffer *)
let getvar_s (b:buffer_t) (length:U32.t) (offset:U32.t): ST (err (U64.t * U32.t))
   (requires (fun _ -> true))
   (ensures (fun _ _ _ -> true))
=
  firstbyte <-- (if U32.(offset <^ length) then
    return (getu8 b offset)
  else
    fail !$"Insufficient buffer"
    );
  let len:U8.t = U8.(firstbyte &^ 0xc0uy) in
  match len with
  | 0x00uy ->
    let nextoffset = U32.(offset+^1ul) in
    if U32.(nextoffset >^ length) then
      fail !$"Insufficient buffer"
    else (
      let t64 = Cast.uint8_to_uint64 firstbyte in
      return (t64, nextoffset)
      )
  | 0x40uy ->
    let nextoffset = U32.(offset+^2ul) in
    if U32.(nextoffset >^ length) then
      fail !$"Insufficient buffer"
    else (
      let t16 = getu16 b offset in
      let t16 = U16.(t16 &^ 0x3fffus) in
      let t64 = Cast.uint16_to_uint64 t16 in
      return (t64, nextoffset)
      )
  | 0x80uy ->
    let nextoffset = U32.(offset+^4ul) in
    if U32.(nextoffset >^ length) then
      fail !$"Insufficient buffer"
    else (
      let t32 = getu32 b offset in
      let t32 = U32.(t32 &^ 0x3ffffffful) in
      let t64 = Cast.uint32_to_uint64 t32 in
      return (t64, nextoffset)
      )
  | _ ->
    let nextoffset = U32.(offset+^8ul) in
    if U32.(nextoffset >^ length) then
      fail !$"Insufficient buffer"
    else (
      let t64 = getu64 b offset in
      let t64 = U64.(t64 &^ 0x3fffffffffffffffUL) in
      return (t64, nextoffset)
      )

(** Convert a C.String to a Prims.string.  This leaks onto the heap.  Do not use outside of
      debug logging code *)
 let rec cstring_to_string_internal (src:C.String.t) (offset:U32.t) (len:U32.t) (dst:string): Tot string
 =
   if offset = len then
     dst
   else (
     let c = C.String.get src offset in
     let cu8 = C.uint8_of_char c in
     let cf = FStar.Char.char_of_u32 (Cast.uint8_to_uint32 cu8) in
     let cs = FStar.String.string_of_char cf in
     let newdst = dst ^ cs in
     cstring_to_string_internal src U32.(offset+^1ul) len newdst
   )

(** Convert a C.String to a Prims.string.  This leaks onto the heap.  Do not use outside of
      debug logging code *)
let cstring_to_string (src:C.String.t):  Tot string
=
    let len = strlen src in
    cstring_to_string_internal src 0ul len ""

(** Extension to FStar.Printf to print C.String.t types *)
let parse_cstring : extension_parser =
  function
    | 'C' :: rest -> Some (MkExtension cstring_to_string, rest)
    | _ -> None

(** Extend FStar.Printf.sprintf to support %XC, which is a C.String.t type *)
inline_for_extraction
let csprintf = ext_sprintf parse_cstring
