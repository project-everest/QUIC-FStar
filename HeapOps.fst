module HeapOps

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

(** Convenience operator for ghostly dereferences *)
unfold
let (@) (p:B.pointer 'a) (h:HS.mem) : GTot 'a =
  B.get h p 0

(** Expose "live" without needing to say "B.live" *)
unfold
let live #t (h:HS.mem) (b:B.buffer t) : GTot Type0 = B.live h b

(** Make it easy to perform dereferences inside heap pre-conditions.

    Expected use case:
      heappre (fun h0 ( !* ) -> ...)
*)
unfold
let heappre (pre:(HS.mem -> ((#t:Type) -> B.pointer t -> GTot t) -> Type0)) (h0:HS.mem) : Type0 =
  pre h0 (fun #t b -> b@h0)
