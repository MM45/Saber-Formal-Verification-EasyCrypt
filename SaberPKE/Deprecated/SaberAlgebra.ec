require import AllCore.
require (*--*) Matrix.

(* Rq: Zq[X]/(X^n + 1); q = 2^eq; n = 256 *)
type Rq.
clone Ring.ComRing as Rq with type t <- Rq.
clone Matrix as Mat_Rq with type R <- Rq.

(* Rp: Zp[X]/(X^n + 1); p = 2^ep; n = 256 *)
type Rp.
clone Ring.ComRing as Rp with type t <- Rp.
clone Matrix as Mat_Rp with type R <- Rp.
