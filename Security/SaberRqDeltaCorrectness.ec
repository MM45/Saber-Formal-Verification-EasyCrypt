(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr ZModP IntDiv StdOrder List.
(*---*) import IntOrder.

(* --- Local --- *)
require import SaberRqPreliminaries.
(*---*) import Saber_PKE.
(*---*) import Zp Rp Rp.ComRing Rp.BasePoly.
(*---*) import Zq Rq Rq.ComRing Rq.BasePoly. 
(*---*) import Zppq Rppq Rppq.ComRing Rppq.BasePoly.
(*---*) import Z2t R2t R2t.ComRing R2t.BasePoly.
(*---*) import Z2 R2 R2.ComRing R2.BasePoly.


(* ----------------------------------- *)
(*  Adversary Prototypes               *)
(* ----------------------------------- *)

module type Adv_Cor = {
   proc choose(pk : pkey, sk : skey) : plaintext
}.

(* ----------------------------------- *)
(*  Correctness Game                   *)
(* ----------------------------------- *)

module Correctness_Game (S : Scheme, A : Adv_Cor) = {
   proc main() : bool = {
      var m: plaintext;
      var m': plaintext option;
      var c: ciphertext;
      var pk: pkey;
      var sk: skey;
      
      (pk, sk) <@ S.kg();
      m <@ A.choose(pk, sk);
      c <@ S.enc(pk, m);
      m' <@ S.dec(sk, c);

      return (Some m = m');
   }
}.

(* Equivalence of Correctness Games with Regular and Alternative PKE Description *)
lemma eq_Correctness_Game_Reg_Alt (A <: Adv_Cor) :
  equiv[Correctness_Game(Saber_PKE_Scheme, A).main ~ Correctness_Game(Saber_PKE_Scheme_Alt, A).main 
        : ={glob A} ==> ={res}].
proof.
proc.
call eq_dec; call eq_enc; call (_ : true); call eq_kg.
by auto.
qed.

(* ----------------------------------- *)
(*  Error                              *)
(* ----------------------------------- *)

clone Matrix as Mat_int with
  type R    <- int,
    op size <- n.

type int_vec = Mat_int.vector.

(*---*) import Mat_Rp Mat_Rq Mat_int.

abbrev ( - ) (pv1 pv2 : Rq_vec) = pv1 + (- pv2).
  
op errorZq (z1 z2 : Zq) : Zq = z1 - z2.
op errorRq (p1 p2 : Rq) : Rq = p1 - p2.
op errorRqv (pv1 pv2 : Rq_vec) : Rq_vec = pv1 - pv2.

op interrorZq (z1 z2 : Zq) : int = `| Zq.asint z1 - Zq.asint z2 |.
op interrorRq (p1 p2 : Rq) : int_vec = offunv (fun (i : int) => interrorZq p1.[i] p2.[i]).
op interrorRqv (pv1 pv2 : Rq_vec) : int_vec list = mkseq (fun (i : int) => interrorRq pv1.[i] pv2.[i]) l.


(*
axiom errorRq_def (p1 p2 : Rq) : 
  exists (i : int), 
  (0 <= i < n => 
  errorRq p1 p2 = errorZq p1.[i] p2.[i] /\ 
  forall (j : int), 0 <= j < n => max (errorRq p1 p2) (errorZq p1.[j] p2.[j]) = errorRq p1 p2).
*)

op error_bq0 (s bq : Rq_vec) (_A : Rq_mat) : Rq_vec = errorRqv bq (_A *^ s).
op error_bq0' (s' bq' : Rq_vec) (_A : Rq_mat) : Rq_vec = errorRqv bq' ((trmx _A) *^ s').
op error_cmq0 (cmq v' m_dec: Rq) : Rq = errorRq cmq (v' + m_dec).

op interror_bq (s bq : Rq_vec) (_A : Rq_mat) : int_vec list = interrorRqv bq (_A *^ s).
op interror_bq' (s' bq' : Rq_vec) (_A : Rq_mat) : int_vec list = interrorRqv bq' ((trmx _A) *^ s').
op interror_cmq (cmq v' m_dec: Rq) : int_vec = interrorRq cmq (v' + m_dec).

op error_bq (_A : Rq_mat) (s : Rq_vec) : Rq_vec = 
  errorRqv (scaleRpv2Rqv (scaleRqv2Rpv (_A *^ s + h))) (_A *^ s).
op error_bq' (_A : Rq_mat) (s': Rq_vec) : Rq_vec = 
  errorRqv (scaleRpv2Rqv (scaleRqv2Rpv ((trmx _A) *^ s' + h))) ((trmx _A) *^ s').

op v_expression (_A : Rq_mat) (s s': Rq_vec) : Rq =
  let bq' = ((trmx _A) *^ s') + (error_bq' _A s') in 
  (dotp bq' s) + (upscaleRq h1 (eq - ep)).

op v'_expression (_A : Rq_mat) (s s': Rq_vec) : Rq =
  let bq = (_A *^ s) + (error_bq _A s) in
  (dotp bq s') + (upscaleRq h1 (eq - ep)).

op error_cmq (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v' = v'_expression _A s s' in
  errorRq (scaleR2t2Rq (scaleRq2R2t (v' + (scaleR22Rq m)))) (v' + (scaleR22Rq m)).

op cmq_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v' = v'_expression _A s s' in
  v' + (scaleR22Rq m) + error_cmq _A s s' m.

op m'_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 =
  let v = v_expression _A s s' in
  let cmq = cmq_expression _A s s' m in
  scaleRq2R2 (v - cmq + (upscaleRq h2 (eq - ep))).



(* 
bq <- scaleRpv2Rqv b;
b <- scaleRqv2Rpv (_A *^ s + h)
==>
bq <- scaleRpv2Rqv (scaleRqv2Rpv (_A *^ s + h))


bq' <- scaleRpv2Rqv b';
b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
==>
bq' <- scaleRpv2Rqv (scaleRqv2Rpv ((trmx _A) *^ s' + h));


cmq <- scaleR2t2Rq cm;
cm <- scaleRq2R2t (v' + (scaleR22Rq m_dec));
==>
cmq <- scaleR2t2Rq (scaleRq2R2t (v' + (scaleR22Rq m_dec)));

m' <- scaleRq2R2 (v - cmq + (upscaleRq h2 (eq - ep)))   
v <- (dotp bq' s) + (upscaleRq h1 (eq - ep))


*)
op error_expression () : 


