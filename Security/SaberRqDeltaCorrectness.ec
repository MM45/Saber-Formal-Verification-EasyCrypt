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

(* Add q / 4t to make error centered around zero *)
op error_cmq (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v' = v'_expression _A s s' in
  errorRq (scaleR2t2Rq (scaleRq2R2t (v' + (scaleR22Rq m)))) (v' + (scaleR22Rq m)).

op cmq_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v' = v'_expression _A s s' in
  v' + (scaleR22Rq m) + error_cmq _A s s' m.

op m'_expression_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v = v_expression _A s s' in
  let cmq = cmq_expression _A s s' m in
  v - cmq + (upscaleRq h2 (eq - ep)).

op m'_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 = scaleRq2R2 (m'_expression_Rq _A s s' m).

pragma Goals:printall.

lemma errrng_impl_correct_Zq (m : Z2) (err : Zq) :
  0 <= Zq.asint err < q %/ 2 => m = scaleZq2Z2 (scaleZ22Zq m + err).
proof.
+ case => [ge0_err @/q]; rewrite (_ : 2 ^ eq = 2 ^ (eq - 1) * 2) 2:mulzK // => [| ltq2_err].
  - by rewrite -{3}expr1 -exprD_nneg; smt(ge3_eq). 
  rewrite /scaleZq2Z2 /scaleZ22Zq /downscale /upscale /shr /shl !inzmodK modzDml /q modz_pow2_div;
          1, 2 : smt(Z2.ge0_asint Zq.ge0_asint addr_ge0 mulr_ge0 expr_ge0 ge3_eq).
  rewrite opprD addzA /= expr1 /inzmod modz_mod divzMDl; 1: rewrite neq_ltz expr_gt0 //=.
  have -> /=: asint err %/ 2 ^ (eq - 1) = 0 by rewrite pdiv_small.
  by rewrite -{1}asintK /inzmod.
qed.

lemma correct_impl_errrng_Zq (m : Z2) (err : Zq) :
   m = scaleZq2Z2 (scaleZ22Zq m + err) => 0 <= Zq.asint err < q %/ 2.
proof.
have h /h errd0: m = scaleZq2Z2 (scaleZ22Zq m + err) => Zq.asint err %/ 2 ^ (eq - 1) = 0; last first.
+ rewrite /q (_ : 2 ^ eq = 2 ^ (eq - 1) * 2) 2:mulzK //. 
  - rewrite -{3}expr1 -exprD_nneg; smt(ge3_eq).
  by rewrite -divz_eq0 in errd0; 1: rewrite expr_gt0 //.
+ rewrite /scaleZq2Z2 /scaleZ22Zq /downscale /upscale /shr /shl !inzmodK modzDml /q modz_pow2_div;
          1, 2 : smt(Z2.ge0_asint Zq.ge0_asint addr_ge0 mulr_ge0 expr_ge0 ge3_eq).
  rewrite opprD addzA /= expr1 /inzmod modz_mod divzMDl; 1: rewrite neq_ltz expr_gt0 //.
  rewrite -{1}asintK -eq_inzmod.
  case (asint err < 2 ^ (eq - 1)); [move: (Zq.ge0_asint err) | move: (Zq.gtp_asint err)]
       => [ge0_err ltq2_err _ | @/q ltq_err /lezNgt geq2_err].
  - by rewrite -divz_eq0 1:expr_gt0.  
  - have -> /=: asint err %/ 2 ^ (eq - 1) = 1.
    * rewrite eqz_leq -(ler_add2l 1) lez_add1r /= ltz_divLR 2:lez_divRL 1,2:expr_gt0 //=.
      rewrite -{1}expr1 -exprD_nneg //; smt(ge3_eq).
    move: (Z2.rg_asint m); rewrite andabP andbC -lez_add1r -(lez_add2r (-1)) /=; case => le1m ge0m.
    case (asint m = 0) => [-> //| /neq_ltz [/ltzNge // |]].
    * rewrite -lez_add1r /= => ge1m; have -> //: asint m = 1 by rewrite eqz_leq.
qed.

lemma correct_errrng_Zq (m : Z2) (err : Zq) :
 0 <= Zq.asint err < q %/ 2 <=> m = scaleZq2Z2 (scaleZ22Zq m + err).
proof. by split; [apply errrng_impl_correct_Zq | apply correct_impl_errrng_Zq]. qed.

lemma correct_errrng_Rq (m : R2) (err : Rq) :
 (forall (i : int), 0 <= i < n => 0 <= Zq.asint err.[i] < q %/ 2)
 <=> 
 (m = scaleRq2R2 (scaleR22Rq m + err)).
proof.
split; rewrite polyXnD1_eqP => [coeff_errrng i rng_i | corr i rng_i]; 2: move: (corr i rng_i);
       rewrite rcoeffZ_sum //= rcoeffD rcoeffZ_sum //=.
+ by move: (coeff_errrng i rng_i); apply errrng_impl_correct_Zq.
+ by apply correct_impl_errrng_Zq.
qed.

lemma test0 (_A : Rq_mat) (s s' err: Rq_vec) :
 (dotp (trmx _A *^ s' + err) s) = (dotp (_A *^ s) s' + dotp err s).
proof. by rewrite dotpDl dotpC mulmxTv -dotp_mulmxv. qed.

lemma test1 (_A : Rq_mat) (s s': Rq_vec) (err err': Rq_vec) :
  (dotp (trmx _A *^ s' + err') s) - (dotp (_A *^ s + err) s')
  =
  dotp err' s - dotp err s'.
proof.
rewrite test0 addrC. rewrite dotpDl.
pose dass' := dotp (_A *^ s) s'; pose derrs' := dotp err s'; pose derrs := dotp err' s.
rewrite addrC. 
rewrite eq_sym addrC. 
rewrite opprD. rewrite addrA. rewrite eq_sym. rewrite addrC.
rewrite &(Rq.ComRing.addrI derrs'). rewrite addrA eq_sym addrA. simplify.
rewrite subrr.
rewrite 2!add0r.
rewrite eq_sym -addrA addrC -addrA.
rewrite &(Rq.ComRing.addrI (-derrs)).
rewrite addrA.
rewrite addrC eq_sym addrC subrr addr0.
rewrite addrC eq_sym subr_eq0 //.
qed.

op m'_expression_reduced (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 =
  scaleRq2R2 (
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
  - scaleR22Rq m - error_cmq _A s s' m + upscaleRq h2 (eq - ep)).

instance ring with Rq
  op rzero = Rq.zeroXnD1
  op rone  = Rq.oneXnD1
  op add   = Rq.( + )
  op opp   = Rq.([-])
  op mul   = Rq.( * )
  op expr  = Rq.ComRing.exp
  op ofint = Rq.ComRing.ofint

  proof oner_neq0 by apply Rq.ComRing.oner_neq0
  proof addrA     by apply Rq.ComRing.addrA
  proof addrC     by apply Rq.ComRing.addrC
  proof addr0     by apply Rq.ComRing.addr0
  proof addrN     by apply Rq.ComRing.addrN
  proof mulr1     by apply Rq.ComRing.mulr1
  proof mulrA     by apply Rq.ComRing.mulrA
  proof mulrC     by apply Rq.ComRing.mulrC
  proof mulrDl    by apply Rq.ComRing.mulrDl
  proof expr0     by apply Rq.ComRing.expr0
  proof ofint0    by apply Rq.ComRing.ofint0
  proof ofint1    by apply Rq.ComRing.ofint1
  proof exprS     by apply Rq.ComRing.exprS
  proof ofintS    by apply Rq.ComRing.ofintS
  proof ofintN    by apply Rq.ComRing.ofintN.

lemma test (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression _A s s' m = m'_expression_reduced _A s s' m.
proof.
rewrite /m'_expression /m'_expression_Rq /v_expression /cmq_expression 
        /v'_expression /m'_expression_reduced /=.
congr. 
congr.
ring.
rewrite addrC.
rewrite test0.
ring.
rewrite dotpDl. ring.
qed.

lemma scaleZ22Zq_PN (z : Z2) : scaleZ22Zq z = scaleZ22Zq (- z).
proof.
rewrite /scaleZ22Zq /upscale /shl -eq_inzmod !inzmodK; do 3! congr.
case (asint z = 0) => [-> //| /neq_ltz [lt0_z | gt0_z]]; move: (Z2.rg_asint z); case => ge0_z lt2_z.
+ by rewrite ltzNge in lt0_z.
+ rewrite -lez_add1r -(lez_add2l (-1)) /= in lt2_z; rewrite -lez_add1r /= in gt0_z.
  by move: (eqz_leq (asint z) 1); rewrite gt0_z lt2_z /= => ->.
qed.

lemma scaleR22Rq_PN (p : R2) : scaleR22Rq p = scaleR22Rq (- p).
proof.
rewrite /scaleR22Rq !BigRq.XnD1CA.big_seq &(BigRq.XnD1CA.eq_bigr) /= => *.
by rewrite -rcoeffN scaleZ22Zq_PN.
qed.

lemma scaleZ22Zq_N (z : Z2) : scaleZ22Zq (- z) = - scaleZ22Zq z.
proof.
rewrite /scaleZ22Zq /upscale /shl -inzmodN oppE -eq_inzmod /q -modz_pow2_mul; 1: smt(ge3_eq).
rewrite expr1 modz_mod -{1}(Ring.IntID.expr1 2) modz_pow2_mul; 1: smt(ge3_eq).
by rewrite mulNr.
qed.

lemma scaleR22Rq_N (p : R2) : scaleR22Rq (- p) = - scaleR22Rq p.
proof.
rewrite /scaleR22Rq Rq.polyXnD1_sumN /= !BigRq.XnD1CA.big_seq &(BigRq.XnD1CA.eq_bigr) /= => *.
by rewrite -rcoeffN scaleZ22Zq_N scaleN.
qed.

(*
lemma test12 (_A : Rq_mat) (s s': Rq_vec) (m : R2):
  m = m'_expression _A s s' m.
proof.
rewrite test.
rewrite /m'_expression_reduced.
rewrite scaleRq2R2_DM.
rewrite /v_expression.
simplify.
rewrite /cmq_expression.
rewrite /v'_expression.
simplify.
have ->:
(dotp (_A *^ s) s' + dotp (error_bq' _A s') s + upscaleRq h1 (eq - ep) -
    (dotp (_A *^ s + error_bq _A s) s' + upscaleRq h1 (eq - ep) +
     scaleR22Rq m + error_cmq _A s s' m))
=
(dotp (_A *^ s) s' + dotp (error_bq' _A s') s + upscaleRq h1 (eq - ep) -
    dotp (_A *^ s + error_bq _A s) s' - upscaleRq h1 (eq - ep) -
     scaleR22Rq m + error_cmq _A s s' m).

have ->: (dotp (trmx _A *^ s' + error_bq' _A s') s = (dotp (_A *^ s) s' + dotp (error_bq' _A s') s)).
rewrite test0 //.
rewrite {1}test1.
qed.
 
lemma rel_m_m' (m : R2) (er : int):
 - (q %/ 4) <= er < q %/ 4 => m = scaleRq2R2 (scaleR22Rq m + Rq.inzmod er).
*)
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

(* Proof errors are correct (e.g., show that bq = As + error_bq)*)
(* 
u = bq - As
u' = bq' - ATs'
u'' = (cmq - (v' + q/2 m)) + q/4t
==>

(No scale) 
m' = v - cmq + q/p h2 
   = v - (v' + q/2 m + u'' - q/4t) + q/p h2
   = (bq' s + q/p h1) - (bq s' + q/p h1 + q/2 m + u'' - q/4t) + q/p h2
   = bq' s - bq s' - q/2 m - u'' + q/4t + q/p h2
   = (AT s' + u') s - (A s + u) s' - q/2 m - u'' + q/4t + q/p h2
   = u' s - u s' - q/2 m - u'' + q/4t + q/p h2
   = u' s - u s' + (- q/2 m) - u'' + q/4t + q/p h2 
   <- q/2 m = q/2 m> 
   = u' s - u s' + q/2 m - u'' + q/4t + q/p h2
   = q/2 m + u' s - u s' - u'' + q/4t + q/p h2
   = q/2 m + u' s - u s' - u'' + q/4t + q/p p/4 - q/p p/4t
   = q/2 m + u' s - u s' - u'' + q/4t + q/4 - q/4t
   = q/2 m + u' s - u s' - u'' + q/4

(With scale)
m' = scaleRq2R2 (q/2 m + u' s - u s' - u'' + q/4)
   = scaleRq2R2 (q/2 m) + scaleRq2R2 (u' s - u s' - u'' + q/4) 
   = m + scaleRq2R2 (u' s - u s' - u'' + q/4)

==>
m' = m iff 0 <= u' s - u s' - u'' + q/4 < q/2
==>
m' = m iff - q/4 <= u' s - u s' - u'' < q/4


*)
