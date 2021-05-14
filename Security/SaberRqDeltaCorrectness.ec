pragma Goals:printall.

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
(*
clone Matrix as Mat_int with
  type R    <- int,
    op size <- n.

type int_vec = Mat_int.vector.
*)
(*---*) import Mat_Rp Mat_Rq.

abbrev ( - ) (pv1 pv2 : Rq_vec) = pv1 + (- pv2).
  
op errorZq (z1 z2 : Zq) : Zq = z1 - z2.
op errorRq (p1 p2 : Rq) : Rq = p1 - p2.
op errorRqv (pv1 pv2 : Rq_vec) : Rq_vec = pv1 - pv2.

(*
op interrorZq (z1 z2 : Zq) : int = `| Zq.asint z1 - Zq.asint z2 |.
op interrorRq (p1 p2 : Rq) : int_vec = offunv (fun (i : int) => interrorZq p1.[i] p2.[i]).
op interrorRqv (pv1 pv2 : Rq_vec) : int_vec list = mkseq (fun (i : int) => interrorRq pv1.[i] pv2.[i]) l.
*)


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

(*
op interror_bq (s bq : Rq_vec) (_A : Rq_mat) : int_vec list = interrorRqv bq (_A *^ s).
op interror_bq' (s' bq' : Rq_vec) (_A : Rq_mat) : int_vec list = interrorRqv bq' ((trmx _A) *^ s').
op interror_cmq (cmq v' m_dec: Rq) : int_vec = interrorRq cmq (v' + m_dec).
*)
const poly_q4 : Rq =
  (BigRq.XnD1CA.bigi predT (fun (i : int) => Zq.inzmod (2 ^ (eq - 2)) ** exp Rq.iX i) 0 n).
const poly_q4t : Rq =
  (BigRq.XnD1CA.bigi predT (fun (i : int) => Zq.inzmod (2 ^ (eq - et - 2)) ** exp Rq.iX i) 0 n).


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

(* Add q / 4t to make error centered around zero *)
op error_cmq_centered (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq = 
  error_cmq _A s s' m + poly_q4t.

op cmq_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v' = v'_expression _A s s' in
  v' + (scaleR22Rq m) + error_cmq _A s s' m.

op cmq_expression_centered (_A : Rq_mat) (s s': Rq_vec) (m : R2) =
  let v' = v'_expression _A s s' in
  v' + (scaleR22Rq m) + error_cmq_centered _A s s' m - poly_q4t.

lemma eq_cmq_cmqcen  (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  cmq_expression _A s s' m = cmq_expression_centered _A s s' m.
proof. 
rewrite /cmq_expression /cmq_expression_centered /v'_expression /error_cmq_centered /error_cmq /=.
by ring.
qed.

op m'_expression_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v = v_expression _A s s' in
  let cmq = cmq_expression _A s s' m in
  v - cmq + (upscaleRq h2 (eq - ep)).

op m'_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 = scaleRq2R2 (m'_expression_Rq _A s s' m).

op m'_expression_Rq_reduced1 (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
   scaleR22Rq m + dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
   - error_cmq _A s s' m + upscaleRq h2 (eq - ep).

op m'_expression_Rq_reduced2 (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
   Rq = scaleR22Rq m + dotp (error_bq' _A s') s - dotp (error_bq _A s)
   s' - error_cmq_centered _A s s' m + poly_q4.

op m'_expression_Rq_fin (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq = 
  scaleR22Rq m + (poly_q4 + dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
  - error_cmq_centered _A s s' m).

op m'_expression_fin (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 = 
  scaleRq2R2 (m'_expression_Rq_fin _A s s' m).


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

lemma dotp_prop1 (_A : Rq_mat) (s s' err: Rq_vec) :
 (dotp (trmx _A *^ s' + err) s) = (dotp (_A *^ s) s' + dotp err s).
proof. by rewrite dotpDl dotpC mulmxTv -dotp_mulmxv. qed.

lemma dotp_red (_A : Rq_mat) (s s': Rq_vec) (err err': Rq_vec) :
  (dotp (trmx _A *^ s' + err') s) - (dotp (_A *^ s + err) s')
  =
  dotp err' s - dotp err s'.
proof.
rewrite dotp_prop1 addrC. rewrite dotpDl.
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

(*
op m'_expression_reduced_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
   scaleR22Rq m + dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
   - error_cmq _A s s' m + upscaleRq h2 (eq - ep).

op m'_expression_reduced (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 =
  scaleRq2R2 (
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
  - scaleR22Rq m - error_cmq _A s s' m + upscaleRq h2 (eq - ep)).
*)


lemma eq_m'_m'red1_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression_Rq _A s s' m =  m'_expression_Rq_reduced1 _A s s' m.
proof.
rewrite /m'_expression_Rq /m'_expression_Rq_reduced1 /v_expression /cmq_expression.
rewrite /v'_expression /=.
congr.
rewrite dotp_prop1. 
rewrite 3!opprD. 
rewrite addrA. 
congr.
rewrite eq_sym.
rewrite -addrA.
rewrite addrC.
rewrite -(dotp_red _A s s' ((error_bq _A s)) ((error_bq' _A s'))).
rewrite dotp_prop1.
rewrite {1}scaleR22Rq_PN.
rewrite scaleR22Rq_N.
by ring.
qed.



lemma eq_m'red1_m'red2_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression_Rq_reduced1 _A s s' m = m'_expression_Rq_reduced2 _A s s' m.
proof.
rewrite /m'_expression_Rq_reduced1 / m'_expression_Rq_reduced2.
rewrite /error_cmq_centered /error_cmq /=.
ring.
rewrite &(Rq.ComRing.addrI poly_q4) addrA addrA Rq.ComRing.subrr -Rq.ComRing.addrA. 
rewrite Rq.ComRing.add0r. 
rewrite Rq.ComRing.ofint0 Rq.ComRing.addr0.
rewrite Rq.ComRing.addrC &(Rq.ComRing.addIr (- poly_q4t)).
rewrite -Rq.ComRing.addrA.
rewrite Rq.ComRing.addrC.
rewrite Rq.ComRing.subrr Rq.ComRing.add0r.
rewrite /upscaleRq /upscaleZq /upscale /shl.
rewrite polyXnD1_eqP => i rng_i.
rewrite rcoeffZ_sum //=.
rewrite rcoeffZ_sum //=.
rewrite !inzmodK. 
rewrite /poly_q4 /poly_q4t. 
rewrite polyXnD1_sumN /=.
rewrite -BigRq.XnD1CA.big_split /=.
have ->:
(fun (i0 : int) =>
       ((inzmod (2 ^ (eq - 2)))%Zq ** exp Rq.iX i0 -
        (inzmod (2 ^ (eq - et - 2)))%Zq ** exp Rq.iX i0))
=
(fun (i0 : int) =>
       ((inzmod (2 ^ (eq - 2)))%Zq -
        (inzmod (2 ^ (eq - et - 2))))%Zq ** exp Rq.iX i0).
rewrite fun_ext /( == ) => x.
rewrite scaleDl.
by rewrite scaleN.
rewrite rcoeffZ_sum //=.
rewrite -eq_inzmod.
rewrite oppE. rewrite !inzmodK. 
rewrite modzNm.
rewrite modzDm.
rewrite modzMml.
rewrite mulrBl.
rewrite -!exprD_nneg; 1, 2, 3, 4: smt(ge2_ep geep1_eq geet2_ep).
congr. congr. congr. congr.
ring.
congr. congr.
ring.
qed.

lemma eq_m'red2_m'fin_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression_Rq_reduced2 _A s s' m = m'_expression_Rq_fin _A s s' m.
proof.
rewrite /m'_expression_Rq_reduced2 /m'_expression_Rq_fin. 
by ring.
qed.

lemma eq_m'_m'fin_Rq  (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression_Rq _A s s' m = m'_expression_Rq_fin _A s s' m.
proof.
by rewrite eq_m'_m'red1_Rq eq_m'red1_m'red2_Rq eq_m'red2_m'fin_Rq.
qed.


lemma eq_m'_m'fin (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression _A s s' m = m'_expression_fin _A s s' m.
proof.
by rewrite /m'_expression /m'_expression_fin eq_m'_m'fin_Rq.
qed.


(* Error Game

module Correctness_Error_Game (S : Scheme, A : Adv_Cor) = {
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
*)

lemma Z2_asint_values (z : Z2) : asint z = 0 \/ asint z = 1.
proof. 
case (asint z = 0) => [-> //| /= /neq_ltz].
case; move: (Z2.rg_asint z); case => [/lezNgt //| _].
by rewrite -!lez_add1r -(lez_add2l (-1)) /= eqz_leq => -> ->.
qed.

lemma scaleZ22Zq_scaleZq2Z2_inv (z : Z2) : scaleZq2Z2 (scaleZ22Zq z) = z.
proof. 
rewrite /scaleZq2Z2 /scaleZ22Zq /downscale /upscale /shr /shl inzmodK /q modz_pow2_div;
        1, 2: smt(mulr_ge0 expr_ge0 Z2.ge0_asint ge3_eq).
by rewrite mulzK 2:opprD 2:addzA /= 2:expr1 2:-inzmodK 2:!asintK // neq_ltz; right; rewrite expr_gt0.
qed.

lemma scaleR22Rq_scaleRq2R2_inv (p : R2) : scaleRq2R2 (scaleR22Rq p) = p.
proof. 
by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= rcoeffZ_sum //= scaleZ22Zq_scaleZq2Z2_inv.
qed.

lemma extr_m_m'_Zq (m : Z2) (err : Zq) : scaleZq2Z2 (scaleZ22Zq m + err) = m + scaleZq2Z2 err.
proof. 
rewrite scaleZq2Z2_DM 2:scaleZ22Zq_scaleZq2Z2_inv //; left.
rewrite /scaleZ22Zq /upscale /shl inzmodK pmod_small 2:dvdz_mull 2:dvdzz.
move: (Z2_asint_values m); case => -> /= @/q.
+ by rewrite expr_gt0.
+ by rewrite expr_ge0 //= ltz_weexpn2l; smt(ge3_eq).
qed.

lemma extr_m_m'_Rq (m : R2) (err : Rq) : scaleRq2R2 (scaleR22Rq m + err) = m + scaleRq2R2 err.
proof.
rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= 2!rcoeffD. 
by rewrite rcoeffZ_sum //= rcoeffZ_sum //=  extr_m_m'_Zq.
qed.

lemma eqv_q2_2eq1 : q %/ 2 = 2 ^ (eq - 1).
proof.
by rewrite /q (_ :  2 ^ eq =  2 ^ (eq - 1) * 2) 2:mulzK 1:-{3}expr1 1:-exprD_nneg //; smt(ge3_eq).
qed.

lemma eqv_q4_2eq2 : q %/ 4 = 2 ^ (eq - 2).
proof.
rewrite /q (_ :  2 ^ eq =  2 ^ (eq - 2) * 4) 2:mulzK //. 
by rewrite (_ : 4 = 2 ^ 2) 1:expr2 //-exprD_nneg; smt(ge3_eq).
qed.

lemma eqv_q4t_2eqet2 : q %/ (4 * t) = 2 ^ (eq - et - 2).
proof.
rewrite /q /t (_ :  2 ^ eq =  2 ^ (eq - et - 2) * (4 * 2 ^ et)) 2:mulzK //.
+ rewrite 1:(_ : 4 = 2 ^ 2) 1:expr2 // -exprD_nneg 2:ge0_et // -exprD_nneg;
          1, 2:smt(ge0_et geet2_ep geep1_eq).
  by congr; ring.
+ by rewrite neq_ltz; right; rewrite mulr_gt0 2:expr_gt0.
qed.

lemma scaleZq2Z2_rng_zero (z : Zq) : 
  Zq.asint Zq.zero <= Zq.asint z < Zq.asint (Zq.inzmod (q %/ 2)) <=> scaleZq2Z2 z = Z2.zero.
proof.
rewrite eqv_q2_2eq1 zeroE inzmodK pmod_small 1:expr_ge0 2:ltz_weexpn2l //; 1, 2, 3: smt(ge3_eq). 
split => [|eq0_scale].
+ by case => [ge0_z ltq2_z @/scaleZq2Z2 @/downscale @/shr]; rewrite pdiv_small.  
+ split => [|?].
  - by rewrite Zq.ge0_asint.
  - move: eq0_scale; rewrite &(contraLR) ltzNge /=; move: (Zq.gtp_asint z) => @/q ltq_z geq2_z.
    have ->: (scaleZq2Z2 z <> Z2.zero) = (scaleZq2Z2 z = Z2.one).
    * move: (Z2_asint_values (scaleZq2Z2 z)); rewrite -zeroE -oneE 2!asint_eq.
      case => -> /=; rewrite -eq_inzmod //.    
    rewrite /scaleZq2Z2 /downscale /shr -eq_inzmod; do 2! congr.
    rewrite eqz_leq -(ler_add2l 1) lez_add1r /= ltz_divLR 2:lez_divRL 1,2:expr_gt0 //=.
    by rewrite -{1}expr1 -exprD_nneg; 2: smt(ge3_eq).
qed.

lemma scaleRq2R2_rng_zero (p : Rq) : 
  (forall (i : int), 0 <= i < n => Zq.asint Zq.zero <= Zq.asint p.[i] < Zq.asint (Zq.inzmod (q %/ 2)))
  <=> 
  (scaleRq2R2 p = R2.zeroXnD1).
proof.
split => [coeff_rng|]; rewrite polyXnD1_eqP => [i rng_i| coeff_scale i rng_i]; 
         2: move: (coeff_scale i rng_i); rewrite rcoeffZ_sum //= rcoeff0 -scaleZq2Z2_rng_zero //. 
+ by apply (coeff_rng i rng_i).
qed.

lemma correct_errrng_Zq (m : Z2) (err : Zq) :
  Zq.asint Zq.zero <= Zq.asint err < Zq.asint (Zq.inzmod (q %/ 2)) 
  <=> 
  m = scaleZq2Z2 (scaleZ22Zq m + err).
proof.
rewrite extr_m_m'_Zq (_ : (m = m + (scaleZq2Z2 err)) <=> ((scaleZq2Z2 err) = Z2.zero)); last first.
+ by apply scaleZq2Z2_rng_zero.
+ split => equ.
  - by rewrite &(Z2.ZModpRing.addrI m) Z2.ZModpRing.addr0 eq_sym.
  - by rewrite &(Z2.ZModpRing.addrI (- m)) Z2.ZModpRing.addrA Z2.ZModpRing.addrC Z2.ZModpRing.subrr
               Z2.ZModpRing.add0r eq_sym.
qed.

lemma correct_errrng_Rq (m : R2) (err : Rq) :
  (forall (i : int), 0 <= i < n => 
   Zq.asint Zq.zero <= Zq.asint err.[i] < Zq.asint (Zq.inzmod (q %/ 2)))
  <=>
  m = scaleRq2R2 (scaleR22Rq m + err).
proof.
split => [coeff_rng|]; rewrite polyXnD1_eqP => [i rng_i| coeff_scale i rng_i];
         2: move: (coeff_scale i rng_i); rewrite rcoeffZ_sum //= rcoeffD rcoeffZ_sum //=
         -correct_errrng_Zq //.
+ by apply (coeff_rng i rng_i).
qed.

lemma eq_minq4_q34_modq : Zq.inzmod (- q %/ 4) = Zq.inzmod (3 * (q %/ 4)).
proof.
rewrite -eq_inzmod /q {1 3}(_ : 2 ^ eq = 2 ^ (eq - 2) * 4) 1:(_ : 4 = 2 ^ 2) 1:expr2 // 1:-exprD_nneg;
        1, 2, 3: smt(ge3_eq).
rewrite !mulzK // modNz 1,2:expr_gt0 // !pmod_small.
+ by rewrite -(lez_add2r 1) /= exprn_ege1 //= 2:-(ltz_add2r 1) /= 2:-(Ring.IntID.addr0 (2 ^ (eq - 2)))
            2:ltr_add 2:ltz_weexpn2l //=; smt(ge3_eq).
+ by rewrite mulr_ge0 2:expr_ge0 //= (_ : 2 ^ eq = 4 * 2 ^ (eq - 2)) 1:(_ : 4 = 2 ^ 2)
            1:expr2 // 1:-exprD_nneg 4:ltr_pmul2r 4:expr_gt0 //; smt(ge3_eq).
rewrite opprD /= addrA; ring; rewrite mulNr (_ : 4 = 2 ^ 2) 1:expr2 // -exprD_nneg; 1, 2: smt(ge3_eq).
by rewrite addzA (addzC _ (-2)) addzA.
qed.

lemma eq_q_14q_34q : q = q %/ 4 + 3 * (q %/ 4).
proof.
rewrite eqv_q4_2eq2 -{1}(Ring.IntID.mulr1z (2 ^ (eq - 2))) intmulz mulzC -mulrDl /=. 
by rewrite (_  : 4 = 2 ^ 2) 1:expr2 // -exprD_nneg //; smt(ge3_eq).
qed.

(*
lemma scaleZq2Z2_rng_zero (z : Zq) : 
  0 <= Zq.asint z < q %/ 2 <=> scaleZq2Z2 z = Z2.zero.
*)
lemma scaleZq2Z2_rng_zero_q4 (err : Zq) :
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint err \/ Zq.asint err < Zq.asint (Zq.inzmod (q %/ 4))
  <=> 
  scaleZq2Z2 (Zq.inzmod (q %/ 4) + err) = Z2.zero.
proof.
rewrite eq_minq4_q34_modq.
rewrite -scaleZq2Z2_rng_zero.
rewrite eqv_q4_2eq2.
split.
rewrite zeroE ge0_asint /=.
case.
rewrite inzmodK.
rewrite pmod_small.
by rewrite mulr_ge0 2:expr_ge0 //= mulrC eq_q_14q_34q eqv_q4_2eq2 mulzC ltz_addr expr_gt0.
move: (Zq.gtp_asint err) => @/q ltq_err ge34q_err.
  rewrite eqv_q2_2eq1.
  rewrite addE !inzmodK modzDml.
  have tt: exists (x : int), 0 <= x < 2 ^ (eq - 1) /\ 2 ^ (eq - 2) + asint err = q + x.
  exists (2 ^ (eq - 2) + asint err - q). split. split.
  - by rewrite -(lez_add2r q) -addzA /= eq_q_14q_34q eqv_q4_2eq2 lez_add2l.
  - move => ?.
    rewrite eq_q_14q_34q eqv_q4_2eq2 opprD addzA.
    smt. smt.
  move: tt. elim => x. case; case => ge0_x ltq2_x ->.
  rewrite modzDl !pmod_small 1:ge0_x 2:expr_ge0 //= 1:(ltz_trans (2 ^ (eq - 1))) //
          /q (_ : 2 ^ eq = 2 ^ (eq - 1) * 2 ^ 1) 1,3: -exprD_nneg //= 2,4:ltr_pmulr 2,5:expr_gt0
          3,6:expr1; smt(ge3_eq).

rewrite inzmodK pmod_small. smt.
move: (Zq.ge0_asint err) => ge0_err ltq4_err.
rewrite addE !inzmodK.
rewrite (pmod_small (2 ^ (eq - 2))) 1:expr_ge0 //=. smt.
rewrite !pmod_small. smt. smt.
rewrite eqv_q2_2eq1 (_ : 2 ^ (eq - 1) = 2 * 2 ^ (eq - 2)) 1:-{2}expr1 1:-exprD_nneg //; 1:smt(ge3_eq).
rewrite mulrC -intmulz mulr2z ltr_add2l //.

rewrite !addE !inzmodK //= (pmod_small (2 ^ (eq - 2))) 2:(pmod_small (q %/ 2)) 3:(pmod_small (3 * 2 ^ (eq - 2))); 1,2,3: smt.
rewrite &(contraLR) andaE negb_or negb_and -!ltzNge /= -!lezNgt /=.
case. move: (Zq.rg_asint err); case => ge0_err ltq_err ltq34_err geq2_err.
right.
rewrite pmod_small.
rewrite addr_ge0 1:expr_ge0 2:ge0_asint //=.
rewrite eq_q_14q_34q eqv_q4_2eq2 ltr_add2l //.
rewrite (_ : q %/ 2 = 2 ^ (eq - 2) + 2 ^ (eq - 2)).
rewrite eqv_q2_2eq1 -mulr2z intmulz -{4}expr1 -exprD_nneg //=; 1: smt(ge3_eq).
by rewrite lez_add2l.
qed.

lemma scaleRq2R2_rng_zero_q4 (err : Rq) :
  (forall (i : int), 0 <= i < n =>
   Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint err.[i] 
   \/ Zq.asint err.[i] < Zq.asint (Zq.inzmod (q %/ 4)))
  <=> 
  scaleRq2R2 (poly_q4 + err) = R2.zeroXnD1.
proof.
split => [coeff_rng|]; rewrite polyXnD1_eqP => [i rng_i| coeff_scale i rng_i];
         2: move: (coeff_scale i rng_i); rewrite rcoeffZ_sum //= (Rq.rcoeffD poly_q4 err) rcoeff0
         rcoeffZ_sum //= -/(Zq.Sub.insubd (2 ^ (eq - 2) %% q)) -/(Zq.inzmod ((2 ^ (eq - 2))))
         -eqv_q4_2eq2 -(scaleZq2Z2_rng_zero_q4 err.[i]) //.
+ by apply (coeff_rng i rng_i).
qed.

op err_exp_fin (_A : Rq_mat) (s s' : Rq_vec) (m : R2) = 
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' - error_cmq_centered _A s s' m.

op coeff_in_min14q_14q_rng (p : Rq) = forall (i : int), 0 <= i < n =>
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint p.[i]  \/ 
  Zq.asint p.[i] < Zq.asint (Zq.inzmod (q %/ 4)).

(* Error Game *)
module Correctness_Error = {
   proc main(m : R2) : bool = {
      var sd: seed;
      var _A: Rq_mat;
      var s, s': Rq_vec;
      
      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      s' <$ dsmallRq_vec;
     
      return coeff_in_min14q_14q_rng (err_exp_fin _A s s' m);
   }
}.

op delta_bound : real.

axiom delta_correctness (msg : R2) &m : 
  Pr[Correctness_Error.main(msg) @ &m : !res] <= delta_bound.

module Correctness_Error_Game (A : Adv_Cor) = {
   proc main() : bool = {
      var sd: seed;
      var _A: Rq_mat;
      var s, s': Rq_vec;
      var m: plaintext;
      var pk: pkey;
      var sk: skey;
      var m_dec: R2;
      
      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      m <@ A.choose(pk_encode_s (sd, scaleRqv2Rpv (_A *^ s + h)), sk_encode_s s);      
      s' <$ dsmallRq_vec;
      m_dec <- m_decode m;
     
      return (m_dec = m'_expression _A s s' m_dec);
   }
}.
(*
lemma m_enc_bij : bijective m_encode.
rewrite
axiom m_dec_bij:
*)
lemma eq_corrgame_correrrgame (A <: Adv_Cor) &m:
 Pr[Correctness_Game(Saber_PKE_Scheme_Alt, A).main() @ &m : res] 
 = 
 Pr[Correctness_Error_Game(A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *.
wp.
rnd. 
wp.
call (_ : true).
wp.
rnd.
wp.
rnd.
skip.
progress.
rewrite !pks_enc_dec_inv !cs_enc_dec_inv !sks_enc_dec_inv /=.
rewrite /m'_expression /m'_expression_Rq /cmq_expression /v_expression /v'_expression /=.
rewrite (_ : (dotp (scaleRpv2Rqv (scaleRqv2Rpv (trmx (gen sdL) *^ s'L + h))) sL) 
             = (dotp (trmx (gen sdL) *^ s'L + error_bq' (gen sdL) s'L) sL)).
rewrite /error_bq' /errorRqv.
have -> //: (trmx (gen sdL) *^ s'L +
   (scaleRpv2Rqv (scaleRqv2Rpv (trmx (gen sdL) *^ s'L + h)) -
    trmx (gen sdL) *^ s'L)) =
  scaleRpv2Rqv (scaleRqv2Rpv (trmx (gen sdL) *^ s'L + h)).
by rewrite Mat_Rq.Vector.ZModule.addrA Mat_Rq.Vector.ZModule.addrAC Mat_Rq.Vector.ZModule.subrr
           Mat_Rq.Vector.ZModule.add0r.
rewrite (_ : scaleR2t2Rq
          (scaleRq2R2t
             (dotp (scaleRpv2Rqv (scaleRqv2Rpv (gen sdL *^ sL + h))) s'L +
              upscaleRq h1 (eq - ep) + scaleR22Rq (m_decode result_R))) =
(dotp (gen sdL *^ sL + error_bq (gen sdL) sL) s'L +
      upscaleRq h1 (eq - ep) + scaleR22Rq (m_decode result_R) +
      error_cmq (gen sdL) sL s'L (m_decode result_R))).
rewrite /error_cmq /v'_expression /error_bq /errorRqv /errorRq /=.
rewrite eq_sym.
apply (eq_trans _ 
((scaleR2t2Rq
   (scaleRq2R2t
      (dotp
         (gen sdL *^ sL +
          (scaleRpv2Rqv (scaleRqv2Rpv (gen sdL *^ sL + h)) - gen sdL *^ sL))
         s'L +
       upscaleRq h1 (eq - ep) + scaleR22Rq (m_decode result_R)))))); 1: by ring.
do 5! congr.
by rewrite Mat_Rq.Vector.ZModule.addrA Mat_Rq.Vector.ZModule.addrAC Mat_Rq.Vector.ZModule.subrr
           Mat_Rq.Vector.ZModule.add0r.
pose x := (scaleRq2R2
   ((dotp (trmx (gen sdL) *^ s'L + error_bq' (gen sdL) s'L) sL +
     upscaleRq h1 (eq - ep) -
     (dotp (gen sdL *^ sL + error_bq (gen sdL) sL) s'L +
      upscaleRq h1 (eq - ep) + scaleR22Rq (m_decode result_R) +
      error_cmq (gen sdL) sL s'L (m_decode result_R)))%Big.CR +
    upscaleRq h2 (eq - ep))).
have : (injective m_decode). apply bij_inj. exists m_encode. rewrite m_enc_dec_inv m_dec_enc_inv //.
move => h.
case (result_R = m_encode x) => [-> | neq_resx].
rewrite m_enc_dec_inv //.
rewrite /injective  in h.
move: (h result_R (m_encode x)). 
move /contra. rewrite neq_resx //= m_enc_dec_inv => -> //.
qed.

module Correctness_Error_Game2 (A : Adv_Cor) = {
   proc main() : bool = {
      var sd: seed;
      var _A: Rq_mat;
      var s, s': Rq_vec;
      var m: plaintext;
      var pk: pkey;
      var sk: skey;
      var m_dec: R2;
      
      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      m <@ A.choose(pk_encode_s (sd, scaleRqv2Rpv (_A *^ s + h)), sk_encode_s s);      
      s' <$ dsmallRq_vec;
      m_dec <- m_decode m;
     
      return coeff_in_min14q_14q_rng (err_exp_fin _A s s' m_dec);
   }
}.

lemma temp1 (_A : Rq_mat) (s s' : Rq_vec) (m : R2) : 
  (m = m + scaleRq2R2 (poly_q4 + dotp (error_bq' _A s') s - dotp (error_bq _A s) s' -
      error_cmq_centered _A s s' m))
   <=>
scaleRq2R2
  (poly_q4 + dotp (error_bq' _A s') s - dotp (error_bq _A s) s' -
   error_cmq_centered _A s s' m) = R2.zeroXnD1.
proof.
split => ?.
+ by rewrite eq_sym &(addrI m) addr0. 
+ by rewrite &(addrI (-m)) addrA addrC subrr add0r eq_sym.
qed.

lemma eq_results (_A : Rq_mat) (s s' : Rq_vec) (m : R2) :
(m = m'_expression _A s s' m) =
  coeff_in_min14q_14q_rng (err_exp_fin _A s s' m).
proof.
rewrite /coeff_in_min14q_14q_rng scaleRq2R2_rng_zero_q4.
rewrite eq_m'_m'fin.
rewrite /m'_expression_fin /m'_expression_Rq_fin extr_m_m'_Rq /err_exp_fin temp1.
rewrite (_ : (poly_q4 +
    (dotp (error_bq' _A s') s - dotp (error_bq _A s) s' -
     error_cmq_centered _A s s' m)) = (poly_q4 +
    dotp (error_bq' _A s') s - dotp (error_bq _A s) s' -
     error_cmq_centered _A s s' m)) //.
by ring.
qed.

lemma eq_correrrgame_correrrgame2 (A <: Adv_Cor) &m :
  Pr[Correctness_Error_Game(A).main() @ &m : res]
  =
  Pr[Correctness_Error_Game2(A).main() @ &m : res].
proof.
byequiv => //.
proc.
auto; call (_ : true); auto; progress.
by apply eq_results.
qed.

(*

(* --- Actual (Alternative Description) --- *)
module Saber_PKE_Scheme_Alt : Scheme = {
   proc kg() : pkey * skey = {
      var sd: seed;
      var _A: Rq_mat;
      var s: Rq_vec;
      var b: Rp_vec;
      
      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      b <- scaleRqv2Rpv (_A *^ s + h);
      
      return (pk_encode_s (sd, b), sk_encode_s s);
   }

   proc enc(pk: pkey, m: plaintext) : ciphertext = {
      var pk_dec: seed * Rp_vec;
      var m_dec: R2;

      var sd: seed;
      var _A: Rq_mat;
      var s': Rq_vec;
      var b, b': Rp_vec;
      var bq: Rq_vec;
      var v': Rq;
      var cm: R2t;
      
      m_dec <- m_decode m;
      pk_dec <- pk_decode_s pk;
      sd <- pk_dec.`1;
      b <- pk_dec.`2;
      _A <- gen sd;
      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      bq <- scaleRpv2Rqv b;
      v' <- (dotp bq s') + (upscaleRq h1 (eq - ep));
      cm <- scaleRq2R2t (v' + (scaleR22Rq m_dec));
      
      return c_encode_s (cm, b');
   }

   proc dec(sk: skey, c: ciphertext) : plaintext option = {
      var c_dec: R2t * Rp_vec;
      var cm: R2t;
      var cmq: Rq;
      var b': Rp_vec;
      var bq': Rq_vec;
      var v: Rq;
      var s: Rq_vec;
      var m': R2;

      c_dec <- c_decode_s c;
      s <- sk_decode_s sk;
      cm <- c_dec.`1;
      cmq <- scaleR2t2Rq cm;
      b' <- c_dec.`2;
      bq' <- scaleRpv2Rqv b';
      
      v <- (dotp bq' s) + (upscaleRq h1 (eq - ep));
      m' <- scaleRq2R2 (v - cmq + (upscaleRq h2 (eq - ep)));
      
      return Some (m_encode m');
   }
}.
*)
(*

lemma scaleZq2Z2_rng_zero_q4 (m : Z2) (err : Zq) :
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint err < Zq.asint (Zq.inzmod (q %/ 4))
  <=> 
  scaleZq2Z2 (Zq.inzmod (q %/ 4) + err) = Z2.zero.
proof.
rewrite eq_minq4_q34_modq.
rewrite -scaleZq2Z2_rng_zero.
rewrite eqv_q4_2eq2.
move: (Zq.rg_asint err); case => ge0_err ltq_err.
rewrite !inzmodK /= pmod_small 2:(pmod_small (2 ^ (eq - 2))) 3:(pmod_small (q %/ 2)); 1,2,3: smt.
split.
(* => *)
rewrite modz_ge0 1:neq_ltz 1:expr_gt0 //=.
case => ge34q_err ltq4_err.
  have: exists (x : int), 0 <= x < 2 ^ (eq - 1) /\ 2 ^ (eq - 2) + asint err = q + x.
  exists (2 ^ (eq - 2) + asint err - q). split. split.
  - by rewrite -(lez_add2r q) -addzA /= eq_q_14q_34q eqv_q4_2eq2 lez_add2l.
  - move => ?.
    rewrite eq_q_14q_34q eqv_q4_2eq2 opprD addzA. smt. smt.
elim => x; case; case => ge0_x ltq2_x ->.
rewrite eqv_q2_2eq1 modzDl !pmod_small 1:ge0_x //= 1:(ltz_trans (2 ^ (eq - 1))) //
        /q (_ : 2 ^ eq = 2 ^ (eq - 1) * 2 ^ 1) -exprD_nneg //=; smt(ge3_eq).
(* <= *)
rewrite &(contraLR) !andaE !negb_and -!lezNgt -!ltzNge.
case => [lt34q_err | geq4_err].
rewrite -(modzz q); left. 
right.
rewrite modz_ge0. 
=> ge0_q4err ltq2_q4err.

qed.

lemma correct_errrng_q4_Zq (m : Z2) (err : Zq) :
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint err \/ Zq.asint err < q %/ 4
  <=> 
  m = scaleZq2Z2 (scaleZ22Zq m + (Zq.inzmod (q %/ 4) + err)).
proof. admitted.


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



lemma correct_errrng_q4_Zq (m : Z2) (err : Zq) :
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint err \/ Zq.asint err < q %/ 4
  <=> 
  m = scaleZq2Z2 (scaleZ22Zq m + (Zq.inzmod (q %/ 4) + err)).
proof.
rewrite eq_minq4_q34_modq.
rewrite -correct_errrng_Zq !inzmodK. 
split. admit. 
(*1: case => [geq34_err ltq4_err].
+ have rng_errq4 : 0 <= q %/ 4 %% q + Zq.asint err < q %/ 2.
  - rewrite pmod_small.
    * by rewrite (_ : 4 = 2 ^ 2) 1:expr2 /q // divz_ge0 expr2 
                 2:expr_ge0 3:ltz_divLR 4:ltr_pmulr 4:expr_gt0.
    rewrite pmod_small in ltq4_err.
    * by rewrite /q lez_divRL 2:ltz_divLR //= expr_ge0 2:ltr_pmulr 2:expr_gt0.
    split => [|?].
    * by rewrite addr_ge0 1:divz_ge0 2:expr_ge0 3:Zq.ge0_asint.
    * rewrite (ltr_le_trans (q %/ 4 + q %/ 4)) 1:ltr_add2l // lez_eqVlt; left.
      rewrite /q -divzDl (_ : 4 = 2 ^ 2) 1,3,4:expr2 // 1:dvdz_exp2l; 1: smt(ge3_eq).
      rewrite eq_sym eqz_div // 1:-expr2 -mulr2z intmulz 1:-{4}expr1 1:-exprD_nneg 3:dvdz_exp2l;
              1, 2, 3: smt(ge3_eq).
    by rewrite mulrA divzK 1:-{1}expr1 1:dvdz_exp2l; smt(ge3_eq).
  split => [|?].
  - by rewrite modz_ge0 neq_ltz /q; right; apply expr_gt0.
  - rewrite pmod_small; first move: rng_errq4; case => -> ltq2_errq4 /=.
    * rewrite (ltr_trans (q %/2)) // ltz_divLR //#.
    by move: rng_errq4; case => ? ->.
*)
admit.
(*
case => ?. apply contraLR.
rewrite !andabP negb_or !negb_and Zq.gtp_asint Zq.ge0_asint /= lezNgt /= -!lezNgt.
case => ltq34_err geq4_err.
rewrite (pmod_small (q %/ 4)). admit.
rewrite pmod_small.
rewrite addr_ge0 2:ge0_asint 1:divz_ge0 2:expr_ge0 //=.
rewrite pmod_small in ltq34_err. admit.
rewrite (ltr_le_trans (q %/ 4 + 3 * q %/ 4)).
rewrite ltr_add2l //.
rewrite -divzDl. admit.
rewrite lez_divLR //.
rewrite mulrC -intmulz.
rewrite -mulrS //= intmulz.
rewrite dvdz_mull.
rewrite dvdzz.
rewrite mulrC -intmulz.
rewrite -mulrS //= intmulz.
rewrite lezz.
rewrite (_ : q %/ 2 = q %/ 4 + q %/ 4).
rewrite -mulr2z intmulz.
rewrite -eqz_mul // /q 1:-{1}expr1 1:dvdz_exp2l; 1:smt(ge3_eq).
rewrite mulzA /= eq_sym -dvdz_eq (_ : 4 = 2 ^ 2) 1:expr2 // dvdz_exp2l; 1:smt(ge3_eq).
rewrite lez_add2l //.
*)
qed.

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

lemma correct_errrng_q4_Rq (m : R2) (err : Rq) :
 (forall (i : int), 0 <= i < n => 
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint err.[i] \/ Zq.asint err.[i] < q %/ 4)
 <=> 
 (m = scaleRq2R2 (scaleR22Rq m + 
                 ((BigRq.XnD1CA.bigi predT (fun (i : int) => Zq.inzmod (q %/ 4) ** exp Rq.iX i) 0 n) +
                   err))).
proof.
split; rewrite polyXnD1_eqP => [coeff_errrng i rng_i | corr i rng_i]; 2: move: (corr i rng_i);
       rewrite rcoeffZ_sum //= 2!rcoeffD rcoeffZ_sum //= rcoeffZ_sum //=;
       rewrite -/(Zq.Sub.insubd (q %/ 4 %% q)) -/(Zq.inzmod (q %/ 4)).
+ by apply /correct_errrng_q4_Zq /(coeff_errrng i rng_i).
+ by rewrite (correct_errrng_q4_Zq m.[i] err.[i]).
qed.


op m'_expression_reduced_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
   scaleR22Rq m + dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
   - error_cmq _A s s' m + upscaleRq h2 (eq - ep).

op m'_expression_reduced (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 =
  scaleRq2R2 (
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
  - scaleR22Rq m - error_cmq _A s s' m + upscaleRq h2 (eq - ep)).

lemma test (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression _A s s' m = m'_expression_reduced _A s s' m.
proof.
rewrite /m'_expression /m'_expression_Rq /v_expression /cmq_expression 
        /v'_expression /m'_expression_reduced /=.
congr. 
congr.
ring.
rewrite addrC.
rewrite dotp_prop1.
ring.
rewrite dotpDl. ring.
qed.

lemma eq_m'exp_Rq  (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  m'_expression_Rq _A s s' m = m'_expression_reduced_Rq _A s s' m.
proof.
rewrite /m'_expression_Rq /m'_expression_reduced_Rq /v_expression /cmq_expression.
rewrite /v'_expression /=.
congr.
rewrite dotp_prop1. rewrite 3!opprD. rewrite addrA. 
congr.
rewrite eq_sym.
rewrite -addrA.
rewrite addrC.
rewrite -(dotp_red _A s s' ((error_bq _A s)) ((error_bq' _A s'))).
rewrite dotp_prop1.
rewrite {1}scaleR22Rq_PN.
rewrite scaleR22Rq_N.
by ring.
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
*)
