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
(*---*) import Mat_Rp Mat_Rq.
(*---*) import Zp Rp Rp.ComRing Rp.BasePoly.
(*---*) import Zq Rq Rq.ComRing Rq.BasePoly. 
(*---*) import Zppq Rppq Rppq.ComRing Rppq.BasePoly.
(*---*) import Z2t R2t R2t.ComRing R2t.BasePoly.
(*---*) import Z2 R2 R2.ComRing R2.BasePoly.


(* ----------------------------------- *)
(*  General Properties                 *)
(* ----------------------------------- *)

(* --- Convenient Equalities --- *)
lemma eq_q2_2eq1 : q %/ 2 = 2 ^ (eq - 1).
proof.
by rewrite /q (_ :  2 ^ eq =  2 ^ (eq - 1) * 2) 2:mulzK 1:-{3}expr1 1:-exprD_nneg //; smt(ge3_eq).
qed.

lemma eq_q4_2eq2 : q %/ 4 = 2 ^ (eq - 2).
proof.
rewrite /q (_ :  2 ^ eq =  2 ^ (eq - 2) * 4) 2:mulzK //. 
by rewrite (_ : 4 = 2 ^ 2) 1:expr2 //-exprD_nneg; smt(ge3_eq).
qed.

lemma eq_q4t_2eqet2 : q %/ (4 * t) = 2 ^ (eq - et - 2).
proof.
rewrite /q /t (_ :  2 ^ eq =  2 ^ (eq - et - 2) * (4 * 2 ^ et)) 2:mulzK //.
+ rewrite 1:(_ : 4 = 2 ^ 2) 1:expr2 // -exprD_nneg 2:ge0_et // -exprD_nneg;
          1, 2:smt(ge0_et geet2_ep geep1_eq).
  by congr; ring.
+ by rewrite neq_ltz; right; rewrite mulr_gt0 2:expr_gt0.
qed.

lemma eq_q_14q_34q : q = q %/ 4 + 3 * (q %/ 4).
proof.
rewrite eq_q4_2eq2 -{1}(Ring.IntID.mulr1z (2 ^ (eq - 2))) intmulz mulzC -mulrDl /=. 
by rewrite (_  : 4 = 2 ^ 2) 1:expr2 // -exprD_nneg //; smt(ge3_eq).
qed.

lemma eq_q2_q4q4 : q %/ 2 = q %/ 4 + q %/ 4.
proof.
rewrite eq_q2_2eq1 eq_q4_2eq2 (_ : 2 ^ (eq - 1) = 2 * 2 ^ (eq - 2)).
+ rewrite -{2}expr1 -exprD_nneg; smt(ge3_eq).
by rewrite mulrC -intmulz mulr2z.
qed.

lemma eq_upscaleRqh2_q4minq4t : upscaleRq h2 (eq - ep) = q4_Rq - q4t_Rq.
proof.
rewrite /upscaleRq polyXnD1_sumN -(BigRq.XnD1CA.big_split) /=.
rewrite !(BigRq.XnD1CA.big_seq) &(BigRq.XnD1CA.eq_bigr) /= => i /mem_range rng_i.
rewrite -scaleN -scaleDl; congr.
rewrite /h2 rcoeffZ_sum //= /upscaleZq /upscale /shl -inzmodD !inzmodK -eq_inzmod /=.
rewrite modzMml (pmod_small (2 ^ (eq - et - 2))).
+ by rewrite /q expr_ge0 //= ltz_weexpn2l //; smt(geet2_ep geep1_eq ge3_eq ge0_et).
rewrite mulrBl -!exprD_nneg; first 4 smt(ge2_ep geet2_ep geep1_eq ge3_eq ge0_et).
have ->: ep - 2 + (eq - ep) = eq - 2 by ring.
by have ->: ep - et - 2 + (eq - ep) = eq - et - 2 by ring.
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

(* --- Relevant Matrix/Vector Properties --- *)
lemma dotpDl_N (pv1 pv2 pv3 : Rq_vec) :
  - dotp (pv1 + pv2) pv3 = - dotp pv1 pv3 - dotp pv2 pv3.
proof. by rewrite dotpDl opprD. qed.

lemma dotpDlxTvxv (_A : Rq_mat) (s s': Rq_vec) (err : Rq_vec) :
 (dotp (trmx _A *^ s' + err) s) = (dotp (_A *^ s) s' + dotp err s).
proof. by rewrite dotpDl dotpC mulmxTv -dotp_mulmxv. qed.

(* --- Relevant Scaling Properties --- *)
lemma scaleZ22Zq2Z2t2Zq_inv (z : Z2) : scaleZ2t2Zq (scaleZq2Z2t (scaleZ22Zq z)) = scaleZ22Zq z.
proof.
rewrite /scaleZ2t2Zq /scaleZq2Z2t /upscale /downscale /shl /shr !inzmodK /t -{2}(Ring.IntID.expr1 2)
        -exprD_nneg 2:ge0_et // (Ring.IntID.addrC 1 et) -eq_inzmod.
have: upscale (asint z) eq 1 = 0 \/ upscale (asint z) eq 1 = 2 ^ (eq - 1).
+ by move: (Z2_asint_values z); case => ->.
case => -> // @/q.
rewrite modz_pow2_mul; 2: do 2! congr; 2: rewrite -eqz_div 1:neq_ltz 1:expr_gt0 3:dvdz_exp2l //; 
        first 2 smt(ge0_et geet2_ep geep1_eq). 
by rewrite pmod_small 1:expr_ge0 2:ltz_weexpn2l; smt(ge3_eq).
qed.

(* --- Equivalences Regarding Ranges of Coefficients and Results of Scaling --- *)
(* - Integers - *)
lemma scaleZq2Z2_rng_zero (z : Zq) : 
  Zq.asint Zq.zero <= Zq.asint z < Zq.asint (Zq.inzmod (q %/ 2)) <=> scaleZq2Z2 z = Z2.zero.
proof.
rewrite eq_q2_2eq1 zeroE inzmodK pmod_small 1:expr_ge0 2:ltz_weexpn2l //; 1, 2, 3: smt(ge3_eq). 
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

lemma scaleZq2Z2_rng_zero_q4 (z : Zq) :
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint z \/ Zq.asint z < Zq.asint (Zq.inzmod (q %/ 4))
  <=> 
  scaleZq2Z2 (Zq.inzmod (q %/ 4) + z) = Z2.zero.
proof.
rewrite eq_minq4_q34_modq -scaleZq2Z2_rng_zero zeroE ge0_asint /= !inzmodK 2?pmod_small 
        3:(pmod_small (q %/ 2)).
+ by rewrite mulr_ge0 2:divz_ge0 3:expr_ge0 //= -(Ring.IntID.add0r (3 * (q %/ 4))) {2}eq_q_14q_34q
          ltz_add2r eq_q4_2eq2 expr_gt0.
+ by rewrite {1}eq_q4_2eq2 expr_ge0 //= ltz_divLR 2:ltr_pmulr 2:expr_gt0.
+ by rewrite {1}eq_q2_2eq1 expr_ge0 //= ltz_divLR 2:ltr_pmulr 2:expr_gt0.
split; first case.
+ move: (Zq.gtp_asint z) => ltq_z ge34q_z.
  pose x := q %/ 4 + asint z - q; have ->: q %/ 4 + asint z = q + x.
  - by rewrite /x; ring.
  have [ge0_x ltq2_x]: 0 <= x < q %/ 2; first split => @/x [|?].
  - by rewrite subr_ge0 {1}eq_q_14q_34q lez_add2l.
  - rewrite ltr_subl_addl addrC ltr_add // eq_q2_2eq1 eq_q4_2eq2 ltz_weexpn2l //; smt(ge3_eq).
  by rewrite modzDl !pmod_small 1:(ltr_trans (q %/ 2)) // ltz_divLR 2:ltr_pmulr 2:expr_gt0.
+ move: (Zq.ge0_asint z) => ge0_z ltq4_z.
  rewrite pmod_small 2:eq_q2_q4q4 2:ltr_add2l // addr_ge0 1:eq_q4_2eq2 1:expr_ge0 //=.
  by rewrite (ltr_trans (q  %/ 2)) 1:eq_q2_q4q4 1:ltz_add2l // ltz_divLR 2:ltr_pmulr 2:expr_gt0.
+ rewrite &(contraLR) negb_or -!ltzNge /= -!lezNgt /=; move: (Zq.rg_asint z).
  case => ge0_z ltq_z; case => ltq34_z geq2_z.
  rewrite eq_q2_q4q4 pmod_small 1:addr_ge0 1:divz_ge0 2:expr_ge0 //= 1:{2}eq_q_14q_34q 1:ltz_add2l //.
  by rewrite lez_add2l.
qed.

lemma scaleZq2Z2_DM_invl_extract_rng (z1 : Z2) (z2 : Zq) :
  Zq.asint Zq.zero <= Zq.asint z2 < Zq.asint (Zq.inzmod (q %/ 2)) 
  <=> 
  z1 = scaleZq2Z2 (scaleZ22Zq z1 + z2).
proof.
rewrite scaleZq2Z2_DM_invl (_ : (z1 = z1 + (scaleZq2Z2 z2)) <=> ((scaleZq2Z2 z2) = Z2.zero)).
+ split => equ.
  - by rewrite &(Z2.ZModpRing.addrI z1) Z2.ZModpRing.addr0 eq_sym.
  - by rewrite &(Z2.ZModpRing.addrI (- z1)) Z2.ZModpRing.addrA Z2.ZModpRing.addrC Z2.ZModpRing.subrr
               Z2.ZModpRing.add0r eq_sym.
+ by apply scaleZq2Z2_rng_zero.
qed.

(* - Polynomials - *)
lemma scaleRq2R2_rng_zero (p : Rq) : 
  (forall (i : int), 0 <= i < n => Zq.asint Zq.zero <= Zq.asint p.[i] < Zq.asint (Zq.inzmod (q %/ 2)))
  <=> 
  (scaleRq2R2 p = R2.zeroXnD1).
proof.
split => [coeff_rng|]; rewrite polyXnD1_eqP => [i rng_i| coeff_scale i rng_i]; 
         2: move: (coeff_scale i rng_i); rewrite rcoeffZ_sum //= rcoeff0 -scaleZq2Z2_rng_zero //. 
+ by apply (coeff_rng i rng_i).
qed.

lemma scaleRq2R2_rng_zero_q4 (p : Rq) :
  (forall (i : int), 0 <= i < n =>
   Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint p.[i] 
   \/ Zq.asint p.[i] < Zq.asint (Zq.inzmod (q %/ 4)))
  <=> 
  scaleRq2R2 (q4_Rq + p) = R2.zeroXnD1.
proof.
split => [coeff_rng|]; rewrite polyXnD1_eqP => [i rng_i| coeff_scale i rng_i];
         2: move: (coeff_scale i rng_i); rewrite rcoeffZ_sum //= (Rq.rcoeffD q4_Rq p) rcoeff0
         rcoeffZ_sum //= -/(Zq.Sub.insubd (2 ^ (eq - 2) %% q)) -/(Zq.inzmod ((2 ^ (eq - 2))))
         -eq_q4_2eq2 -(scaleZq2Z2_rng_zero_q4 p.[i]) //.
+ by apply (coeff_rng i rng_i).
qed.

lemma scaleRq2R2_DM_invl_extract_rng (p1 : R2) (p2 : Rq) :
  (forall (i : int), 0 <= i < n => 
   Zq.asint Zq.zero <= Zq.asint p2.[i] < Zq.asint (Zq.inzmod (q %/ 2)))
  <=>
  p1 = scaleRq2R2 (scaleR22Rq p1 + p2).
proof.
split => [coeff_rng|]; rewrite polyXnD1_eqP => [i rng_i| coeff_scale i rng_i];
         2: move: (coeff_scale i rng_i); rewrite rcoeffZ_sum //= rcoeffD rcoeffZ_sum //=
         -scaleZq2Z2_DM_invl_extract_rng //.
+ by apply (coeff_rng i rng_i).
qed.

(* ----------------------------------- *)
(*  Adversary Prototypes               *)
(* ----------------------------------- *)

module type Adv_Cor = {
   proc choose(pk : pkey, sk : skey) : plaintext
}.

axiom Adv_Cor_ll (A <: Adv_Cor) : islossless A.choose.

(* ----------------------------------- *)
(*  Correctness Game (FO Transform)    *)
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
lemma eqv_Correctness_Game_Reg_Alt (A <: Adv_Cor) :
  equiv[Correctness_Game(Saber_PKE_Scheme, A).main ~ Correctness_Game(Saber_PKE_Scheme_Alt, A).main 
        : ={glob A} ==> ={res}].
proof.
proc.
call eqv_dec; call eqv_enc; call (_ : true); call eqv_kg.
by auto.
qed.

lemma eq_Pr_Correctness_Game_Reg_Alt (A <: Adv_Cor) &m :
  Pr[Correctness_Game(Saber_PKE_Scheme, A).main() @ &m : res]
  =
  Pr[Correctness_Game(Saber_PKE_Scheme_Alt, A).main() @ &m : res].
proof. by byequiv (eqv_Correctness_Game_Reg_Alt A). qed.

(* ----------------------------------- *)
(*  Correctness Analysis               *)
(* ----------------------------------- *)
(* --- Errors and Expressions --- *)
op errorZq (z1 z2 : Zq) : Zq = z1 - z2.
op errorRq (p1 p2 : Rq) : Rq = p1 - p2.
op errorRqv (pv1 pv2 : Rq_vec) : Rq_vec = pv1 - pv2.

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
op error_cmq_centered (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq = 
  error_cmq _A s s' m + q4t_Rq.

op cmq_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v' = v'_expression _A s s' in
  v' + (scaleR22Rq m) + error_cmq _A s s' m.
op cmq_expression_centered (_A : Rq_mat) (s s': Rq_vec) (m : R2) =
  let v' = v'_expression _A s s' in
  v' + (scaleR22Rq m) + error_cmq_centered _A s s' m - q4t_Rq.

op error_cmq_nom  (_A : Rq_mat) (s s': Rq_vec) : Rq =
  let v' = v'_expression _A s s' in
  errorRq (scaleR2t2Rq (scaleRq2R2t v')) v'.
op error_cmq_nom_centered (_A : Rq_mat) (s s': Rq_vec) : Rq = 
  error_cmq_nom _A s s' + q4t_Rq.

op m'_expression_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq =
  let v = v_expression _A s s' in
  let cmq = cmq_expression _A s s' m in
  v - cmq + (upscaleRq h2 (eq - ep)).
op m'_expression (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 = 
  scaleRq2R2 (m'_expression_Rq _A s s' m).

op m'_expression_Rq_alt (_A : Rq_mat) (s s': Rq_vec) (m : R2) : Rq = 
  scaleR22Rq m + (q4_Rq + dotp (error_bq' _A s') s - dotp (error_bq _A s) s' 
  - error_cmq_centered _A s s' m).

op m'_expression_alt (_A : Rq_mat) (s s': Rq_vec) (m : R2) : R2 = 
  scaleRq2R2 (m'_expression_Rq_alt _A s s' m).

lemma eq_cmq_cmqcen  (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  cmq_expression _A s s' m = cmq_expression_centered _A s s' m.
proof. 
rewrite /cmq_expression /cmq_expression_centered /v'_expression /error_cmq_centered /error_cmq /=.
by ring.
qed.

lemma eq_errcmq_errcmqnom (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
  error_cmq _A s s' m = error_cmq_nom _A s s'.
proof.
rewrite /error_cmq /error_cmq_nom /errorRq /=.
have ->:
  scaleR2t2Rq (scaleRq2R2t (v'_expression _A s s' + scaleR22Rq m))
  =
  scaleR2t2Rq (scaleRq2R2t (v'_expression _A s s')) + scaleR22Rq m.
+ rewrite -BigRq.XnD1CA.big_split /=.
  have ->:
    (fun (i : int) => scaleZ2t2Zq (scaleRq2R2t (v'_expression _A s s')).[i] ** exp Rq.iX i +
     scaleZ22Zq m.[i] ** exp Rq.iX i)
    =
    (fun (i : int) => (scaleZ2t2Zq (scaleRq2R2t (v'_expression _A s s')).[i] + scaleZ22Zq m.[i])  
     ** exp Rq.iX i).
  - by rewrite fun_ext /(==) => x; rewrite scaleDl.
  rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //= !rcoeffZ_sum //= rcoeffD rcoeffZ_sum //=.
  rewrite scaleZq2Z2t_DM; first right; rewrite inzmodK /upscale /shl; move: (Z2_asint_values m.[i]). 
  case => -> /=; first apply dvdz0.
  - rewrite pmod_small 1:expr_ge0 2:ltz_weexpn2l 7:dvdz_exp2l; smt(ge0_et geet2_ep geep1_eq ge3_eq).
  by rewrite scaleZ2t2Zq_DM scaleZ22Zq2Z2t2Zq_inv. 
by ring.
qed.

lemma eq_expression_m'_m'_alt_Rq (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
   m'_expression_Rq _A s s' m = m'_expression_Rq_alt _A s s' m.
proof.
rewrite /m'_expression_Rq /m'_expression_Rq_alt /cmq_expression /v_expression /v'_expression
        /error_cmq_centered /=.
rewrite dotpDlxTvxv addrC eq_upscaleRqh2_q4minq4t scaleR22Rq_PN scaleR22Rq_N; ring.
by rewrite dotpDl_N mulrC mul1r2z {1}scaleR22Rq_PN scaleR22Rq_N; ring.
qed.

lemma eq_expression_m'_m'_alt (_A : Rq_mat) (s s': Rq_vec) (m : R2) :
   m'_expression _A s s' m = m'_expression_alt _A s s' m.
proof. by rewrite /m'_expression /m'_expression_alt eq_expression_m'_m'_alt_Rq. qed.

(* --- Delta-Related Errors, Predicates, Properties, and Game --- *)
(* Error With Probability Distribution That is Computed Exhaustively in Python Script *)
op delta_error (_A : Rq_mat) (s s' : Rq_vec) = 
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' - error_cmq_nom_centered _A s s'.

(* Error Equivalent to Previous Error, But Includes Message m *)
op delta_error_wm (_A : Rq_mat) (s s' : Rq_vec) (m : R2) = 
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' - error_cmq_centered _A s s' m.

(* Predicate That Checks Whether Coefficients are In Correctness Range that Gives Delta Bound *)
op coeffs_in_correctness_rng (p : Rq) = forall (i : int), 0 <= i < n =>
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint p.[i] \/ Zq.asint p.[i] < Zq.asint (Zq.inzmod (q %/ 4)).

(* Game Used to Represent Delta Bound for the Relevant Error to Have Coefficient in Correct Range *)
module Delta_Bound_Game = {
   proc main() : bool = {
      var sd: seed;
      var _A : Rq_mat;
      var s, s': Rq_vec;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      s' <$ dsmallRq_vec;

      return coeffs_in_correctness_rng (delta_error _A s s');
   }
}.

(* Define Delta Bound and State Delta-Correctness *)
op delta_bound : real.

axiom delta_correctness &m : 
  Pr[Delta_Bound_Game.main() @ &m : res] >= 1%r - delta_bound.

(* Equivalence of Delta Errors With and Without m *)
lemma eq_deltaerror_deltaerrorwm (_A : Rq_mat) (s s' : Rq_vec) (m : R2) :
   delta_error _A s s' = delta_error_wm _A s s' m.
proof. 
by rewrite /delta_error /delta_error_wm /error_cmq_nom_centered /error_cmq_centered 
           eq_errcmq_errcmqnom.
qed.

(* --- Proof of Equivalence of Correctness Game for Original Scheme and Delta-Bound Game --- *)
(* - Intermediate Game, Correctness Game in Terms of Error - *)
module Correctness_Game_Error (A : Adv_Cor) = {
   proc main() : bool = {
      var sd: seed;
      var _A: Rq_mat;
      var s, s': Rq_vec;
      var m: plaintext;
      
      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      m <@ A.choose(pk_encode_s (sd, scaleRqv2Rpv (_A *^ s + h)), sk_encode_s s);      
      s' <$ dsmallRq_vec;
     
      return (m_decode m = m'_expression _A s s' (m_decode m));
   }
}.

lemma eq_Pr_Corr_Error (A <: Adv_Cor) &m:
  Pr[Correctness_Game(Saber_PKE_Scheme_Alt, A).main() @ &m : res] 
  = 
  Pr[Correctness_Game_Error(A).main() @ &m : res].
proof.
byequiv => //.
proc; inline *.
wp; rnd; wp; call (_ : true); auto.
progress.
rewrite !pks_enc_dec_inv !cs_enc_dec_inv !sks_enc_dec_inv /=.
rewrite /m'_expression /m'_expression_Rq /cmq_expression /v_expression /v'_expression /= eq_sym.
pose a := dotp (trmx (gen sdL) *^ s'L + error_bq' (gen sdL) s'L) sL.
have ->: a = dotp (scaleRpv2Rqv (scaleRqv2Rpv (trmx (gen sdL) *^ s'L + h))) sL.
+ rewrite /a /error_bq' /errorRqv; congr. 
  by rewrite Mat_Rq.Vector.ZModule.addrCA Mat_Rq.Vector.ZModule.addrC Mat_Rq.Vector.ZModule.subrr
             Mat_Rq.Vector.ZModule.add0r.
rewrite eq_sym eq_iff; split => [{1}-> | resR_dec].
+ rewrite m_enc_dec_inv eq_sym; do 3! congr. 
  rewrite /error_cmq /v'_expression /error_bq /errorRqv /errorRq /=; ring.
  pose b:= gen sdL *^ sL + (scaleRpv2Rqv (scaleRqv2Rpv (gen sdL *^ sL + h)) - gen sdL *^ sL).
  have ->: b = (scaleRpv2Rqv (scaleRqv2Rpv (gen sdL *^ sL + h))); 2: by ring.
  - by rewrite /b Mat_Rq.Vector.ZModule.addrCA Mat_Rq.Vector.ZModule.addrC Mat_Rq.Vector.ZModule.subrr
               Mat_Rq.Vector.ZModule.add0r.
+ have: (injective m_decode); last apply; rewrite {1}resR_dec m_enc_dec_inv; do 3! congr.
  - by apply bij_inj; exists m_encode; rewrite m_enc_dec_inv m_dec_enc_inv.
  rewrite /error_cmq /v'_expression /error_bq /errorRqv /errorRq /=; ring.
  pose b:= gen sdL *^ sL + (scaleRpv2Rqv (scaleRqv2Rpv (gen sdL *^ sL + h)) - gen sdL *^ sL).
  have ->: b = (scaleRpv2Rqv (scaleRqv2Rpv (gen sdL *^ sL + h))); 2: by ring.
  - by rewrite /b Mat_Rq.Vector.ZModule.addrCA Mat_Rq.Vector.ZModule.addrC Mat_Rq.Vector.ZModule.subrr
               Mat_Rq.Vector.ZModule.add0r.
qed.

lemma eq_returns_Error_Delta (_A : Rq_mat) (s s' : Rq_vec) (m : R2) :
  (m = m'_expression _A s s' m) = coeffs_in_correctness_rng (delta_error _A s s').
proof.
rewrite /coeffs_in_correctness_rng scaleRq2R2_rng_zero_q4 eq_expression_m'_m'_alt
        (eq_deltaerror_deltaerrorwm _ _ _ m) /delta_error_wm. 
rewrite /m'_expression_alt /m'_expression_Rq_alt scaleRq2R2_DM_invl eq_iff.
split => [eqm_merr | coeffs_corr].
+ by rewrite eq_sym &(addrI m) addr0 {1}eqm_merr; do 2! congr; ring.
+ by rewrite &(addrI (- m)) addrC subrr addrCA addrA subrr add0r -coeffs_corr; congr; ring.
qed.

lemma eq_Pr_Error_Delta (A <: Adv_Cor) &m:
  Pr[Correctness_Game_Error(A).main() @ &m : res] 
  = 
  Pr[Delta_Bound_Game.main() @ &m : res].
proof.
byequiv => //.
proc.
wp; rnd; call {1} (_ : true ==> true); auto; first apply (Adv_Cor_ll A).
progress.
by rewrite eq_returns_Error_Delta. 
qed.

lemma delta_correctness_original_scheme (A <: Adv_Cor) &m :
  Pr[Correctness_Game(Saber_PKE_Scheme, A).main() @ &m : res] >= 1%r - delta_bound.
proof.
rewrite (eq_Pr_Correctness_Game_Reg_Alt A) (eq_Pr_Corr_Error A) (eq_Pr_Error_Delta  A).
by apply delta_correctness.
qed.

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
   < -q/2 m = q/2 m > 
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
