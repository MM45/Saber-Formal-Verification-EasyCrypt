(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr ZModP IntDiv StdOrder List SmtMap.
(*---*) import IntOrder.
require (*--*) ROM.

(* --- Local --- *)
require import SaberPKEPreliminaries.
(*---*) import Saber_PKE.
(*---*) import Mat_Rp Mat_Rq.
(*---*) import Mat_Rq.Vector Mat_Rq.Vector.ZModule.
(*---*) import Zp Rp Rp.ComRing Rp.BasePoly.
(*---*) import Zq Rq Rq.ComRing Rq.BasePoly. 
(*---*) import Zppq Rppq Rppq.ComRing Rppq.BasePoly.
(*---*) import Z2t R2t R2t.ComRing R2t.BasePoly.
(*---*) import Z2 R2 R2.ComRing R2.BasePoly.

(* ----------------------------------- *)
(*  ROM                                *)
(* ----------------------------------- *)
clone import ROM as RO with
  type in_t  <= seed,
  type out_t <= Rq_mat,
    op dout  <= (fun (sd : seed) => dRq_mat).


clone import PKE_ROM as Saber_PKE_ROM with
  theory RO <- RO.

import Lazy.

module Gen = LRO.

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
          1, 2: smt(ge0_et geet2_ep geep1_eq).
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
module type Adv_Cor_ROM (RO : POracle) = {
   proc choose(pk : seed * Rp_vec, sk : Rq_vec) : R2
}.

(* ----------------------------------- *)
(*  Standard Correctness Definition    *)
(* ----------------------------------- *)
(*
In standard model:

module Correctness_Standard (S : Scheme) = {
   proc main(m : R2) : bool = {
      var m': R2 option;
      var c: R2t * Rp_vec;
      var pk: seed * Rp_vec;
      var sk: Rq_vec;
      
      (pk, sk) <@ S.kg();
      c <@ S.enc(pk, m);
      m' <@ S.dec(sk, c);

      return (Some m = m');
   }
}.
*)

module Correctness_Standard_ROM (S : SchemeRO) (RO : Oracle) = {
   proc main(m : R2) : bool = {
      var m': R2 option;
      var c: R2t * Rp_vec;
      var pk: seed * Rp_vec;
      var sk: Rq_vec;
      
      RO.init();
      
      (pk, sk) <@ S(RO).kg();
      c <@ S(RO).enc(pk, m);
      m' <@ S(RO).dec(sk, c);

      return (Some m = m');
   }
}.


(* ----------------------------------- *)
(*  FO Correctness Definition (Game)   *)
(* ----------------------------------- *)
(*
In standard model:

module Correctness_Game (S : Scheme, A : Adv_Cor) = {
   proc main() : bool = {
      var m: R2;
      var m': R2 option;
      var c: R2t * Rp_vec;
      var pk: seed * Rp_vec;
      var sk: Rq_vec;
      
      (pk, sk) <@ S.kg();
      m <@ A.choose(pk, sk);
      c <@ S.enc(pk, m);
      m' <@ S.dec(sk, c);

      return (Some m = m');
   }
}.
*)

module Correctness_Game_ROM (S : SchemeRO, A : Adv_Cor_ROM, RO : Oracle) = {
   proc main() : bool = {
      var m: R2;
      var m': R2 option;
      var c: R2t * Rp_vec;
      var pk: seed * Rp_vec;
      var sk: Rq_vec;
      
      RO.init();
      
      (pk, sk) <@ S(RO).kg();
      m <@ A(RO).choose(pk, sk);
      c <@ S(RO).enc(pk, m);
      m' <@ S(RO).dec(sk, c);

      return (Some m = m');
   }
}.



(* ----------------------------------- *)
(*  Scheme Specifications (ROM)        *)
(* ----------------------------------- *)
(* Original Specification *)
module (Saber_PKE_Scheme_ROM : SchemeRO) (Gen : POracle) = {
   proc kg() : (seed * Rp_vec) * Rq_vec = {
      var sd: seed;
      var _A: Rq_mat;
      var s: Rq_vec;
      var b: Rp_vec;
      
      sd <$ dseed;
      _A <@ Gen.o(sd);
      s <$ dsmallRq_vec;
      b <- scaleRqv2Rpv (_A *^ s + h);
      
      return ((sd, b), s);
   }

   proc enc(pk: seed * Rp_vec, m: R2) : R2t * Rp_vec = {
      var sd: seed;
      var _A: Rq_mat;
      var s': Rq_vec;
      var b, b': Rp_vec;
      var v': Rp;
      var cm: R2t;
      
      sd <- pk.`1;
      b <- pk.`2;
      _A <@ Gen.o(sd);
      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cm <- scaleRp2R2t (v' + (scaleR22Rp m));
      
      return (cm, b');
   }

   proc dec(sk: Rq_vec, c: R2t * Rp_vec) : R2 option = {
      var c_dec: R2t * Rp_vec;
      var cm: R2t;
      var b': Rp_vec;
      var v: Rp;
      var s: Rq_vec;
      var m': R2;
      
      s <- sk;
      cm <- c.`1;
      b' <- c.`2;
      v <- (dotp b' (Rqv2Rpv s)) + (Rq2Rp h1);
      m' <- scaleRp2R2 (v  - (scaleR2t2Rp cm) + (Rq2Rp h2));
      
      return Some m';
   }
}.

(* Alternative Specification (Equivalent to Original, but More Useful in Correctness Analysis) *)
module (Saber_PKE_Scheme_Alt_ROM : SchemeRO) (Gen : POracle) = {
   proc kg() : (seed * Rp_vec) * Rq_vec = {
      var sd: seed;
      var _A: Rq_mat;
      var s: Rq_vec;
      var b: Rp_vec;
      
      sd <$ dseed;
      _A <@ Gen.o(sd);
      s <$ dsmallRq_vec;
      b <- scaleRqv2Rpv (_A *^ s + h);
      
      return ((sd, b), s);
   }

   proc enc(pk: seed * Rp_vec, m: R2) : R2t * Rp_vec = {
      var sd: seed;
      var _A: Rq_mat;
      var s': Rq_vec;
      var b, b': Rp_vec;
      var bq: Rq_vec;
      var v': Rq;
      var cm: R2t;
      
      sd <- pk.`1;
      b <- pk.`2;
      _A <@ Gen.o(sd);
      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      bq <- scaleRpv2Rqv b;
      v' <- (dotp bq s') + (upscaleRq h1 (eq - ep));
      cm <- scaleRq2R2t (v' + (scaleR22Rq m));
      
      return (cm, b');
   }

    proc dec(sk: Rq_vec, c: R2t * Rp_vec) : R2 option = {
      var c_dec: R2t * Rp_vec;
      var cm: R2t;
      var cmq: Rq;
      var b': Rp_vec;
      var bq': Rq_vec;
      var v: Rq;
      var s: Rq_vec;
      var m': R2;

      s <- sk;
      cm <- c.`1;
      cmq <- scaleR2t2Rq cm;
      b' <- c.`2;
      bq' <- scaleRpv2Rqv b';
      
      v <- (dotp bq' s) + (upscaleRq h1 (eq - ep));
      m' <- scaleRq2R2 (v - cmq + (upscaleRq h2 (eq - ep)));
      
      return Some m';
   }
}.


(* --- Equivalence of Schemes --- *)
(* - Equivalence of Key Generation - *)
equiv eqv_kg (RO <: POracle) : 
  Saber_PKE_Scheme_ROM(RO).kg ~ Saber_PKE_Scheme_Alt_ROM(RO).kg : ={glob RO} ==> ={glob RO, res}.
proof. 
proc.
by wp; rnd; call(: true); rnd; skip.
qed.

(* - Equivalence of Encryption - *)
equiv eqv_enc (RO <: POracle): 
  Saber_PKE_Scheme_ROM(RO).enc ~ Saber_PKE_Scheme_Alt_ROM(RO).enc : ={glob RO, pk, m} ==> ={glob RO, res}.
proof.
proc.
wp; rnd; call (: true); wp; skip => /> *.
by apply eq_comp_enc_altenc.
qed.

(* - Equivalence of Decryption - *)
equiv eqv_dec (RO <: POracle): 
  Saber_PKE_Scheme_ROM(RO).dec ~ Saber_PKE_Scheme_Alt_ROM(RO).dec : ={sk, c} ==> ={res}.
proof.
proc.
wp; skip => /> ?.
by apply eq_comp_dec_altdec.
qed.

(* Equivalence of Standard Correctness Definition with Regular and Alternative PKE Description *)
equiv Equivalence_Correctness_Standard_Reg_Alt :
  Correctness_Standard_ROM(Saber_PKE_Scheme_ROM, Gen).main ~ Correctness_Standard_ROM(Saber_PKE_Scheme_Alt_ROM, Gen).main : ={m} ==> ={res}.
proof.
proc; inline{1} 1; inline{2} 1.
call (eqv_dec Gen); call (eqv_enc Gen); call (eqv_kg Gen).
by wp; skip.
qed.

lemma eq_Pr_Correctness_Standard_Reg_Alt &m (msg : R2) :
  Pr[ Correctness_Standard_ROM(Saber_PKE_Scheme_ROM, Gen).main(msg) @ &m : res]
  =
  Pr[Correctness_Standard_ROM(Saber_PKE_Scheme_Alt_ROM, Gen).main(msg) @ &m : res].
proof. by byequiv Equivalence_Correctness_Standard_Reg_Alt. qed.


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

(* --- Delta-Related Errors, Predicates, Properties, and Probabilistic Program --- *)
(* Error With Probability Distribution That is Computed Exhaustively in Python Script *)
op delta_error (_A : Rq_mat) (s s' : Rq_vec) = 
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' - error_cmq_nom_centered _A s s'.

(* Error Equivalent to Previous Error, But Includes Message m *)
op delta_error_wm (_A : Rq_mat) (s s' : Rq_vec) (m : R2) = 
  dotp (error_bq' _A s') s - dotp (error_bq _A s) s' - error_cmq_centered _A s s' m.

(* Predicate That Checks Whether Coefficients are In Correctness Range that Gives Delta Bound *)
op coeffs_in_correctness_rng (p : Rq) = forall (i : int), 0 <= i < n =>
  Zq.asint (Zq.inzmod (- q %/ 4)) <= Zq.asint p.[i] \/ Zq.asint p.[i] < Zq.asint (Zq.inzmod (q %/ 4)).

(* Equality of Delta Errors With and Without m *)
lemma eq_deltaerror_deltaerrorwm (_A : Rq_mat) (s s' : Rq_vec) (m : R2) :
   delta_error _A s s' = delta_error_wm _A s s' m.
proof. 
by rewrite /delta_error /delta_error_wm /error_cmq_nom_centered /error_cmq_centered 
           eq_errcmq_errcmqnom.
qed.

(* Equivalence Between Verifying (m = m') and Verifying Delta Error Coefficients in Correct Range *)
lemma eqv_verification_mm'_coeffsrngdelta (_A : Rq_mat) (s s' : Rq_vec) (m : R2) :
  (m = m'_expression _A s s' m) = coeffs_in_correctness_rng (delta_error _A s s').
proof.
rewrite /coeffs_in_correctness_rng scaleRq2R2_rng_zero_q4 eq_expression_m'_m'_alt
        (eq_deltaerror_deltaerrorwm _ _ _ m) /delta_error_wm. 
rewrite /m'_expression_alt /m'_expression_Rq_alt scaleRq2R2_DM_invl eq_iff.
split => [eqm_merr | coeffs_corr].
+ by rewrite eq_sym &(addrI m) addr0 {1}eqm_merr; do 2! congr; ring.
+ by rewrite &(addrI (- m)) addrC subrr addrCA addrA subrr add0r -coeffs_corr; congr; ring.
qed.

(* Probabilistic Program Used to Represent Exhaustively Computed Correctness Probability *)
module Delta_Prob_PProg = {
   proc main() : bool = {
      var sd: seed;
      var _A : Rq_mat;
      var s, s': Rq_vec;

      _A <$ dRq_mat;
      s <$ dsmallRq_vec;
      s' <$ dsmallRq_vec;

      return coeffs_in_correctness_rng (delta_error _A s s');
   }
}.

(* Constant Probability of Delta-Prob Program *)
lemma DeltaProb_Constant &m1 &m2 :
  Pr[Delta_Prob_PProg.main() @ &m1 : res] = Pr[Delta_Prob_PProg.main() @ &m2 : res].
proof.
byequiv => //.
proc.
by auto.
qed.

(* Define Delta Bound and Delta-Correctness *)
op delta_prob : { real | 0%r <= delta_prob <= 1%r } as rng_deltaprob.

axiom delta_correctness &m : 
  Pr[Delta_Prob_PProg.main() @ &m : res] = 1%r - delta_prob.


(* --- Proof of Equivalence of Standard Correctness for Original Scheme and Delta-Prob Program --- *)
(* - Intermediate Game, Standard Correctness in Terms of Error - *)
module Correctness_Standard_Error_Gen = {
   proc main(m : R2) : bool = {
      var sd: seed;
      var _A: Rq_mat;
      var s, s': Rq_vec;
      
      Gen.init();
     
      sd <$ dseed;
      _A <@ Gen.o(sd);
      s <$ dsmallRq_vec;
      s' <$ dsmallRq_vec;

      return (m = m'_expression _A s s' m);
   }
}.

equiv Equivalence_CorrStd_Error :
  Correctness_Standard_ROM(Saber_PKE_Scheme_Alt_ROM, Gen).main ~ Correctness_Standard_Error_Gen.main
        : ={m} ==> ={res}.
proof.
proc; inline *.
wp; rnd.
wp; rnd{1}.
wp; rnd; wp; rnd; wp; rnd; wp; skip => /> &2 sd sdin r rin.
split=> [sdnin s sin| ]; 2: by rewrite SmtMap.mem_empty.
split=> [| _ r' rpin]; 1: by apply dRq_mat_ll.
split=> [| sdinm s' spin]; 1: by rewrite SmtMap.mem_set negb_or. 
pose sc := scaleRq2R2 _; pose mp := m'_expression _ _ _ _.
suff -> //: sc = mp; rewrite /sc /mp.
have eqsc:
 forall (m : matrix), 
  (trmx m) *^ s' + error_bq' m s'   
  = 
  scaleRpv2Rqv (scaleRqv2Rpv (trmx m *^ s' + h)).
+ by move=> m; rewrite /error_bq' /errorRqv addrCA addrC subrr add0r.
rewrite /m'_expression /m'_expression_Rq /v_expression /cmq_expression /error_cmq 
        /v'_expression /errorRq /=.
do 4! congr; 1: by rewrite eqsc.
ring; rewrite addrC ofint0 subr_eq0; do 5! congr; rewrite /error_bq /errorRqv. 
by pose sc2 := scaleRpv2Rqv _; rewrite addrCA Vector.ZModule.addrC -subr_eq subrr subrr.
qed.

equiv Equivalence_CorrStd_DeltaProb :
  Correctness_Standard_ROM(Saber_PKE_Scheme_ROM, Gen).main ~ Delta_Prob_PProg.main : true ==> ={res}.
proof.
transitivity Correctness_Standard_ROM(Saber_PKE_Scheme_Alt_ROM, Gen).main 
             (={m} ==> ={res}) (true ==> ={res}) => //= [&1| |].
+ by exists m{1}.
+ by apply Equivalence_Correctness_Standard_Reg_Alt.
transitivity Correctness_Standard_Error_Gen.main 
             (={m} ==> ={res}) (true ==> ={res}) => //= [&1| |].
+ by exists m{1}.
+ by apply Equivalence_CorrStd_Error.
proc; inline *.
rnd; rnd.
wp; rnd.
wp; rnd{1}.
wp; skip => /> &1 sd sdin r rin.
split => [sdninm s sin s' spin|]; 2: by rewrite SmtMap.mem_empty.
by rewrite eqv_verification_mm'_coeffsrngdelta SmtMap.get_set_sameE oget_some.
qed.

lemma Delta_Correctness_Standard_Original_Scheme &m (msg : R2) :
  Pr[Correctness_Standard_ROM(Saber_PKE_Scheme_ROM, Gen).main(msg) @ &m : res] = 1%r - delta_prob.
proof.
have ->:
  Pr[Correctness_Standard_ROM(Saber_PKE_Scheme_ROM, Gen).main(msg) @ &m : res]
  =
  Pr[Delta_Prob_PProg.main() @ &m : res].
+ by byequiv Equivalence_CorrStd_DeltaProb.
by apply delta_correctness.
qed.


(* --- Proof of Equivalence of Correctness Game for Original Scheme and Delta-Prob Program --- *)
section Equivalence_Correctness_Games_Delta_PProg.

(* - Declare (Arbitrary, Terminating) Adversary Against FO Correctness Game - *)
declare module A <: Adv_Cor_ROM{-Gen}.
declare axiom A_Cor_ll (RO <: POracle{-A}) : 
  islossless RO.o => islossless A(RO).choose.

(* - Intermediate Game, Correctness Game in Terms of Error - *)
local module Correctness_Game_Error_Gen = {
   proc main() : bool = {
      var sd: seed;
      var _A: Rq_mat;
      var s, s': Rq_vec;
      var m: R2;
      
      Gen.init();
      
      sd <$ dseed;
      _A <@ Gen.o(sd);
      s <$ dsmallRq_vec;
      m <@ A(Gen).choose((sd, scaleRqv2Rpv (_A *^ s + h)), s);      
      s' <$ dsmallRq_vec;
     
      return (m = m'_expression _A s s' m);
   }
}.

(* Equivalence of FO Correctness Games with Original and Alternative PKE Description *)
local lemma Equivalence_Correctness_Game_Reg_Alt :
  equiv[Correctness_Game_ROM(Saber_PKE_Scheme_ROM, A, Gen).main ~ Correctness_Game_ROM(Saber_PKE_Scheme_Alt_ROM, A, Gen).main 
        : ={glob A} ==> ={res}].
proof.
proc; inline{1} 1; inline{2} 1.
call (eqv_dec Gen); call (eqv_enc Gen).
call (: ={Gen.m}); 1: by proc; auto.
call (eqv_kg Gen).
by wp; skip.
qed.

local lemma Equivalence_CorrGame_Error :
  equiv[Correctness_Game_ROM(Saber_PKE_Scheme_Alt_ROM, A, Gen).main ~ Correctness_Game_Error_Gen.main
        : ={glob A} ==> ={res}].
proof.
proc; inline *.
seq 9 7 : (   ={glob A, LRO.m, _A} 
           /\ pk{1} = (sd{2}, scaleRqv2Rpv (_A{2} *^ s{2} + h))  
           /\ sk{1} = s{2}
           /\ pk{1}.`1 \in LRO.m{1} 
           /\ LRO.m{1}.[pk{1}.`1] = Some _A{1}).
+ rcondt{1} 5; first by auto; smt(SmtMap.mem_empty).
  rcondt{2} 5; first by auto; smt(SmtMap.mem_empty).
  wp; rnd; wp; rnd; wp; rnd; wp; skip => /> *.
  by rewrite mem_set get_set_sameE.
wp; rnd; wp.
rnd{1}. wp.
exists* pk{1}, _A{1}; elim* => pkt _At.
call (: ={LRO.m} /\ pkt.`1 \in LRO.m{1} /\ LRO.m{1}.[pkt.`1] = Some _At).
proc.
wp. rnd.
skip => />.
progress.
rewrite mem_set /#.
rewrite get_setE.
by have ->: pkt.`1 <> x{2} by smt().
skip=> /> &2 sdinm eqlrma msg fm sdin eqfma.
split => [| _ r rin s' spin]; 1: by apply dRq_mat_ll.
pose sc := scaleRq2R2 _; pose mp := m'_expression _ _ _ _.
suff -> //: sc = mp; rewrite /sc /mp.
have eqsc:
 forall (m : matrix), 
  (trmx m) *^ s' + error_bq' m s'   
  = 
  scaleRpv2Rqv (scaleRqv2Rpv (trmx m *^ s' + h)).
+ by move=> m; rewrite /error_bq' /errorRqv addrCA addrC subrr add0r.
rewrite /m'_expression /m'_expression_Rq /v_expression /cmq_expression /error_cmq 
        /v'_expression /errorRq /=.
do 4! congr; 1: by rewrite eqfma oget_some eqsc.
ring; rewrite addrC ofint0 subr_eq0; do 5! congr; rewrite /error_bq /errorRqv. 
by pose sc2 := scaleRpv2Rqv _; rewrite addrCA Vector.ZModule.addrC -subr_eq subrr subrr.
qed.



(* --- Final Theorems/Results --- *) 
(* 
  Equivalence of FO Correctness Game for Saber's Original Scheme and
  Probabilistic Program Used to Represent Exhaustively Computed Correctness Probability 
*)
lemma Equivalence_CorrGame_DeltaProb :
  equiv[Correctness_Game_ROM(Saber_PKE_Scheme_ROM, A, Gen).main ~ Delta_Prob_PProg.main : true ==> ={res}].
proof.
transitivity Correctness_Game_ROM(Saber_PKE_Scheme_Alt_ROM, A, Gen).main 
             (={glob A} ==> ={res}) (true ==> ={res}) => //= [&1| |]; first by exists (glob A){1}.
+ by apply Equivalence_Correctness_Game_Reg_Alt.
transitivity Correctness_Game_Error_Gen.main (={glob A} ==> ={res}) (true ==> ={res}) 
             => //= [&1| |]; first by exists (glob A){1}.
+ by apply Equivalence_CorrGame_Error.
proc; inline *.
wp; rnd; call{1} (A_Cor_ll Gen).
+ proc.
  wp; rnd; skip => />.
  by apply dRq_mat_ll.
rcondt{1} 5; first by auto; smt(mem_empty).
rnd; wp; rnd; wp; rnd{1}; wp; skip => /> *.
by rewrite eqv_verification_mm'_coeffsrngdelta SmtMap.get_set_sameE oget_some.
qed.

(* Delta-Correctness of Saber's Original Scheme *)
lemma Delta_Correctness_Game_Original_Scheme &m :
  Pr[Correctness_Game_ROM(Saber_PKE_Scheme_ROM, A, Gen).main() @ &m : res] = 1%r - delta_prob.
proof.
have ->:
  Pr[Correctness_Game_ROM(Saber_PKE_Scheme_ROM, A, Gen).main() @ &m : res]
  =
  Pr[Delta_Prob_PProg.main() @ &m : res].
+ by byequiv Equivalence_CorrGame_DeltaProb.
by apply delta_correctness.
qed.

(* Equivalence of Correctness Definitions for Saber's Original Scheme *)
lemma Equivalence_Corr_Std_Game_Original_Scheme :
  equiv[Correctness_Standard_ROM(Saber_PKE_Scheme_ROM, Gen).main ~ Correctness_Game_ROM(Saber_PKE_Scheme_ROM, A, Gen).main
        : true ==> ={res}].
proof.
transitivity Delta_Prob_PProg.main (true ==> ={res}) (true ==> ={res}) => //=.
+ by apply Equivalence_CorrStd_DeltaProb.
symmetry; conseq (_ : _ ==> ={res}) => //. 
by apply Equivalence_CorrGame_DeltaProb.
qed.

end section Equivalence_Correctness_Games_Delta_PProg.
