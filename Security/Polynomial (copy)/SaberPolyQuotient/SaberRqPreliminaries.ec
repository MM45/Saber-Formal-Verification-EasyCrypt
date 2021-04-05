(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr ZModP IntDiv StdOrder.
require (*--*) Matrix.

(* --- Local --- *)
require (*--*) SaberPolyQuotientRing SaberMatrix.

(* ----------------------------------- *)
(*  Preliminaries                      *)
(* ----------------------------------- *)

(* --- Constants --- *)
(* -- Exponents -- *)
const eq: int.
const ep: int.
const et: int.
const en: int.

(* -- Parameters -- *)
const q: int = 2^eq. 
const p: int = 2^ep.
const t: int = 2^et.
const n: int = 2^en.
const l: int.

(* -- Assumptions/Properties -- *)
axiom ge0_en: 0 <= en.
axiom ge1_et1: 1 <= et + 1.
axiom geet2_ep: et + 2 <= ep.
axiom geep1_eq: ep + 1 <= eq.
axiom sec_assumption: eq - ep <= ep - et - 1.
axiom ge1_l: 1 <= l.

lemma ge0_et: 0 <= et by apply /(lez_add2l (-1) 1 (et + 1)) /ge1_et1.
lemma ge2_ep: 2 <= ep by apply /(lez_trans (et + 2) 2 ep) /geet2_ep /(lez_add2r 2 0 et) /ge0_et.
lemma ge3_eq: 3 <= eq by apply /(lez_trans (ep + 1) 3 eq) /geep1_eq /(lez_add2r 1 2 ep) /ge2_ep.

lemma ge1_t: 1 <= t by rewrite IntOrder.exprn_ege1; [apply ge0_et |].
lemma ge2_2t: 2 <= 2 * t by move: (IntOrder.ler_pmul2l 2 _ 1 t); rewrite // ge1_t //.
lemma ge4_p: 4 <= p by move: (IntOrder.ler_weexpn2l 2 _ 2 ep); rewrite //= ge2_ep /= expr2.
lemma ge8_q: 8 <= q by move: (IntOrder.ler_weexpn2l 2 _ 3 eq); rewrite //= ge3_eq /= (exprS 2 2) // expr2.

lemma two_div_t: 2 %| 2 * t by apply /dvdz_mulr /dvdzz.

lemma t_div_p: t %| p.
proof.
  rewrite /t /p; apply (dvdz_exp2l 2 et ep); split; [apply ge0_et | move=> ?].
  by apply /(lez_trans (et + 2) et ep) /geet2_ep; rewrite (lez_addl et 2). 
qed.

lemma twot_div_p: 2 * t %| p.
proof.
  rewrite /t /p -exprS; [apply ge0_et | apply (dvdz_exp2l 2 (et + 1) (ep)); split; last move=> ?].
  by apply /(lez_trans 1 0 (et + 1)) /ge1_et1.  
  by apply /(lez_trans (et + 2) (et + 1) ep) /geet2_ep /(IntOrder.ler_add et et 1 2).
qed.

lemma p_div_q: p %| q.
proof. 
  rewrite /p /q; apply (dvdz_exp2l 2 ep eq); split; [| move=> ?].
  by apply /(lez_trans 2 0 (ep)) /ge2_ep.
  by apply /(lez_trans (ep + 1) ep eq) /geep1_eq; rewrite (lez_addl ep 1).
qed.

lemma t_div_q: t %| q by apply /(dvdz_trans p t q) /p_div_q /t_div_p.

lemma geeq1_2ep: eq + 1 <= 2 * ep.
proof.
  have le0_eq2ep: eq - ep - ep <= -1.
   apply (lez_trans (-et - 1) (eq - ep - ep) (-1)). 
    by move: (lez_add2l (-ep) (eq - ep) (ep - et - 1)); rewrite sec_assumption addzC 2!addzA.
    by rewrite -(lez_add2r (et + 1) (-et - 1) (-1)) addzA addzC addzA /= ge0_et.
  by rewrite mulzC -(intmulz ep 2) mulr2z -(lez_add2r (-1) _ _) /= 
             -(lez_add2l ((-(ep + ep))) _ _) addzA /= addzC opprD addzA.
qed.  

lemma q_div_pp: q %| (p * p).
proof.
  rewrite /p /q -exprD_nneg; first 2 by apply /(IntOrder.ler_trans 2 0 ep) /ge2_ep.
  rewrite dvdz_exp2l; split; [by apply /(lez_trans 3 0 eq) /ge3_eq | move => ?]. 
  by rewrite -mul1r2z mulrC /ofint_id intmulz /= (lez_trans (eq + 1) _ _); 
             [rewrite (lez_addl eq 1) | apply geeq1_2ep].
qed.

lemma ge2_ppq: 2 <= (p * p) %/ q.
proof.
  apply (IntOrder.ler_pmul2r q); first by rewrite /q IntOrder.expr_gt0.
   have ->: p * p %/ q * q = p * p.
    by rewrite -(dvdz_eq q (p * p)) q_div_pp.
   rewrite /p /q -exprS; first by apply /(lez_trans 3 0 eq) /ge3_eq.
    rewrite -exprD_nneg; first 2 by apply /(lez_trans 2 0 ep) /ge2_ep.
     apply IntOrder.ler_weexpn2l; split; [by apply (lez_trans eq 0 (eq + 1)); 
           [apply /(lez_trans 3 0 eq) /ge3_eq | rewrite (lez_addl eq 1)] |].
      by rewrite -mul1r2z mulrC /ofint_id intmulz /= geeq1_2ep.
qed.

lemma eq_22epeq_ppq: 2 ^ (2 * ep - eq) = (p * p) %/ q.
proof.
  apply (mulfI q); [by rewrite neq_ltz; right; apply IntOrder.expr_gt0 | rewrite mulzC -(mulzC (p * p %/ q) _)].  
  have ->: p * p %/ q * q = p * p.
   by rewrite -(dvdz_eq q (p * p)) q_div_pp.
  rewrite /p /q -exprD_nneg; first by rewrite subz_ge0 (lez_trans (eq + 1) eq (2 * ep)); 
          [rewrite (lez_addl _ 1) | apply geeq1_2ep].
   by apply /(lez_trans 3 0 eq) /ge3_eq.
  rewrite -exprD_nneg; first 2 by rewrite (lez_trans 2 0 ep); [| apply ge2_ep || apply ge2_ep ].
   by congr; rewrite -addzA /= mulzC -mul1r2z /ofint_id intmulz.
qed.

(* --- Types, Operators and Distributions --- *)
(* -- Rq = Z/qZ[X] / (X^n + 1) -- *)
type Zq.
type Rq.

clone import MFinite as DRq with
    type t <- Rq,
    op Support.card <- q ^ n.
    
clone SaberMatrix as Mat_Rq with
    op p <- q,
    op en <- en,
    type coeff <- Zq,
    type poly <- Rq,
    op size <- l
  proof ge2_coeffp by apply /(lez_trans 8 2 q) /ge8_q
  proof ge0_en by apply ge0_en
  proof ge0_size by apply /(lez_trans 1 0 l) /ge1_l

  rename [theory] "PolyQuotientRing" as "Rq"
  rename [theory] "Coeff" as "Zq".

type Rq_vec = Mat_Rq.vector.
type Rq_mat = Mat_Rq.Matrix.matrix.

op dRq : Rq distr = DRq.dunifin.
op [lossless] dsmallRq : Rq distr.

op dRq_vec : Rq_vec distr = Mat_Rq.Matrix.dvector dRq.
op dRq_mat : Rq_mat distr = Mat_Rq.Matrix.dmatrix dRq.
op dsmallRq_vec : Rq_vec distr = Mat_Rq.Matrix.dvector dsmallRq.

(* -- Rp = Z/pZ[X] / (X^n + 1) -- *)
type Zp.
type Rp.

clone import MFinite as DRp with
    type t <- Rp,
    op Support.card <- p ^ n.

clone SaberMatrix as Mat_Rp with
    op p <- p,
    op en <- en,
    type coeff <- Zp,
    type poly <- Rp,
    op size <- l
  proof ge2_coeffp by apply /(lez_trans 4 2 p) /ge4_p
  proof ge0_en by apply ge0_en
  proof ge0_size by apply /(lez_trans 1 0 l) /ge1_l

  rename [theory] "PolyQuotientRing" as "Rp"
  rename [theory] "Coeff" as "Zp".  

type Rp_vec = Mat_Rp.vector.

op dRp : Rp distr = DRp.dunifin. 
op dRp_vec : Rp_vec distr = Mat_Rp.Matrix.dvector dRp.

(* -- Rppq = Z/ppqZ [X] / (X^n + 1) -- *)
type Zppq.
type Rppq.

clone import SaberPolyQuotientRing as Rppq with 
    op p <- (p * p) %/ q,
    op en <- en,
    type coeff <- Zppq,
    type poly <- Rppq
  proof ge2_coeffp by apply ge2_ppq
  proof ge0_en by apply ge0_en

  rename [theory] "Coeff" as "Zppq".

(* -- R2t = Z/2tZ [X] / (X^n + 1)  -- *)
type Z2t.
type R2t.

clone import SaberPolyQuotientRing as R2t with 
    op p <- 2 * t,
    op en <- en,
    type coeff <- Z2t,
    type poly <- R2t
  proof ge2_coeffp by apply ge2_2t
  proof ge0_en by apply ge0_en

  rename [theory] "Coeff" as "Z2t".

(* -- R2 = Z/2Z [X] / (X^n + 1) -- *)
type Z2.
type R2.

clone import SaberPolyQuotientRing as R2 with 
    op p <- 2,
    op en <- en,
    type coeff <- Z2,
    type poly <- R2
  proof ge2_coeffp by apply lezz
  proof ge0_en by apply ge0_en

  rename [theory] "Coeff" as "Z2".

(* - Properties - *)
(* Vector Distribution Has Same Properties as the Distribution of the Vector's Elements *)
lemma dRq_vec_ll: is_lossless dRq_vec.
proof. by apply Mat_Rq.Matrix.dvector_ll; rewrite /dRq; apply /DRq.dunifin_ll. qed.

lemma dRq_vec_fu: is_full dRq_vec.
proof. by apply /Mat_Rq.Matrix.dvector_fu; rewrite /dRq; apply /DRq.dunifin_fu. qed.

lemma dRq_vec_uni: is_uniform dRq_vec.
proof. by apply /Mat_Rq.Matrix.dvector_uni; rewrite /dRq; apply /DRq.dunifin_uni. qed.

lemma dRp_vec_ll: is_lossless dRp_vec.
proof. by apply /Mat_Rp.Matrix.dvector_ll; rewrite /dRp; apply /DRp.dunifin_ll. qed.

lemma dRp_vec_fu: is_full dRp_vec.
proof. by apply /Mat_Rp.Matrix.dvector_fu; rewrite /dRp; apply /DRp.dunifin_fu. qed.

lemma dRp_vec_uni: is_uniform dRp_vec.
proof. by apply /Mat_Rp.Matrix.dvector_uni; rewrite /dRp; apply /DRp.dunifin_uni. qed.

lemma dsmallRq_vec_ll: is_lossless dsmallRq_vec.
proof. by apply /Mat_Rq.Matrix.dvector_ll /dsmallRq_ll. qed.

(* Matrix Distribution Has Same Properties as the Distribution of the Matrix's Elements *)
lemma dRq_mat_ll: is_lossless dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_ll; rewrite /dRq; apply /DRq.dunifin_ll. qed.

lemma dRq_mat_fu: is_full dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_fu; rewrite /dRq; apply /DRq.dunifin_fu. qed.

lemma dRq_mat_uni: is_uniform dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_uni; rewrite /dRq; apply /DRq.dunifin_uni. qed.

(* - Imports - *)
import Mat_Rq Mat_Rp.
import Rq Rp.
import Zq Zp.

(* - Constants - *)
const h1 : Rq = to_polyd (fun _ => Zq.inzmod (2 ^ (eq - ep - 1))).
const h2 : Rq = to_polyd (fun _ => Zq.inzmod (2 ^ (ep - 2) - 2 ^ (ep - et - 2))).
const h : Rq_vec = vectc h1.
 
(* -- Cryptographic Types and Distributions  -- *)
type seed.
type pkey.
type skey.
type plaintext.
type ciphertext.

op [lossless full uniform] dseed : seed distr.

(* -- Operations -- *)
op gen : seed -> Rq_mat.

op shl (x : int, ex : int) : int = x * 2^ex.
op shl_enc (x : R2, ex : int) : Rp = to_polyd (fun i => Zp.inzmod (shl (Z2.asint x.[i]) ex)).
op shl_dec (x : R2t) : Rp = to_polyd (fun i => Zp.inzmod (shl (Z2t.asint x.[i]) (ep - et - 1))).

op shr (x : int, ex : int) : int = x %/ 2^ex.

op scale (x : int, ea : int, eb : int) : int = shr x (ea - eb).
op scale_Zq_Zp (x : Zq) : Zp = Zp.inzmod (scale (Zq.asint x) eq ep).
op scale_Zp_Z2t (x : Zp) : Z2t = Z2t.inzmod (scale (Zp.asint x) ep (et + 1)).
op scale_Zp_Z2 (x : Zp) : Z2 = Z2.inzmod (scale (Zp.asint x) ep 1).
op scale_Zp_Zppq (x : Zp) : Zppq = Zppq.inzmod (scale (Zp.asint x) ep (2 * ep - eq)).
op scale_Zp_Zp (x : Zp) : Zp = Zp.inzmod (scale (Zp.asint x) ep ep).
op scale_Zppq_Z2t (x : Zppq) : Z2t = Z2t.inzmod (scale (Zppq.asint x) (2 * ep - eq) (et + 1)).

op scale_Rq_Rp (x : Rq) : Rp = to_polyd (fun i => scale_Zq_Zp x.[i]).
op scale_Rp_R2t (x : Rp) : R2t = to_polyd (fun i => scale_Zp_Z2t x.[i]).
op scale_Rp_R2 (x : Rp) : R2 = to_polyd (fun i => scale_Zp_Z2 x.[i]).
op scale_Rp_Rppq (x : Rp) : Rppq = to_polyd (fun i => scale_Zp_Zppq x.[i]).
op scale_Rp_Rp (x : Rp) : Rp = to_polyd (fun i => scale_Zp_Zp x.[i]).
op scale_Rppq_R2t (x : Rppq) : R2t = to_polyd (fun i => scale_Zppq_Z2t x.[i]).

op scale_vec_Rq_Rp (v : Rq_vec) : Rp_vec = offunv (fun i => scale_Rq_Rp v.[i]).

op mod_p_Rq (x : Rq) : Rp = to_polyd (fun i => Zp.inzmod (Zq.asint x.[i])).
op mod_p_Rq_vec (v : Rq_vec) : Rp_vec = offunv (fun i => mod_p_Rq v.[i]).

op mod_q_Rp (x : Rp) : Rq = to_polyd (fun i => Zq.inzmod (Zp.asint x.[i])).
op mod_q_Rp_vec (v : Rp_vec) : Rq_vec = offunv (fun i => mod_q_Rp v.[i]).

op mod_ppq_Rp (x : Rp) : Rppq =  to_polyd (fun i => Zppq.inzmod (Zp.asint x.[i])).

op pk_encode ['a] : 'a -> pkey.
op pk_decode ['a] : pkey -> 'a.

op sk_encode ['a] : 'a -> skey.
op sk_decode ['a] : skey -> 'a.

op m_encode ['a] : 'a -> plaintext.
op m_decode ['a] : plaintext -> 'a.

op c_encode ['a] : 'a -> ciphertext.
op c_decode ['a] : ciphertext -> 'a.

(* - Properties  - *)
axiom pk_enc_dec_inv ['a] (x : 'a) : pk_decode (pk_encode x) = x. 
axiom sk_enc_dec_inv ['a] (x : 'a) : sk_decode (sk_encode x) = x. 
axiom m_enc_dec_inv ['a] (x : 'a) : m_decode (m_encode x) = x. 
axiom c_enc_dec_inv ['a] (x : 'a) : c_decode (c_encode x) = x. 

lemma scale_comp (x ea eab eb : int):
      0 <= x => 0 <= eb => eb <= eab => eab <= ea =>
      scale x ea eb = scale (scale x ea eab) eab eb. 
proof. 
  (* Context *)
  move=> ge0_x ge0_eb geeb_eab geeab_ea; rewrite /scale /shr. 
  move: (divz_eq x (2^(ea - eb))) 
        (divz_eq x (2^(ea - eab))) 
        (divz_eq (x %/ 2 ^ (ea - eab)) (2^(eab - eb))).
  pose dmain := 2 ^ (ea - eb); pose d0 := 2 ^ (ea - eab); pose d1 := 2 ^ (eab - eb).
  pose qmain := x %/ dmain; pose q0 := x %/ d0; pose q1 := x %/ d1.
  pose rmain := x %% dmain; pose r0 := x %% d0; pose r1 := x %% d1.
  move=> divmain div0 div1.
  
  have gt0_d0: 0 < d0.
   by apply IntOrder.expr_gt0.
  have gt0_d1: 0 < d1.
   by apply IntOrder.expr_gt0.

  have eq_dmain_d0d1: dmain = d0 * d1.
   rewrite /dmain /d0 /d1 -exprD_nneg. 
    by rewrite -(lez_add2r eab 0 (ea - eab)) -addrA /= geeab_ea.
    by rewrite -(lez_add2r eb 0 (eab - eb)) -addrA /= geeb_eab.
    by congr; rewrite -addzA addKz.

  (* Main Result *)
  move: (euclideU dmain qmain (q0 %/ d1) rmain (q0 %% d1 * d0 + r0)).
   have <-: x = q0 %/ d1 * dmain + (q0 %% d1 * d0 + r0).
    by rewrite eq_dmain_d0d1 (mulzC d0 d1) -(mulzA (q0 %/ d1) _ _) addzA -(mulzDl _ _ d0) -div1.
   rewrite -divmain /=.  
   have ->: 0 <= rmain && rmain < `| dmain |.
    split; [by apply /modn_ge0 /ge0_x | move => ge0_rmain].
     by rewrite ltz_mod neq_ltz; right; apply IntOrder.expr_gt0.
   have ->:  0 <= q0 %% d1 * d0 + r0 && q0 %% d1 * d0 + r0 < `| dmain |.
    split; [by apply /addz_ge0 /modn_ge0 /ge0_x /IntOrder.mulr_ge0 /ltzW /gt0_d0 /modz_ge0 /neq_ltz; right | move=> ?].
     rewrite IntOrder.ger0_norm eq_dmain_d0d1; first by apply /IntOrder.mulr_ge0; apply /ltzW.
     apply (IntOrder.ltr_le_trans ((d1 - 1) * d0 + d0) (q0 %% d1 * d0 + r0) (d0 * d1)). 
      apply (IntOrder.ler_lt_add (q0 %% d1 * d0) ((d1 - 1) * d0) r0 d0); last by apply ltz_pmod.
       apply /(IntOrder.ler_pmul (q0 %% d1) (d1 - 1) d0 d0) /lezz; 
             [by apply /modz_ge0 /neq_ltz; right | by apply ltzW |].
       by apply (lez_add2l 1 _ _); rewrite lez_add1r -addzCA /= ltz_pmod.
       by rewrite mulzDl mulNr /= -addzA addNz /= mulzC; apply lezz.
   by case.
qed.

lemma scale_comp_Zp_Zppq_Z2t (x : Zp):
      scale_Zp_Z2t x = scale_Zppq_Z2t (scale_Zp_Zppq x).
proof. 
  rewrite /scale_Zp_Z2t /scale_Zppq_Z2t /scale_Zp_Zppq Zppq.inzmodK -Z2t.eq_inzmod; do 2! congr.
  have ge2epeq_ep: 2 * ep - eq <= ep.
   by rewrite mulzC -intmulz mulr2z -(lez_add2l (-ep) _ _) -addzA addzCA addzA /= subz_le0 (lez_trans (ep + 1) ep eq);
              [rewrite (lez_addl _ 1) | apply geep1_eq ].
  rewrite (modz_small (scale (Zp.asint x) ep (2 * ep - eq)) (p * p %/ q)); first split; 
          rewrite /scale /shr; last move => ?.
   by apply /divz_ge0 /Zp.ge0_asint /IntOrder.expr_gt0.
   rewrite IntOrder.ger0_norm; first by apply /(lez_trans 2 0 (p * p %/ q)) /ge2_ppq. 
   apply ltz_divLR; first by apply IntOrder.expr_gt0. 
    rewrite -eq_22epeq_ppq -exprD_nneg; first by rewrite subz_ge0 (lez_trans (eq + 1) eq (2 * ep)); 
            [rewrite (lez_addl _ 1) | apply geeq1_2ep].
     by rewrite subz_ge0.
     by rewrite mulzC -intmulz mulr2z addzCA /=; apply /(IntOrder.ltr_le_trans p (Zp.asint x) p) /lezz /Zp.gtp_asint.
  apply /(scale_comp (Zp.asint x) ep (2 * ep - eq) (et + 1)) /ge2epeq_ep; 
        [apply Zp.ge0_asint | by apply /(lez_trans 1 0 (et + 1)) /ge1_et1 |].
  rewrite mulzC -intmulz mulr2z -(lez_add2r (-(et + 1))) /= -(lez_add2l (eq)) addzAC addzCA /= 
          -(lez_add2r (-ep)) addzAC (subrK ep (-ep)) opprD addzA.
  by apply sec_assumption.
qed.

lemma scale_comp_Rp_Rppq_R2t (x : Rp):
      scale_Rp_R2t x = scale_Rppq_R2t (scale_Rp_Rppq x).
proof. 
  rewrite /scale_Rp_R2t /scale_Rppq_R2t /scale_Rp_Rppq. 
  congr; rewrite fun_ext /(==) => i. 
  rewrite coeffE /=; first split; [| exists (deg x - 1); split] => [c0 gt0_c /= | | c0 ltc_deg /= ];
          1, 3: rewrite /scale_Zp_Zppq /scale /shr /Zppq.zero -Zppq.eq_inzmod; 
          1, 3: have ->: (Zp.asint x.[c0] = 0);
          [by rewrite -Zp.zeroE Zp.asint_eq lt0_coeff | | | 
           by rewrite -Zp.zeroE Zp.asint_eq gedeg_coeff //=; rewrite -(lez_add1r) addzC /= in ltc_deg|];
          1, 3: by do 2!congr; apply div0z.
  by rewrite (IntOrder.ltr_le_trans Rp.n) // -lez_add1r addzC /= Rp.len_deg.
  by apply scale_comp_Zp_Zppq_Z2t. 
qed.

lemma scale_id (x ea eb : int) : ea = eb => scale x ea eb = x.
proof. by move=> eq_eaeb; rewrite /scale /shr eq_eaeb addzN expr0. qed.

lemma scale_Zp_Zp_id (x : Zp) : scale_Zp_Zp x = x.
proof. by rewrite /scale_Zp_Zp scale_id 2: Zp.asintK. qed.

lemma scale_Rp_Rp_id (x : Rp) : scale_Rp_Rp x = x.
proof. 
  rewrite /scale_Rp_Rp poly_eqP => c gte0_c.
  have ->: (fun i => scale_Zp_Zp x.[i]) = (fun i => x.[i]).
   by rewrite fun_ext /(==) => ?; apply scale_Zp_Zp_id. 
  rewrite coeffE //; split; [| exists (deg x - 1); split] => [c0 gt0_c /= | | c0 ltc_deg /=]; 
          [by apply /Rp.lt0_coeff | | by apply /Rp.gedeg_coeff; rewrite -lez_add1r addzC /= in ltc_deg]. 
   by rewrite -lez_add1r addzC /= Rp.len_deg.
qed.

lemma eq_scaleZqZp_modZppq_scaleZpZppq (x : Zq) (m : Z2) :
  Zppq.inzmod (Zp.asint ( (scale_Zq_Zp x) + (Zp.inzmod (shl (Z2.asint m) (2 * ep - eq - 1)))))
  =
  scale_Zp_Zppq ((Zp.inzmod (Zq.asint x)) + Zp.inzmod (shl (Z2.asint m) (ep - 1))).
proof.
  rewrite /scale_Zq_Zp /scale_Zp_Zppq /scale /shr /shl !Zp.inzmodK !modzDm. 
  rewrite {2}(mulzC 2) -(intmulz ep) mulr2z !opprD !addzA /= (addzC _ eq).
  have ge0_eqep: 0 <= eq - ep; 1: by apply /(lez_trans 1) /(lez_add2l ep); 2: rewrite addzCA /= geep1_eq.
  have leep_eq_ep: eq - ep <= ep; 1: by rewrite -(lez_add2r ep) -addzA /= -mulr2z intmulz mulzC (lez_trans (eq + 1)) 2:geeq1_2ep lez_addl.
  have ge0_2epeq: 0 <= 2 * ep - eq; 1: by rewrite -(lez_add2r eq) -addzA /= (lez_trans (eq + 1)) 2:geeq1_2ep lez_addl.
  have leep_2epeq: 2 * ep - eq <= ep; first rewrite mulzC -intmulz mulr2z -(lez_add2l (-ep)) 2!addzA /=;
       move: (oppz_le0 (eq - ep)); rewrite ge0_eqep opprD /= addzC => -> //.
  case: (Z2.asint m = 0) => [-> /= | /neq_ltz]; last case => [lt0_m | gt0_m]; move: (Z2.Sub.valP m) => [ge0_m lt2_m].
   by rewrite -Zppq.eq_inzmod -eq_22epeq_ppq /p /q (modz_pow2_div); 
           [apply Zq.ge0_asint | split | rewrite opprD (addzC _ ep) addzA -mulr2z intmulz (mulzC ep) modz_mod modz_dvd_pow //].
   by rewrite -/Z2.asint lezNgt in ge0_m.
   have -> /= {gt0_m ge0_m lt2_m}: Z2.asint m = 1; first rewrite eqz_leq; split. 
    by rewrite -/Z2.asint -lez_add1r -(lez_add2l (-1)) /= in lt2_m.
    by rewrite -lez_add1r in gt0_m.
   rewrite -Zppq.eq_inzmod -eq_22epeq_ppq /p modz_dvd_pow; 1: by split.
   rewrite modz_pow2_div; [by apply /addz_ge0 /IntOrder.expr_ge0; 1: apply Zq.ge0_asint | by split |]. 
   rewrite opprD (addzC (-eq)) addzA /= -mulr2z intmulz (mulzC ep) modz_mod divzDr 1: dvdz_exp2l. 
    by split => [| ?]; last rewrite -(lez_add2r 1) -(lez_add2l ep) -!addzA /= !addzA addzAC addzC !addzA /= -mulr2z intmulz mulzC geeq1_2ep.
   have -> //: 2 ^ (ep - 1) %/ 2 ^ (eq - ep) = 2 ^ (2 * ep - eq - 1).
    rewrite eq_sym eqz_div 2:dvdz_exp2l 3: -exprD_nneg; last congr; rewrite //#. 
     by rewrite neq_ltz; right; apply IntOrder.expr_gt0.
     by split => [| ?]; last rewrite -(lez_add2r 1) -(lez_add2l ep) -!addzA /= !addzA addzAC addzC !addzA /= -mulr2z intmulz mulzC geeq1_2ep.
     by rewrite -(lez_add2r 1) -addzA /= -(lez_add2r eq) -addzA addzC /= geeq1_2ep.
     by apply /(lez_trans 1) /(lez_add2l ep); 2: rewrite addzCA /= geep1_eq.
qed. 

lemma eq_scaleRqRp_modRppq_scale_Rppq (x : Rq) (m : R2) :
  mod_ppq_Rp ( (scale_Rq_Rp x) + (shl_enc m (2 * ep - eq - 1)))
  =
  scale_Rp_Rppq ((mod_p_Rq x) + (shl_enc m (ep - 1))).
proof.
  rewrite /mod_ppq_Rp /scale_Rp_Rppq; congr; rewrite fun_ext /(==) => i. 
  rewrite !polyDE /mod_p_Rq /scale_Rq_Rp /shl_enc /"_.[_]" !to_polydK //=; first 4 split => [c lt0_c |]; 
          rewrite -/R2."_.[_]" -/Rq."_.[_]" //=; 2: exists (Rp.n - 1); 2: split => [| c gtn1_c]; 
          2: by rewrite -lez_add1r. 
   by rewrite lt0_coeff; 2: rewrite /scale_Zq_Zp /scale /shr Zq.zeroE.
   by rewrite gedeg_coeff 1:(lez_trans Rq.n) 1:Rq.len_deg; 1: rewrite -lez_add1r in gtn1_c;
              last rewrite /scale_Zq_Zp /scale /shr Zq.zeroE.
   by rewrite lt0_coeff 2:Z2.zeroE.
   by rewrite gedeg_coeff 1:(lez_trans Rq.n) 1:R2.len_deg; 1: rewrite -lez_add1r in gtn1_c;
              last rewrite /scale_Zq_Zp /scale /shr Z2.zeroE.
   by rewrite lt0_coeff 2:Zq.zeroE.
   by rewrite gedeg_coeff 1:(lez_trans Rq.n) 1:Rq.len_deg; 1: rewrite -lez_add1r in gtn1_c;
              last rewrite /scale_Zq_Zp /scale /shr Zq.zeroE.
   by rewrite lt0_coeff 2:Z2.zeroE.
   by rewrite gedeg_coeff 1:(lez_trans Rq.n) 1:R2.len_deg; 1: rewrite -lez_add1r in gtn1_c;
              last rewrite /scale_Zq_Zp /scale /shr Z2.zeroE.
 by apply eq_scaleZqZp_modZppq_scaleZpZppq.
qed.  
