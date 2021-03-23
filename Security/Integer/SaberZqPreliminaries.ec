(*
----------------------------------- 
 Require/Import Theories
-----------------------------------
*)
(* --- Built-in --- *)
require import AllCore Distr ZModP IntDiv StdOrder.
require (*--*) Matrix.

(*
--------------------------------
 Preliminaries
--------------------------------
*)
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
axiom ge1_et1: 1 <= et + 1.
axiom geet2_ep: et + 2 <= ep.
axiom geep1_eq: ep + 1 <= eq.
axiom sec_assumption: eq - ep <= ep - et - 1. (* q %/ p <= p %/ 2*t. *)
axiom ge1_l: 1 <= l.

lemma ge0_et: 0 <= et by apply /(lez_add2l (-1) 1 (et + 1)) /ge1_et1.
lemma ge2_ep: 2 <= ep by apply /(lez_trans (et + 2) 2 ep) /geet2_ep /(lez_add2r 2 0 et) /ge0_et.
lemma ge3_eq: 3 <= eq by apply /(lez_trans (ep + 1) 3 eq) /geep1_eq /(lez_add2r 1 2 ep) /ge2_ep.

lemma ge1_t: 1 <= t by rewrite IntOrder.exprn_ege1; [apply ge0_et |].
lemma ge2_2t: 2 <= 2 * t by move: (IntOrder.ler_pmul2l 2) => /= mm; rewrite (mm 1 t) ge1_t. 
lemma ge4_p: 4 <= p by move: (IntOrder.ler_weexpn2l 2) => /= mn; move: (mn 2 ep) => /=; rewrite ge2_ep /= expr2. 
lemma ge8_q: 8 <= q by move: (IntOrder.ler_weexpn2l 2) => /= mn; move: (mn 3 eq) => /=; rewrite ge3_eq /= (exprS 2 2) // expr2.

lemma geeq1_2ep: eq + 1 <= 2 * ep.
proof.
  have le0_eq2ep: eq - ep - ep <= -1.
   apply (lez_trans (-et - 1) (eq - ep - ep) (-1)). 
    by move: (lez_add2l (-ep) (eq - ep) (ep - et - 1)); rewrite sec_assumption addzC 2!addzA.
    by rewrite -(lez_add2r (et + 1) (-et - 1) (-1)) addzA addzC addzA /= ge0_et.
  by rewrite mulzC -(intmulz ep 2) mulr2z -(lez_add2r (-1) _ _) /= 
             -(lez_add2l ((-(ep + ep))) _ _) addzA /= addzC opprD addzA.
qed.  

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

lemma q_div_pp: q %| p * p.
proof.
  rewrite /p /q -exprD_nneg; first 2 by apply /(IntOrder.ler_trans 2 0 ep) /ge2_ep.
  rewrite dvdz_exp2l; split; [by apply /(lez_trans 3 0 eq) /ge3_eq | move => ?]. 
  by rewrite -mul1r2z mulrC /ofint_id intmulz /= (lez_trans (eq + 1) _ _); 
             [rewrite (lez_addl eq 1) | apply geeq1_2ep].
qed.

lemma ge2_ppq: 2 <= p * p %/ q.
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

lemma eq_22epeq_ppq: 2 ^ (2 * ep - eq) = p * p %/ q.
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
(* -- Zq = Z/qZ -- *)
type Zq.

clone import ZModRing as Zq with
    op p <- q,
    type zmod <- Zq
  proof ge2_p by apply /(lez_trans 8 2 q) /ge8_q.

clone import MFinite as DZq with
    type t <- Zq,
    op Support.card <- q.

op dZq : Zq distr = DZq.dunifin.

clone Matrix as Mat_Zq with
    type R <- Zq,
    op size <- l
  proof ge0_size by apply /(lez_trans 1 0 l) /ge1_l.

type Zq_vec = Mat_Zq.vector.
type Zq_mat = Mat_Zq.Matrix.matrix.

op dZq_vec : Zq_vec distr = Mat_Zq.Matrix.dvector dZq.
op dZq_mat : Zq_mat distr = Mat_Zq.Matrix.dmatrix dZq.

op [lossless] dsmallZq : Zq distr.
op dsmallZq_vec : Zq_vec distr =  Mat_Zq.Matrix.dvector dsmallZq.

(* -- Zp = Z/pZ -- *)
type Zp.

clone import ZModRing as Zp with
    op p <- p,
    type zmod <- Zp
  proof ge2_p by apply /(lez_trans 4 2 p) /ge4_p.

clone import MFinite as DZp with
    type t <- Zp,
    op Support.card <- p.

op dZp : Zp distr = DZp.dunifin.

clone Matrix as Mat_Zp with
    type R <- Zp,
    op size <- l
  proof ge0_size by apply /(lez_trans 1 0 l) /ge1_l.

type Zp_vec = Mat_Zp.vector.

op dZp_vec : Zp_vec distr = Mat_Zp.Matrix.dvector dZp.

(* -- Zppq = Z/ppqZ -- *)
type Zppq.

clone import ZModRing as Zppq with
    op p <- p * p %/ q,
    type zmod <- Zppq
  proof ge2_p by apply ge2_ppq.

(* -- Z2t = Z/2tZ  -- *)
type Z2t.

clone import ZModRing as Z2t with
    op p <- 2 * t,
    type zmod <- Z2t
    proof ge2_p by apply ge2_2t.

(* -- Z2 = Z/2Z -- *)
type Z2.

clone import ZModRing as Z2 with
    op p <- 2,
    type zmod <- Z2
    proof ge2_p by apply lezz.

(* - Properties - *)
(* Vector distribution has same properties as the distribution of the vector's elements *)
lemma dZq_vec_ll: is_lossless dZq_vec.
proof. apply Mat_Zq.Matrix.dvector_ll; rewrite /dZq; apply /DZq.dunifin_ll. qed.

lemma dZq_vec_uni: is_uniform dZq_vec.
proof. apply /Mat_Zq.Matrix.dvector_uni; rewrite /dZq; apply /DZq.dunifin_uni. qed.

lemma dZq_vec_fu: is_full dZq_vec.
proof. apply /Mat_Zq.Matrix.dvector_fu; rewrite /dZq; apply /DZq.dunifin_fu. qed.

lemma dZp_vec_ll: is_lossless dZp_vec.
proof. apply /Mat_Zp.Matrix.dvector_ll; rewrite /dZp; apply /DZp.dunifin_ll. qed.

lemma dZp_vec_uni: is_uniform dZp_vec.
proof. apply /Mat_Zp.Matrix.dvector_uni; rewrite /dZp; apply /DZp.dunifin_uni. qed.

lemma dZp_vec_fu: is_full dZp_vec.
proof. apply /Mat_Zp.Matrix.dvector_fu; rewrite /dZp; apply /DZp.dunifin_fu. qed.

lemma dsmallZq_vec_ll: is_lossless dsmallZq_vec.
proof. apply /Mat_Zq.Matrix.dvector_ll /dsmallZq_ll. qed.

(* Matrix Distribution has same properties as the distribution of the matrix's elements *)
lemma dZq_mat_ll: is_lossless dZq_mat.
proof. apply /Mat_Zq.Matrix.dmatrix_ll; rewrite /dZq; apply /DZq.dunifin_ll. qed.

lemma dZq_mat_uni: is_uniform dZq_mat.
proof. apply /Mat_Zq.Matrix.dmatrix_uni; rewrite /dZq; apply /DZq.dunifin_uni. qed.

lemma dZq_mat_fu: is_full dZq_mat.
proof. apply /Mat_Zq.Matrix.dmatrix_fu; rewrite /dZq; apply /DZq.dunifin_fu. qed.

(* - Imports - *)
import Mat_Zq.
import Mat_Zp.

(* - Constants - *)
const h1 : Zq = Zq.inzmod (2 ^(eq - ep - 1)).
const h2 : Zq = Zq.inzmod (2^(ep - 2) - 2^(ep - et - 2)).
const h : Zq_vec = vectc h1.
 
(* -- Cryptographic Types and Distributions  -- *)
type seed.
type pkey.
type skey.
type plaintext.
type ciphertext.

op [lossless full uniform] dseed : seed distr.

(* -- Operations -- *)
op gen : seed -> Zq_mat.

op shl (x : int, ex : int) : int = x * 2^ex.
op shr (x : int, ex : int) : int = x %/ 2^ex.

op scale (x : int, ea : int, eb : int) : int = shr x (ea - eb).
op scale_q_p (x : Zq) : Zp = Zp.inzmod (scale (Zq.asint x) eq ep).
op scale_p_2t (x : Zp) : Z2t = Z2t.inzmod (scale (Zp.asint x) ep (et + 1)).
op scale_p_2 (x : Zp) : Z2 = Z2.inzmod (scale (Zp.asint x) ep 1).
op scale_p_ppq (x : Zp) : Zppq = Zppq.inzmod (scale (Zp.asint x) ep (2 * ep - eq)).
op scale_p_p (x : Zp) : Zp = Zp.inzmod (scale (Zp.asint x) ep ep).
op scale_ppq_2t (x : Zppq) : Z2t = Z2t.inzmod (scale (Zppq.asint x) (2 * ep - eq) (et + 1)).
op scale_vec_q_p (v : Zq_vec) : Zp_vec = offunv (fun i => scale_q_p v.[i]).

op mod_p_Zq_vec (v : Zq_vec) : Zp_vec = offunv (fun i => Zp.inzmod (Zq.asint v.[i])).

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
(*
axiom mapZqZp_mod: dmap dZq_vec mod_p_Zq_vec = dZp_vec.
 *)
(* Essentially Proves: (x %/ 2^(a - b)) %/ 2^(b - c) == x %/ 2^(a - c) *)
lemma scale_comp (x ea eab eb : int):
      0 <= x => 0 <= eb => eb <= eab => eab <= ea =>
      scale x ea eb = scale (scale x ea eab) eab eb. 
proof. 
  (* Context and readability *)
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

lemma scale_comp_p_ppq_2t (x : Zp):
      scale_p_2t x = scale_ppq_2t (scale_p_ppq x).
proof. 
  rewrite /scale_p_2t /scale_ppq_2t /scale_p_ppq inzmodK -eq_inzmod; do 2! congr.
  have ge2epeq_ep: 2 * ep - eq <= ep.
   by rewrite mulzC -intmulz mulr2z -(lez_add2l (-ep) _ _) -addzA addzCA addzA /= subz_le0 (lez_trans (ep + 1) ep eq);
              [rewrite (lez_addl _ 1) | apply geep1_eq ].
  rewrite (modz_small (scale (asint x) ep (2 * ep - eq)) (p * p %/ q)); first split; 
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

lemma scale_id (x ea eb : int) : ea = eb => scale x ea eb = x.
by move=> eq_eaeb; rewrite /scale /shr eq_eaeb addzN expr0. qed.

lemma scale_p_p_id (x : Zp) : scale_p_p x = x.
proof. by rewrite /scale_p_p scale_id; [trivial | rewrite asintK]. qed.
