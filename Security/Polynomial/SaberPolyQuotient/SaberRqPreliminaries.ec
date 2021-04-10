(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr ZModP IntDiv StdOrder.
require (*--*) Matrix PKE.
(*---*) import IntOrder.

(* --- Local --- *)
require (*--*) SaberPolyQuotientRing SaberMatrix PolyReduce.

(* ----------------------------------- *)
(*  General Preliminaries              *)
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

lemma ge1_n : 1 <= n by rewrite exprn_ege1 1:ge0_en.
lemma ge1_t: 1 <= t by rewrite exprn_ege1 1:ge0_et.
lemma ge2_2t: 2 <= 2 * t by move: (ler_pmul2l 2 _ 1 t); rewrite // ge1_t //.
lemma ge4_p: 4 <= p by move: (ler_weexpn2l 2 _ 2 ep); rewrite //= ge2_ep /= expr2.
lemma ge8_q: 8 <= q by move: (ler_weexpn2l 2 _ 3 eq); rewrite //= ge3_eq /= (exprS 2 2) // expr2.

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
  by apply /(lez_trans (et + 2) (et + 1) ep) /geet2_ep /(ler_add et et 1 2).
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
  rewrite /p /q -exprD_nneg; first 2 by apply /(ler_trans 2 0 ep) /ge2_ep.
  rewrite dvdz_exp2l; split; [by apply /(lez_trans 3 0 eq) /ge3_eq | move => ?]. 
  by rewrite -mul1r2z mulrC /ofint_id intmulz /= (lez_trans (eq + 1) _ _); 
             [rewrite (lez_addl eq 1) | apply geeq1_2ep].
qed.

lemma ge2_ppq: 2 <= (p * p) %/ q.
proof.
  apply (ler_pmul2r q); first by rewrite /q expr_gt0.
   have ->: p * p %/ q * q = p * p.
    by rewrite -(dvdz_eq q (p * p)) q_div_pp.
   rewrite /p /q -exprS; first by apply /(lez_trans 3 0 eq) /ge3_eq.
    rewrite -exprD_nneg; first 2 by apply /(lez_trans 2 0 ep) /ge2_ep.
     apply ler_weexpn2l; split; [by apply (lez_trans eq 0 (eq + 1)); 
           [apply /(lez_trans 3 0 eq) /ge3_eq | rewrite (lez_addl eq 1)] |].
      by rewrite -mul1r2z mulrC /ofint_id intmulz /= geeq1_2ep.
qed.

lemma eq_22epeq_ppq: 2 ^ (2 * ep - eq) = (p * p) %/ q.
proof.
  apply (mulfI q); [by rewrite neq_ltz; right; apply expr_gt0 | rewrite mulzC -(mulzC (p * p %/ q) _)].  
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

clone import ZModRing as Zq with
    type zmod <- Zq,
    op p <- q
  proof ge2_p by apply (lez_trans 8 _ _ _ ge8_q).

clone import PolyReduce as Rq with
    type BasePoly.coeff      <- Zq,
    pred BasePoly.Coeff.unit <- Zq.unit,
    op BasePoly.Coeff.zeror  <- Zq.zero,
    op BasePoly.Coeff.oner   <- Zq.one,
    op BasePoly.Coeff.( + )  <- Zq.( + ),
    op BasePoly.Coeff.([-])  <- Zq.([-]),
    op BasePoly.Coeff.( * )  <- Zq.( * ),
    op BasePoly.Coeff.invr   <- Zq.inv,
    type polyXnD1            <- Rq,
    op n                     <- n
  proof gt0_n                    by rewrite -lez_add1r /= ge1_n
  proof BasePoly.Coeff.addrA     by exact Zq.ZModpRing.addrA
  proof BasePoly.Coeff.addrC     by exact Zq.ZModpRing.addrC
  proof BasePoly.Coeff.add0r     by exact Zq.ZModpRing.add0r
  proof BasePoly.Coeff.addNr     by exact Zq.ZModpRing.addNr
  proof BasePoly.Coeff.oner_neq0 by exact Zq.ZModpRing.oner_neq0
  proof BasePoly.Coeff.mulrA     by exact Zq.ZModpRing.mulrA
  proof BasePoly.Coeff.mulrC     by exact Zq.ZModpRing.mulrC
  proof BasePoly.Coeff.mul1r     by exact Zq.ZModpRing.mul1r
  proof BasePoly.Coeff.mulrDl    by exact Zq.ZModpRing.mulrDl
  proof BasePoly.Coeff.mulVr     by exact Zq.ZModpRing.mulVr
  proof BasePoly.Coeff.unitP     by exact Zq.ZModpRing.unitP
  proof BasePoly.Coeff.unitout   by exact Zq.ZModpRing.unitout.

clone Matrix as Mat_Rq with 
    type R <- Rq,
    op size <- l
  proof ge0_size by apply (lez_trans 1 _ _ _ ge1_l).

clone import MFinite as DRq with
    type t <- Rq,
    op Support.card <- q ^ n.
    
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

clone import ZModRing as Zp with
    type zmod <- Zp,
    op p <- p
  proof ge2_p by apply (lez_trans 4 _ _ _ ge4_p).

clone import PolyReduce as Rp with
    type BasePoly.coeff      <- Zp,
    pred BasePoly.Coeff.unit <- Zp.unit,
    op BasePoly.Coeff.zeror  <- Zp.zero,
    op BasePoly.Coeff.oner   <- Zp.one,
    op BasePoly.Coeff.( + )  <- Zp.( + ),
    op BasePoly.Coeff.([-])  <- Zp.([-]),
    op BasePoly.Coeff.( * )  <- Zp.( * ),
    op BasePoly.Coeff.invr   <- Zp.inv,
    type polyXnD1            <- Rp,
    op n                     <- n
  proof gt0_n                    by rewrite -lez_add1r /= ge1_n
  proof BasePoly.Coeff.addrA     by exact Zp.ZModpRing.addrA
  proof BasePoly.Coeff.addrC     by exact Zp.ZModpRing.addrC
  proof BasePoly.Coeff.add0r     by exact Zp.ZModpRing.add0r
  proof BasePoly.Coeff.addNr     by exact Zp.ZModpRing.addNr
  proof BasePoly.Coeff.oner_neq0 by exact Zp.ZModpRing.oner_neq0
  proof BasePoly.Coeff.mulrA     by exact Zp.ZModpRing.mulrA
  proof BasePoly.Coeff.mulrC     by exact Zp.ZModpRing.mulrC
  proof BasePoly.Coeff.mul1r     by exact Zp.ZModpRing.mul1r
  proof BasePoly.Coeff.mulrDl    by exact Zp.ZModpRing.mulrDl
  proof BasePoly.Coeff.mulVr     by exact Zp.ZModpRing.mulVr
  proof BasePoly.Coeff.unitP     by exact Zp.ZModpRing.unitP
  proof BasePoly.Coeff.unitout   by exact Zp.ZModpRing.unitout.

clone Matrix as Mat_Rp with 
    type R <- Rp,
    op size <- l
  proof ge0_size by apply (lez_trans 1 _ _ _ ge1_l).

clone import MFinite as DRp with
    type t <- Rp,
    op Support.card <- p ^ n.  

type Rp_vec = Mat_Rp.vector.

op dRp : Rp distr = DRp.dunifin. 
op dRp_vec : Rp_vec distr = Mat_Rp.Matrix.dvector dRp.

(* -- Rppq = Z/ppqZ [X] / (X^n + 1) -- *)
type Zppq.
type Rppq.

clone import ZModRing as Zppq with
    type zmod <- Zppq,
    op p      <- (p * p) %/ q
  proof ge2_p by apply ge2_ppq.

clone import PolyReduce as Rppq with
    type BasePoly.coeff      <- Zppq,
    pred BasePoly.Coeff.unit <- Zppq.unit,
    op BasePoly.Coeff.zeror  <- Zppq.zero,
    op BasePoly.Coeff.oner   <- Zppq.one,
    op BasePoly.Coeff.( + )  <- Zppq.( + ),
    op BasePoly.Coeff.([-])  <- Zppq.([-]),
    op BasePoly.Coeff.( * )  <- Zppq.( * ),
    op BasePoly.Coeff.invr   <- Zppq.inv,
    op BasePoly.Coeff.intmul <- Zppq.ZModpRing.intmul,
    op BasePoly.Coeff.ofint  <- Zppq.ZModpRing.ofint,
    op BasePoly.Coeff.exp    <- Zppq.ZModpRing.exp,
    type polyXnD1            <- Rppq,
    op n                     <- n
  proof gt0_n                    by rewrite -lez_add1r /= ge1_n
  proof BasePoly.Coeff.addrA     by exact Zppq.ZModpRing.addrA
  proof BasePoly.Coeff.addrC     by exact Zppq.ZModpRing.addrC
  proof BasePoly.Coeff.add0r     by exact Zppq.ZModpRing.add0r
  proof BasePoly.Coeff.addNr     by exact Zppq.ZModpRing.addNr
  proof BasePoly.Coeff.oner_neq0 by exact Zppq.ZModpRing.oner_neq0
  proof BasePoly.Coeff.mulrA     by exact Zppq.ZModpRing.mulrA
  proof BasePoly.Coeff.mulrC     by exact Zppq.ZModpRing.mulrC
  proof BasePoly.Coeff.mul1r     by exact Zppq.ZModpRing.mul1r
  proof BasePoly.Coeff.mulrDl    by exact Zppq.ZModpRing.mulrDl
  proof BasePoly.Coeff.mulVr     by exact Zppq.ZModpRing.mulVr
  proof BasePoly.Coeff.unitP     by exact Zppq.ZModpRing.unitP
  proof BasePoly.Coeff.unitout   by exact Zppq.ZModpRing.unitout.

(* -- R2t = Z/2tZ [X] / (X^n + 1)  -- *)
type Z2t.
type R2t.

clone import ZModRing as Z2t with
    type zmod <- Z2t,
    op p <- 2 * t
  proof ge2_p by apply ge2_2t.

clone import PolyReduce as R2t with
    type BasePoly.coeff      <- Z2t,
    pred BasePoly.Coeff.unit <- Z2t.unit,
    op BasePoly.Coeff.zeror  <- Z2t.zero,
    op BasePoly.Coeff.oner   <- Z2t.one,
    op BasePoly.Coeff.( + )  <- Z2t.( + ),
    op BasePoly.Coeff.([-])  <- Z2t.([-]),
    op BasePoly.Coeff.( * )  <- Z2t.( * ),
    op BasePoly.Coeff.invr   <- Z2t.inv,
    op BasePoly.Coeff.intmul <- Z2t.ZModpRing.intmul,
    op BasePoly.Coeff.ofint  <- Z2t.ZModpRing.ofint,
    op BasePoly.Coeff.exp    <- Z2t.ZModpRing.exp,
    type polyXnD1            <- R2t,
    op n                     <- n
  proof gt0_n                    by rewrite -lez_add1r /= ge1_n
  proof BasePoly.Coeff.addrA     by exact Z2t.ZModpRing.addrA
  proof BasePoly.Coeff.addrC     by exact Z2t.ZModpRing.addrC
  proof BasePoly.Coeff.add0r     by exact Z2t.ZModpRing.add0r
  proof BasePoly.Coeff.addNr     by exact Z2t.ZModpRing.addNr
  proof BasePoly.Coeff.oner_neq0 by exact Z2t.ZModpRing.oner_neq0
  proof BasePoly.Coeff.mulrA     by exact Z2t.ZModpRing.mulrA
  proof BasePoly.Coeff.mulrC     by exact Z2t.ZModpRing.mulrC
  proof BasePoly.Coeff.mul1r     by exact Z2t.ZModpRing.mul1r
  proof BasePoly.Coeff.mulrDl    by exact Z2t.ZModpRing.mulrDl
  proof BasePoly.Coeff.mulVr     by exact Z2t.ZModpRing.mulVr
  proof BasePoly.Coeff.unitP     by exact Z2t.ZModpRing.unitP
  proof BasePoly.Coeff.unitout   by exact Z2t.ZModpRing.unitout.

(* -- R2 = Z/2Z [X] / (X^n + 1) -- *)
type Z2.
type R2.

clone import ZModRing as Z2 with
    type zmod <- Z2,
    op p <- 2
  proof ge2_p by apply lezz.

clone import PolyReduce as R2 with
    type BasePoly.coeff      <- Z2,
    pred BasePoly.Coeff.unit <- Z2.unit,
    op BasePoly.Coeff.zeror  <- Z2.zero,
    op BasePoly.Coeff.oner   <- Z2.one,
    op BasePoly.Coeff.( + )  <- Z2.( + ),
    op BasePoly.Coeff.([-])  <- Z2.([-]),
    op BasePoly.Coeff.( * )  <- Z2.( * ),
    op BasePoly.Coeff.invr   <- Z2.inv,
    op BasePoly.Coeff.intmul <- Z2.ZModpRing.intmul,
    op BasePoly.Coeff.ofint  <- Z2.ZModpRing.ofint,
    op BasePoly.Coeff.exp    <- Z2.ZModpRing.exp,
    type polyXnD1            <- R2,
    op n                     <- n
  proof gt0_n                    by rewrite -lez_add1r /= ge1_n
  proof BasePoly.Coeff.addrA     by exact Z2.ZModpRing.addrA
  proof BasePoly.Coeff.addrC     by exact Z2.ZModpRing.addrC
  proof BasePoly.Coeff.add0r     by exact Z2.ZModpRing.add0r
  proof BasePoly.Coeff.addNr     by exact Z2.ZModpRing.addNr
  proof BasePoly.Coeff.oner_neq0 by exact Z2.ZModpRing.oner_neq0
  proof BasePoly.Coeff.mulrA     by exact Z2.ZModpRing.mulrA
  proof BasePoly.Coeff.mulrC     by exact Z2.ZModpRing.mulrC
  proof BasePoly.Coeff.mul1r     by exact Z2.ZModpRing.mul1r
  proof BasePoly.Coeff.mulrDl    by exact Z2.ZModpRing.mulrDl
  proof BasePoly.Coeff.mulVr     by exact Z2.ZModpRing.mulVr
  proof BasePoly.Coeff.unitP     by exact Z2.ZModpRing.unitP
  proof BasePoly.Coeff.unitout   by exact Z2.ZModpRing.unitout.

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
import Rq.RingQuotient Rq.BasePoly. 
import Rp.RingQuotient Rp.BasePoly.
import Rppq.RingQuotient Rppq.BasePoly.
import R2t.RingQuotient R2t.BasePoly.
import R2.RingQuotient R2.BasePoly.

(* - Constants - *)
const h1 : Rq = pi (to_polyd (fun _ => Zq.inzmod (2 ^ (eq - ep - 1)))).
const h2 : Rq = pi (to_polyd (fun _ => Zq.inzmod (2 ^ (ep - 2) - 2 ^ (ep - et - 2)))).
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

op shl (x : int, ex : int) : int = x * 2 ^ ex.
op shl_enc (x : R2, ex : int) : Rp = pi (to_polyd (fun i => Zp.inzmod (shl (Z2.asint x.[i]) ex))).
op shl_dec (x : R2t) : Rp = pi (to_polyd (fun i => Zp.inzmod (shl (Z2t.asint x.[i]) (ep - et - 1)))).

op shr (x : int, ex : int) : int = x %/ 2 ^ ex.

op scale (x : int, ea : int, eb : int) : int = shr x (ea - eb).

op scale_Zq_Zp (x : Zq) : Zp = Zp.inzmod (scale (Zq.asint x) eq ep).
op scale_Zp_Z2t (x : Zp) : Z2t = Z2t.inzmod (scale (Zp.asint x) ep (et + 1)).
op scale_Zp_Z2 (x : Zp) : Z2 = Z2.inzmod (scale (Zp.asint x) ep 1).
op scale_Zp_Zppq (x : Zp) : Zppq = Zppq.inzmod (scale (Zp.asint x) ep (2 * ep - eq)).
op scale_Zp_Zp (x : Zp) : Zp = Zp.inzmod (scale (Zp.asint x) ep ep).
op scale_Zppq_Z2t (x : Zppq) : Z2t = Z2t.inzmod (scale (Zppq.asint x) (2 * ep - eq) (et + 1)).

op scale_Rq_Rp (x : Rq) : Rp = pi (to_polyd (fun i => scale_Zq_Zp x.[i])).
op scale_Rp_R2t (x : Rp) : R2t = pi (to_polyd (fun i => scale_Zp_Z2t x.[i])).
op scale_Rp_R2 (x : Rp) : R2 = pi (to_polyd (fun i => scale_Zp_Z2 x.[i])).
op scale_Rp_Rppq (x : Rp) : Rppq = pi (to_polyd (fun i => scale_Zp_Zppq x.[i])).
op scale_Rp_Rp (x : Rp) : Rp = pi (to_polyd (fun i => scale_Zp_Zp x.[i])).
op scale_Rppq_R2t (x : Rppq) : R2t = pi (to_polyd (fun i => scale_Zppq_Z2t x.[i])).

op scale_vec_Rq_Rp (v : Rq_vec) : Rp_vec = offunv (fun i => scale_Rq_Rp v.[i]).

op mod_p_Rq (x : Rq) : Rp = pi (to_polyd (fun i => Zp.inzmod (Zq.asint x.[i]))).
op mod_p_Rq_vec (v : Rq_vec) : Rp_vec = offunv (fun i => mod_p_Rq v.[i]).

op mod_q_Rp (x : Rp) : Rq = pi (to_polyd (fun i => Zq.inzmod (Zp.asint x.[i]))).
op mod_q_Rp_vec (v : Rp_vec) : Rq_vec = offunv (fun i => mod_q_Rp v.[i]).

op mod_ppq_Rp (x : Rp) : Rppq =  pi (to_polyd (fun i => Zppq.inzmod (Zp.asint x.[i]))).

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
  + by apply expr_gt0.
  have gt0_d1: 0 < d1.
  + by apply expr_gt0.

  have eq_dmain_d0d1: dmain = d0 * d1.
  + rewrite /dmain /d0 /d1 -exprD_nneg. 
    - by rewrite -(lez_add2r eab 0 (ea - eab)) -addrA /= geeab_ea.
    - by rewrite -(lez_add2r eb 0 (eab - eb)) -addrA /= geeb_eab.
    - by congr; rewrite -addzA addKz.

  (* Main Proof *)
  move: (euclideU dmain qmain (q0 %/ d1) rmain (q0 %% d1 * d0 + r0)).
  + have <-: x = q0 %/ d1 * dmain + (q0 %% d1 * d0 + r0).
    - by rewrite eq_dmain_d0d1 (mulzC d0 d1) -(mulzA (q0 %/ d1)) addzA -(mulzDl _ _ d0) -div1.
  rewrite -divmain /=.  
  + have -> /=: 0 <= rmain && rmain < `| dmain |.
    - split; [by apply /modn_ge0 /ge0_x | move => ge0_rmain].
      * by rewrite ltz_mod neq_ltz; right; apply expr_gt0.
  + have -> /=:  0 <= q0 %% d1 * d0 + r0 && q0 %% d1 * d0 + r0 < `| dmain |.
    - split; 1: by apply /addz_ge0 /modn_ge0 /ge0_x /mulr_ge0 /ltzW /gt0_d0 /modz_ge0 /neq_ltz; right.
      * rewrite ger0_norm eq_dmain_d0d1; first by rewrite mulr_ge0 ltzW.
        rewrite (ltr_le_trans ((d1 - 1) * d0 + d0) _ (d0 * d1)) 3://.
        + apply (ler_lt_add _ _ r0 d0); last by apply ltz_pmod.
          apply /(ler_pmul _ _ d0 d0) /lezz; [by apply /modz_ge0 /neq_ltz; right | by apply ltzW |].
          by apply (lez_add2l 1); rewrite lez_add1r -addzCA /= ltz_pmod.
        + by rewrite mulzDl mulNr /= -addzA addNz /= mulzC; apply lezz.
   by case.
qed.

lemma ispoly_fun_scale_Zq_Zp (x : Rq) : ispoly (fun i => scale_Zq_Zp x.[i]).
proof.
  split; [| exists (deg (crepr x) - 1)] => [c lt0_c | c gtdeg1_c] /=;
         rewrite /scale_Zq_Zp /scale /shr; have ->: asint x.[c] = 0; 
         2, 4: by rewrite div0z -Zp.zeroE asintK. 
  + by rewrite lt0_coeff 2:-Zq.zeroE.
  + by rewrite gedeg_coeff 2:-Zq.zeroE; rewrite -lez_add1r addzC /= in gtdeg1_c.
qed.

lemma ispoly_fun_scale_Zp_Zppq (x : Rp) : ispoly (fun i => scale_Zp_Zppq x.[i]).
proof.
  split; [| exists (deg (crepr x) - 1)] => [c lt0_c | c gtdeg1_c] /=;
         rewrite /scale_Zp_Zppq /scale /shr; have ->: asint x.[c] = 0; 
         2, 4: by rewrite div0z -Zppq.zeroE asintK. 
  + by rewrite lt0_coeff 2:-Zp.zeroE.
  + by rewrite gedeg_coeff 2:-Zp.zeroE; rewrite -lez_add1r addzC /= in gtdeg1_c.
qed.

lemma ispoly_fun_scale_Zp_Zp (x : Rp) : ispoly (fun i => scale_Zp_Zp x.[i]).
proof.
  split; [| exists (deg (crepr x) - 1)] => [c lt0_c | c gtdeg1_c] /=;
         rewrite /scale_Zp_Zp /scale /shr; have ->: asint x.[c] = 0; 
         2, 4: by rewrite div0z -Zp.zeroE asintK. 
  + by rewrite lt0_coeff 2:-Zp.zeroE.
  + by rewrite gedeg_coeff 2:-Zp.zeroE; rewrite -lez_add1r addzC /= in gtdeg1_c.
qed.

lemma reduced_topolyd_scale_Zq_Zp (x : Rq): 
      reduced (to_polyd (fun i => scale_Zq_Zp x.[i])).
proof.
  rewrite reducedP deg_leP 1:ge0_n => i gen_i; rewrite coeffE 2:/= 1:ispoly_fun_scale_Zq_Zp.
  rewrite /scale_Zq_Zp /scale /shr; have ->: asint x.[i] = 0; 2: by rewrite div0z -Zp.zeroE asintK.
  by rewrite -Zq.zeroE Zq.asint_eq gedeg_coeff 1:(lez_trans n) /crepr 1:deg_reduce.
qed.

lemma reduced_topolyd_scale_Zp_Zppq (x : Rp): 
      reduced (to_polyd (fun i => scale_Zp_Zppq x.[i])).
proof.
  rewrite reducedP deg_leP 1:ge0_n => i gen_i; rewrite coeffE 2:/= 1:ispoly_fun_scale_Zp_Zppq.
  rewrite /scale_Zp_Zppq /scale /shr; have ->: asint x.[i] = 0; 2: by rewrite div0z -Zppq.zeroE asintK.
  by rewrite -Zp.zeroE Zp.asint_eq gedeg_coeff 1:(lez_trans n) /crepr 1:deg_reduce.
qed.

lemma scale_comp_Zp_Zppq_Z2t (x : Zp):
      scale_Zp_Z2t x = scale_Zppq_Z2t (scale_Zp_Zppq x).
proof. 
  rewrite /scale_Zp_Z2t /scale_Zppq_Z2t /scale_Zp_Zppq Zppq.inzmodK -Z2t.eq_inzmod; do 2! congr.
  have ge2epeq_ep: 2 * ep - eq <= ep.
  + by rewrite mulzC -intmulz mulr2z -(lez_add2l (-ep)) -addzA addzCA addzA /= 
               subz_le0 (lez_trans (ep + 1)); [rewrite (lez_addl _ 1) | apply geep1_eq].
  rewrite (modz_small (scale (Zp.asint x) ep (2 * ep - eq)) (p * p %/ q)); first split; 
          rewrite /scale /shr => [| ?].
  + by apply /divz_ge0 /Zp.ge0_asint /expr_gt0.
  + rewrite ger0_norm; first by apply /(lez_trans 2) /ge2_ppq. 
    apply ltz_divLR; first by apply expr_gt0. 
    rewrite -eq_22epeq_ppq -exprD_nneg; first by rewrite subz_ge0 (lez_trans (eq + 1)); 
            [rewrite (lez_addl _ 1) | apply geeq1_2ep].
    - by rewrite subz_ge0.
    - by rewrite mulzC -intmulz mulr2z addzCA /= (ltr_le_trans p) 2:lezz Zp.gtp_asint.
  apply /(scale_comp (Zp.asint x)) /ge2epeq_ep; [apply Zp.ge0_asint | by apply /(lez_trans 1) /ge1_et1 |].
  rewrite mulzC -intmulz mulr2z -(lez_add2r (-(et + 1))) /= -(lez_add2l (eq)) addzAC addzCA /= 
          -(lez_add2r (-ep)) addzAC (subrK ep (-ep)) opprD addzA.
  by apply sec_assumption.
qed.

lemma scale_comp_Rp_Rppq_R2t (x : Rp):
      scale_Rp_R2t x = scale_Rppq_R2t (scale_Rp_Rppq x).
proof.
  rewrite /scale_Rp_R2t /scale_Rppq_R2t /scale_Rp_Rppq; do 2! congr; rewrite fun_ext /(==) => i. 
  by rewrite piK 1:reduced_topolyd_scale_Zp_Zppq coeffE 
             1:ispoly_fun_scale_Zp_Zppq /= scale_comp_Zp_Zppq_Z2t.
qed.

lemma scale_id (x ea eb : int) : ea = eb => scale x ea eb = x.
proof. by move=> eq_eaeb; rewrite /scale /shr eq_eaeb addzN expr0. qed.

lemma scale_Zp_Zp_id (x : Zp) : scale_Zp_Zp x = x.
proof. by rewrite /scale_Zp_Zp scale_id 2: Zp.asintK. qed.

lemma scale_Rp_Rp_id (x : Rp) : scale_Rp_Rp x = x.
proof. 
  rewrite /scale_Rp_Rp -{2}creprK; congr.
  rewrite poly_eqP => c ge0_c; rewrite coeffE /= 1:ispoly_fun_scale_Zp_Zp &(scale_Zp_Zp_id). 
qed.

lemma mod_p_Zq_h1_id : 
      Zp.asint (Zp.inzmod (2 ^ (eq - ep - 1))) 
      = 
      Zq.asint (Zq.inzmod (2 ^ (eq - ep - 1))).
proof.
  rewrite Zp.inzmodK Zq.inzmodK ?modz_small /p /q //; first 2 split => [| ?];
          [by apply expr_ge0 |
           rewrite ger0_norm ?expr_ge0 // ltz_def ler_weexpn2l // ?andbT; first split => [| ?]; 
           1: rewrite -(lez_add2r 1) /= -(lez_add2r ep) -addzA addzC /= geep1_eq].
  + by rewrite -(lez_add2r ep) addzAC addzC -addzA addzC -mulr2z intmulz mulzC (lez_trans (eq + 1)) 
           1:-(lez_add2r 1) /= 1:lez_addl // geeq1_2ep.
  + move: (ieexprIn 2 _ _ ep (eq - ep - 1) (lez_trans 2 0 ep _ ge2_ep) _) => //.
    - by rewrite -(lez_add2r 1) /= -(lez_add2r ep) -addzA /= addzC geep1_eq.   
    move /contra; apply; rewrite neq_ltz; right.
    by rewrite -(ltz_add2l ep) /= addzCA addzC addzA addzC 2!addzA addzC /= -mulr2z intmulz mulzC 
                (ltr_le_trans (eq + 1)) 1: ltz_add2l 2: geeq1_2ep.
  + by rewrite -(lez_add2l (-eq)) 2!addzA /= -(lez_add2l ep) addzA /= (lez_trans 2) // ge2_ep.
  + move: (ieexprIn 2 _ _ eq (eq - ep - 1) (lez_trans 3 0 eq _ ge3_eq) _) => //.
    - by rewrite -(lez_add2r 1) /= -(lez_add2r ep) -addzA /= addzC geep1_eq.
    move /(contra); apply; rewrite neq_ltz; right.
   by rewrite -(ltz_add2l (-eq)) 2!addzA /= -(ltz_add2l ep) addzA /= (ltr_le_trans 2) 2:ge2_ep.
qed.

lemma eq_scaleZqZp_modZppq_scaleZpZppq (x : Zq) (m : Z2) :
      Zppq.inzmod (Zp.asint ( (scale_Zq_Zp x) + (Zp.inzmod (shl (Z2.asint m) (2 * ep - eq - 1)))))
      =
      scale_Zp_Zppq ((Zp.inzmod (Zq.asint x)) + Zp.inzmod (shl (Z2.asint m) (ep - 1))).
proof.
  rewrite /scale_Zq_Zp /scale_Zp_Zppq /scale /shr /shl !Zp.inzmodK !modzDm 
          {2}(mulzC 2) -(intmulz ep) mulr2z !opprD !addzA /= (addzC _ eq).
  have ge0_eqep: 0 <= eq - ep; 1: by apply /(lez_trans 1) /(lez_add2l ep); 
       2: rewrite addzCA /= geep1_eq.
  have leep_eq_ep: eq - ep <= ep; 1: by rewrite -(lez_add2r ep) -addzA /= -mulr2z intmulz mulzC 
                                                 (lez_trans (eq + 1)) 2:geeq1_2ep lez_addl.
  have ge0_2epeq: 0 <= 2 * ep - eq; 1: by rewrite -(lez_add2r eq) -addzA /= (lez_trans (eq + 1)) 
                                                  2:geeq1_2ep lez_addl.
  have leep_2epeq: 2 * ep - eq <= ep; first rewrite mulzC -intmulz mulr2z -(lez_add2l (-ep)) 2!addzA;
       move: (oppz_le0 (eq - ep)); rewrite ge0_eqep opprD /= addzC => -> //.
  case: (Z2.asint m = 0) => [-> /= | /neq_ltz]; last case => [lt0_m | gt0_m]; 
        move: (Z2.Sub.valP m) => [ge0_m lt2_m].
  + by rewrite -Zppq.eq_inzmod -eq_22epeq_ppq /p /q (modz_pow2_div); 
               [apply Zq.ge0_asint | 
                split | 
                rewrite opprD (addzC _ ep) addzA -mulr2z intmulz (mulzC ep) modz_mod modz_dvd_pow].
  + by rewrite -/Z2.asint lezNgt in ge0_m.
  have -> /= {gt0_m ge0_m lt2_m}: Z2.asint m = 1; first rewrite eqz_leq; split. 
  + by rewrite -/Z2.asint -lez_add1r -(lez_add2l (-1)) /= in lt2_m.
  + by rewrite -lez_add1r in gt0_m.
  rewrite -Zppq.eq_inzmod -eq_22epeq_ppq /p modz_dvd_pow; 1: by split.
  rewrite modz_pow2_div; [by apply /addz_ge0 /expr_ge0; 1: apply Zq.ge0_asint | by split |]. 
  rewrite opprD (addzC (-eq)) addzA /= -mulr2z intmulz (mulzC ep) modz_mod divzDr 1: dvdz_exp2l. 
  + by split => [| ?]; last rewrite -(lez_add2r 1) -(lez_add2l ep) -!addzA /= !addzA addzAC 
                                     addzC !addzA /= -mulr2z intmulz mulzC geeq1_2ep.
  have -> //: 2 ^ (ep - 1) %/ 2 ^ (eq - ep) = 2 ^ (2 * ep - eq - 1).
  rewrite eq_sym eqz_div 2:dvdz_exp2l 3: -exprD_nneg; last congr; rewrite //#. 
  + by rewrite neq_ltz; right; apply expr_gt0.
  + by split => [| ?]; last rewrite -(lez_add2r 1) -(lez_add2l ep) -!addzA /= !addzA 
                                     addzAC addzC !addzA /= -mulr2z intmulz mulzC geeq1_2ep.
  + by rewrite -(lez_add2r 1) -addzA /= -(lez_add2r eq) -addzA addzC /= geeq1_2ep.
  + by apply /(lez_trans 1) /(lez_add2l ep); 2: rewrite addzCA /= geep1_eq.
qed. 

lemma eq_scaleRqRp_modRppq_scale_Rppq (x : Rq) (m : R2) :
      mod_ppq_Rp ((scale_Rq_Rp x) + (shl_enc m (2 * ep - eq - 1)))
      =
      scale_Rp_Rppq ((mod_p_Rq x) + (shl_enc m (ep - 1))).
proof.
  (* Re-occuring Goals *)
  have ispoly_shlm_pp2q: 
       ispoly (fun (i0 : int) => (Zp.inzmod (shl (Z2.asint m.[i0]) (2 * ep - eq - 1)))).
  + split; [| exists (deg (crepr m) - 1)] => [c lt0_c | c gtdeg1_c] /=; have ->: asint m.[c] = 0;
           2, 4: rewrite /shl mul0r //; 1, 2: rewrite -Z2.zeroE asint_eq. 
    - by apply R2.BasePoly.lt0_coeff. 
    - by apply R2.BasePoly.gedeg_coeff; rewrite -lez_add1r addzC /= in gtdeg1_c. 

  have ispoly_xmodp : ispoly (fun (i0 : int) => (Zp.inzmod (Zq.asint x.[i0]))).
  + split; [| exists (deg (crepr x) - 1)] => [c lt0_c | c gtdeg1_c] /=; have ->: asint x.[c] = 0;
           rewrite // -Zq.zeroE asint_eq.
    - by apply Rq.BasePoly.lt0_coeff.
    - by apply Rq.BasePoly.gedeg_coeff; rewrite -lez_add1r addzC /= in gtdeg1_c.

  have ispoly_shlm_p2 : ispoly (fun (i0 : int) => (Zp.inzmod (shl (Z2.asint m.[i0]) (ep - 1)))).
  + split; [| exists (deg (crepr m) - 1)] => [c lt0_c | c gtdeg1_c] /=; have ->: asint m.[c] = 0;
           2, 4: rewrite /shl mul0r //; 1, 2: rewrite -Z2.zeroE asint_eq. 
    - by apply R2.BasePoly.lt0_coeff. 
    - by apply R2.BasePoly.gedeg_coeff; rewrite -lez_add1r addzC /= in gtdeg1_c.

  (* Main Proof *)
  rewrite /mod_ppq_Rp /scale_Rp_Rppq; do 2! congr; rewrite fun_ext /(==) => i.
  rewrite /mod_p_Rq /scale_Rq_Rp /shl_enc !addE !piK; 1, 2: apply Rp.reduceD;
          2, 3, 4: rewrite reducedP deg_leP 1:ge0_n => j gen_j; 2, 3, 4: rewrite coeffE /=.
  + by apply reduced_topolyd_scale_Zq_Zp.
  + by apply ispoly_shlm_pp2q.
  + have ->: asint m.[j] = 0; 2: rewrite /shl mul0r //.
    - by rewrite -Z2.zeroE asint_eq gedeg_coeff 1:(lez_trans n) 1:&(R2.deg_crepr).
  + by apply ispoly_xmodp.
  + by have ->: asint x.[j] = 0; rewrite // -Zq.zeroE asint_eq gedeg_coeff // 
                                         (lez_trans n) ?deg_crepr.
  + by apply ispoly_shlm_p2.
  + have ->: asint m.[j] = 0; 2: rewrite /shl mul0r //.
    - by rewrite -Z2.zeroE asint_eq gedeg_coeff 1:(lez_trans n) 1:&(R2.deg_crepr).
  rewrite !polyDE !coeffE.
  + by apply ispoly_fun_scale_Zq_Zp.
  + by apply ispoly_shlm_pp2q.
  + by apply ispoly_xmodp.
  + by apply ispoly_shlm_p2.
  by apply eq_scaleZqZp_modZppq_scaleZpZppq.
qed.  

(* ----------------------------------- *)
(*  Saber's PKE Scheme                 *)
(* ----------------------------------- *)

(* --- General --- *)
clone import PKE as Saber_PKE with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

(* --- Actual --- *)
module Saber_PKE_Scheme : Scheme = {
   proc kg() : pkey * skey = {
      var sd: seed;
      var _A: Rq_mat;
      var s: Rq_vec;
      var b: Rp_vec;
      
      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      b <- scale_vec_Rq_Rp (_A *^ s + h);
      
      return (pk_encode (sd, b), sk_encode s);
   }

   proc enc(pk: pkey, m: plaintext) : ciphertext = {
      var pk_dec: seed * Rp_vec;
      var m_dec: R2;

      var sd: seed;
      var _A: Rq_mat;
      var s': Rq_vec;
      var b, b': Rp_vec;
      var v': Rp;
      var cm: R2t;
      
      m_dec <- m_decode m;
      pk_dec <- pk_decode pk;
      sd <- pk_dec.`1;
      b <- pk_dec.`2;
      _A <- gen sd;
      s' <$ dsmallRq_vec;
      b' <- scale_vec_Rq_Rp ((trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Rq_vec s')) + (mod_p_Rq h1);
      cm <- scale_Rp_R2t (v' + (shl_enc m_dec (ep - 1)));
      
      return c_encode (cm, b');
   }

   proc dec(sk: skey, c: ciphertext) : plaintext option = {
      var c_dec: R2t * Rp_vec;
      var cm: R2t;
      var b': Rp_vec;
      var v: Rp;
      var s: Rq_vec;
      var m': R2;

      c_dec <- c_decode c;
      s <- sk_decode sk;
      cm <- c_dec.`1;
      b' <- c_dec.`2;
      v <- (dotp b' (mod_p_Rq_vec s)) + (mod_p_Rq h1);
      m' <- scale_Rp_R2 (v + (- (shl_dec cm)) + (mod_p_Rq h2));
      
      return Some (m_encode m');
   }
}.
