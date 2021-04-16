(* ------------------------------------------------------------------------------------- *)
(*  Require/Import Theories                                                              *)
(* ------------------------------------------------------------------------------------- *)

(* --- Built-in --- *)
require import AllCore List Distr Ring ZModP IntDiv Bigalg StdOrder.
require (*--*) Matrix PKE.
(*---*) import IntOrder.

(* --- Local --- *)
require (*--*) PolyReduce.

(* ------------------------------------------------------------------------------------- *)
(*  General Preliminaries                                                                *)
(* ------------------------------------------------------------------------------------- *)

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
lemma ge0_n: 0 <= n by smt(ge1_n).
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
  apply (mulfI q); [by rewrite neq_ltz; right; apply expr_gt0 | 
                    rewrite mulzC -(mulzC (p * p %/ q) _)].  
  have ->: p * p %/ q * q = p * p.
   by rewrite -(dvdz_eq q (p * p)) q_div_pp.
  rewrite /p /q -exprD_nneg; first by rewrite subz_ge0 (lez_trans (eq + 1) eq (2 * ep)); 
          [rewrite (lez_addl _ 1) | apply geeq1_2ep].
   by apply /(lez_trans 3 0 eq) /ge3_eq.
  rewrite -exprD_nneg; first 2 by rewrite (lez_trans 2 0 ep); [| apply ge2_ep || apply ge2_ep ].
   by congr; rewrite -addzA /= mulzC -mul1r2z /ofint_id intmulz.
qed.

(* --- Types, Operators and Distributions --- *)
abstract theory PolyZ.
clone import ZModRing as Zmod.

clone import PolyReduce.PolyReduceZp as Rmod with
  type Zp <- Zmod.zmod,
    op p  <- Zmod.p,
    op n  <- n,

    op Zp.unit   <- Zmod.unit,
    op Zp.zero   <- Zmod.zero,
    op Zp.one    <- Zmod.one,
    op Zp.( + )  <- Zmod.( + ),
    op Zp.([-])  <- Zmod.([-]),
    op Zp.( * )  <- Zmod.( * ),
    op Zp.inv    <- Zmod.inv,
    op Zp.inzmod <- Zmod.inzmod,
    op Zp.asint  <- Zmod.asint,
  
    op Zp.DZmodP.dunifin <- Zmod.DZmodP.dunifin,
  
    op Zp.ZModpRing.ofint  <- Zmod.ZModpRing.ofint,
    op Zp.ZModpRing.intmul <- Zmod.ZModpRing.intmul,
    op Zp.ZModpRing.exp    <- Zmod.ZModpRing.exp,
    op Zp.ZModpRing.lreg   <- Zmod.ZModpRing.lreg

  proof gt0_n by smt(ge1_n)
  proof ge2_p by apply/Zmod.ge2_p

  remove abbrev Zp.zmodcgr
  remove abbrev Zp.(-)
  remove abbrev Zp.(/)

  remove abbrev Zp.ZModpRing.(-)
  remove abbrev Zp.ZModpRing.(/)

  rename [theory] "Zp" as "Zrmod".

clear [Rmod.Zrmod.* Rmod.Zrmod.DZmodP.* Rmod.Zrmod.DZmodP.Support.*].
clear [Rmod.Zrmod.ZModule.* Rmod.Zrmod.ComRing.* Rmod.Zrmod.ZModpRing.*].
clear [Rmod.Zrmod.ZModpRing.AddMonoid.* Rmod.Zrmod.ZModpRing.MulMonoid.*].
end PolyZ.

(* -- Rq = Z/qZ[X] / (X^n + 1) -- *)
type Zq, Rq.

clone include PolyZ with
  type Zmod.zmod     <- Zq,
  type Rmod.polyXnD1 <- Rq,
    op Zmod.p        <- q

  proof Zmod.ge2_p by smt(ge8_q)

  rename [theory] "Zmod" as "Zq"
  rename [theory] "Rmod" as "Rq"
  rename [theory] "BigXnD1" as "BigRq".

clone Matrix as Mat_Rq with 
  type R         <- Rq,
    op size      <- l,

  pred ZR.unit   <- Rq.unit,
    op ZR.zeror  <- Rq.zeroXnD1,
    op ZR.oner   <- Rq.oneXnD1,
    op ZR.( + )  <- Rq.( + ),
    op ZR.([-])  <- Rq.([-]),
    op ZR.( * )  <- Rq.( * ),
    op ZR.invr   <- Rq.invr,
    op ZR.intmul <- Rq.ComRing.intmul,
    op ZR.ofint  <- Rq.ComRing.ofint,
    op ZR.exp    <- Rq.ComRing.exp,
    op ZR.lreg   <- Rq.ComRing.lreg

  proof ge0_size by apply (lez_trans 1 _ _ _ ge1_l).
    
type Rq_vec = Mat_Rq.vector.
type Rq_mat = Mat_Rq.Matrix.matrix.

op dRq : Rq distr = Rq.dpolyXnD1.
op [lossless] dsmallRq : Rq distr.

op dRq_vec : Rq_vec distr = Mat_Rq.Matrix.dvector dRq.
op dRq_mat : Rq_mat distr = Mat_Rq.Matrix.dmatrix dRq.
op dsmallRq_vec : Rq_vec distr = Mat_Rq.Matrix.dvector dsmallRq.

(* -- Rp = Z/pZ[X] / (X^n + 1) -- *)
type Zp, Rp.

clone include PolyZ with
   type Zmod.zmod     <- Zp,
   type Rmod.polyXnD1 <- Rp,
     op Zmod.p        <- p

  proof Zmod.ge2_p by smt(ge4_p)

  rename [theory] "Zmod" as "Zp"
  rename [theory] "Rmod" as "Rp"
  rename [theory] "BigXnD1" as "BigRp".

clone Matrix as Mat_Rp with 
  type R         <- Rp,
    op size      <- l,

  pred ZR.unit   <- Rp.unit,
    op ZR.zeror  <- Rp.zeroXnD1,
    op ZR.oner   <- Rp.oneXnD1,
    op ZR.( + )  <- Rp.( + ),
    op ZR.([-])  <- Rp.([-]),
    op ZR.( * )  <- Rp.( * ),
    op ZR.invr   <- Rp.invr,
    op ZR.intmul <- Rp.ComRing.intmul,
    op ZR.ofint  <- Rp.ComRing.ofint,
    op ZR.exp    <- Rp.ComRing.exp,
    op ZR.lreg   <- Rp.ComRing.lreg

  proof ge0_size by apply (lez_trans 1 _ _ _ ge1_l).

type Rp_vec = Mat_Rp.vector.

op dRp : Rp distr = Rp.dpolyXnD1. 
op dRp_vec : Rp_vec distr = Mat_Rp.Matrix.dvector dRp.

(* -- Rppq = Z/ppqZ [X] / (X^n + 1) -- *)
type Zppq, Rppq.

clone include PolyZ with
  type Zmod.zmod     <- Zppq,
  type Rmod.polyXnD1 <- Rppq,
    op Zmod.p        <- (p * p) %/ q

  proof Zmod.ge2_p by apply/ge2_ppq

  rename [theory] "Zmod" as "Zppq"
  rename [theory] "Rmod" as "Rppq"
  rename [theory] "BigXnD1" as "BigRppq".

(* -- R2t = Z/2tZ [X] / (X^n + 1)  -- *)
type Z2t, R2t.

clone include PolyZ with
  type Zmod.zmod     <- Z2t,
  type Rmod.polyXnD1 <- R2t,
    op Zmod.p        <- 2 * t

  proof Zmod.ge2_p by apply/ge2_2t

  rename [theory] "Zmod" as "Z2t"
  rename [theory] "Rmod" as "R2t"
  rename [theory] "BigXnD1" as "BigR2t".

(* -- R2 = Z/2Z [X] / (X^n + 1) -- *)
type Z2, R2.

clone include PolyZ with
  type Zmod.zmod     <- Z2,
  type Rmod.polyXnD1 <- R2,
    op Zmod.p        <- 2

  proof Zmod.ge2_p by done

  rename [theory] "Zmod" as "Z2"
  rename [theory] "Rmod" as "R2"
  rename [theory] "BigXnD1" as "BigR2".

(* - Properties - *)
(* Vector Distribution Has Same Properties as the Distribution of the Vector's Elements *)
lemma dRq_vec_ll: is_lossless dRq_vec.
proof. by apply Mat_Rq.Matrix.dvector_ll; rewrite /dRq; apply /Rq.dpolyXnD1_ll. qed.

lemma dRq_vec_fu: is_full dRq_vec.
proof. by apply /Mat_Rq.Matrix.dvector_fu; rewrite /dRq; apply /Rq.dpolyXnD1_fu. qed.

lemma dRq_vec_uni: is_uniform dRq_vec.
proof. by apply /Mat_Rq.Matrix.dvector_uni; rewrite /dRq; apply /Rq.dpolyXnD1_uni. qed.

lemma dRp_vec_ll: is_lossless dRp_vec.
proof. by apply /Mat_Rp.Matrix.dvector_ll; rewrite /dRp; apply /Rp.dpolyXnD1_ll. qed.

lemma dRp_vec_fu: is_full dRp_vec.
proof. by apply /Mat_Rp.Matrix.dvector_fu; rewrite /dRp; apply /Rp.dpolyXnD1_fu. qed.

lemma dRp_vec_uni: is_uniform dRp_vec.
proof. by apply /Mat_Rp.Matrix.dvector_uni; rewrite /dRp; apply /Rp.dpolyXnD1_uni. qed.

lemma dsmallRq_vec_ll: is_lossless dsmallRq_vec.
proof. by apply /Mat_Rq.Matrix.dvector_ll /dsmallRq_ll. qed.

(* Matrix Distribution Has Same Properties as the Distribution of the Matrix's Elements *)
lemma dRq_mat_ll: is_lossless dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_ll; rewrite /dRq; apply /Rq.dpolyXnD1_ll. qed.

lemma dRq_mat_fu: is_full dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_fu; rewrite /dRq; apply /Rq.dpolyXnD1_fu. qed.

lemma dRq_mat_uni: is_uniform dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_uni; rewrite /dRq; apply /Rq.dpolyXnD1_uni. qed.

(* - Imports - *)
import Mat_Rq Mat_Rp.
import Zq Rq Rq.ComRing Rq.BasePoly. 
import Zp Rp Rp.ComRing Rp.BasePoly.
import Zppq Rppq Rppq.ComRing Rppq.BasePoly.
import Z2t R2t R2t.ComRing R2t.BasePoly.
import Z2 R2 R2.ComRing R2.BasePoly.
import Rp.BasePoly.BigCf.

(* - From Rq to Rp - *)
op Zq2Zp (z : Zq) : Zp =
  Zp.inzmod (asint z).

lemma Zq2Zp0 : Zq2Zp Zq.zero = Zp.zero.
proof. by rewrite -eq_inzmod zeroE mod0z. qed.

import DInterval DList.

lemma duni_Zp_Zq : dmap DZqP.dunifin Zq2Zp = DZpP.dunifin.
proof.
rewrite !(DZqP.dzmodE, DZpP.dzmodE) dmap_comp.
have ->: Zq2Zp \o Zq.inzmod = Zp.inzmod.
- apply/fun_ext=> i; apply/Zp.eq_inzmod.
  by rewrite inzmodK modz_dvd // p_div_q.
apply/eq_distr; elim/Zp.inzmodW => i rgi.
rewrite eq_sym (dmap1E_can _ _ Zp.asint) 1:&(Zp.asintK).
- by move=> j /supp_dinter rgj; rewrite inzmodK pmod_small //#.
rewrite inzmodK pmod_small // eq_sym dmap1E /(\o) /pred1.
pose P := fun x => Zp.inzmod x = Zp.inzmod i.
have ->: P = pred1 i \o (fun x => x %% p).
- apply/fun_ext=> j @/(\o) @/pred1 @/P.
  by rewrite -eq_inzmod (pmod_small i).
rewrite -dmap1E; apply/eq_distr/duni_range_dvd/p_div_q.
- by apply/(ltr_le_trans 8)/ge8_q.
- by apply/(ltr_le_trans 4)/ge4_p.
qed.

op Rq2Rp (p : Rq) : Rp =
  BigRp.XnD1CA.bigi predT (fun (i : int) => Zq2Zp p.[i] ** exp Rp.iX i) 0 n.

op Rqv2Rpv (p : Rq_vec) : Rp_vec = offunv (fun (i : int) => Rq2Rp p.[i]).

lemma Rq2RpE (p : Rq) (i : int) : (Rq2Rp p).[i] = Zq2Zp p.[i].
proof.
case: (i < 0) => [lt0_i|]; first by rewrite !lt0_rcoeff // Zq2Zp0.
move/lerNgt=> ge0_i; case: (i < n); last first.
- by move/lerNgt=> ge_ni; rewrite !gered_rcoeff // Zq2Zp0.
move=> lt_in; rewrite rcoeff_sum /= (BCA.bigD1 _ _ i) /=;
  1,2: by rewrite (mem_range, range_uniq).
rewrite rcoeffZ rcoeff_polyXn //= Zp.ZModpRing.mulr1.
rewrite BCA.big_seq_cond BCA.big1 /=; last first.
- by rewrite Zp.ZModpRing.addr0.
move=> j [/mem_range rgj @/predC1 ne_ji].
rewrite rcoeffZ rcoeff_polyXn // (eq_sym i j) ne_ji /=.
- by rewrite Zp.ZModpRing.mulr0.
qed.

lemma duni_Rp_Rq : dmap Rq.dpolyXnD1 Rq2Rp = Rp.dpolyXnD1.
proof.
rewrite /Rq.dpolyXnD1 /Rp.dpolyXnD1 -duni_Zp_Zq.
rewrite !(dmap_comp, dlist_dmap) &(eq_dmap_in).
move=> xs /(supp_dlist_size _ _ _ ge0_n) => szxs @/(\o).
apply/Rp.polyXnD1_eqP=> i rgi; rewrite Rq2RpE.
rewrite !piK; ~-1: by rewrite (reduced_polyL) ?size_map szxs.
by rewrite !polyLE (nth_map Zq.zero) ?szxs.
qed.

lemma Rqv2RpvE (p : Rq_vec) (i : int) : (Rqv2Rpv p).[i] = Rq2Rp p.[i].
proof.
  rewrite /Rqv2Rpv /Mat_Rp.Vector."_.[_]" offunvK /vclamp.
  case (0 <= i && i < l) => //; move/(Mat_Rq.Vector.getv_out p i) => ->.
  rewrite /Rq2Rp eq_sym BigRp.XnD1CA.big_seq BigRp.XnD1CA.big1 => //= j; 
          case/mem_range => ge0_j ltn_j.
  have ->: Zq2Zp Rq.zeroXnD1.[j] = Zp.zero; 2: rewrite /( ** ) scale0p //.
  by rewrite /zeror /"_.[_]" piK 1:reducedP 1:degC // 
     -/Rq.BasePoly."_.[_]" poly0E /Zq2Zp Zq.zeroE.
qed.

lemma duni_Rp_Rq_vec: dmap dRq_vec Rqv2Rpv = dRp_vec.
proof.
  rewrite /dRp_vec /dRp /dRq_vec /dRq /Rq.dpolyXnD1 /Rp.dpolyXnD1 /dvector -duni_Zp_Zq.
  rewrite !(dmap_comp, dlist_dmap, -djoin_dmap_nseq) /(\o).
  apply eq_dmap_in => x /supp_djoin [sxl /allP] /= xele.
  rewrite size_nseq maxrE lezNgt -(lez_add1r _ l) ge1_l /= in sxl.
  apply eq_vectorP => i [ge0_i ltl_i]; rewrite Rqv2RpvE /"_.[_]" !offunvK /vclamp ge0_i ltl_i /=.
  rewrite !(nth_map witness) /=; 1, 2: smt().
  have sxn : size (nth witness x i) = n.
  + move: (xele ((dlist DZqP.dunifin n), (nth witness x i)) _) => /=.
    - by rewrite sxl &(mem_zip_nseqL) mem_nth //#.
    - by apply supp_dlist_size. 
  apply Rp.polyXnD1_eqP => j [gt0_j ltn_j]; rewrite Rq2RpE. 
  rewrite !piK; first 2 by rewrite reduced_polyL ?size_map lez_eqVlt; left. 
  by rewrite !polyLE (nth_map Zq.zero) //#.
qed.

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
  apply /(scale_comp (Zp.asint x)) /ge2epeq_ep; 
        [apply Zp.ge0_asint | by apply /(lez_trans 1) /ge1_et1 |].
  rewrite mulzC -intmulz mulr2z -(lez_add2r (-(et + 1))) /= -(lez_add2l (eq)) addzAC addzCA /= 
          -(lez_add2r (-ep)) addzAC (IntID.subrK ep (-ep)) opprD addzA.
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
      Zppq.inzmod (Zp.asint ((scale_Zq_Zp x) + (Zp.inzmod (shl (Z2.asint m) (2 * ep - eq - 1)))))
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
  rewrite /mod_p_Rq /scale_Rq_Rp /shl_enc !addE !piK; 1, 2: apply Rp.reducedD;
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

pragma Goals:printall.

lemma Zq2Zp_DDl (a b : Zq) : Zq2Zp (a + b) = Zq2Zp a + Zq2Zp b.
proof. by rewrite /Zq2Zp /( + ) !inzmodK /inzmod modzDm modz_dvd 1:p_div_q. qed.

lemma Zq2Zp_BDl (a b : Zq) : Zq2Zp (a - b) = Zq2Zp a - Zq2Zp b.
proof. 
by rewrite /Zq2Zp /( + ) !inzmodK modzNm /inzmod modzDm modzDmr modz_dvd 1:p_div_q. 
qed.

lemma Zq2Zp_MDl (a b : Zq) : Zq2Zp (a * b) = Zq2Zp a * Zq2Zp b.
proof. by rewrite /Zq2Zp /( * ) !inzmodK /inzmod modzMm modz_dvd 1:p_div_q. qed.

lemma Rq2Rp_DDl (a: Rq) (b : Rq) :
      Rq2Rp (a + b) = (Rq2Rp a) + (Rq2Rp b).
proof.
by rewrite polyXnD1_eqP => i [ge0_i ltn_i]; rewrite eq_sym rcoeffD !Rq2RpE rcoeffD Zq2Zp_DDl.
qed.

lemma Rq2Rp_MDl (a: Rq) (b : Rq) :
      Rq2Rp (a * b) = (Rq2Rp a) * (Rq2Rp b).
proof.
rewrite polyXnD1_eqP => i [ge0_i ltn_i]; rewrite Rq2RpE !rcoeffM 1,2://# eq_sym. 
have ->: 
 (fun (i0 : int) =>
  ((Rq2Rp a).[i0] * (Rq2Rp b).[i - i0] - (Rq2Rp a).[i0] * (Rq2Rp b).[n + i - i0]))
 =    
 (fun (i0 : int) =>
  (Zq2Zp (a.[i0] * b.[i - i0] - a.[i0] * b.[n + i - i0]))).
+ by rewrite fun_ext /( == ) => j; rewrite !Rq2RpE Zq2Zp_BDl !Zq2Zp_MDl.
admit.
qed.

lemma Rq2Rp_DotDl (a: Rq_vec) (b : Rq_vec) :
      Rq2Rp (dotp a b) = dotp (Rqv2Rpv a) (Rqv2Rpv b).
proof.
rewrite /Rqv2Rpv /dotp eq_sym.
rewrite /Mat_Rp.Vector."_.[_]" !offunvK /= /vclamp.
have ->:
(Big.BAdd.bigi predT
   (fun (i : int) =>
      (if 0 <= i && i < l then Rq2Rp (a.[i]) else Rp.zeroXnD1) *
      if 0 <= i && i < l then Rq2Rp (b.[i]) else Rp.zeroXnD1) 0 l)
=
(Big.BAdd.bigi predT
   (fun (i : int) =>
      Rq2Rp (a.[i] * b.[i])) 0 l).
rewrite !Big.BAdd.big_seq &(Big.BAdd.eq_bigr) => i /= /mem_range [ge0_i ltl_i]; smt(Rq2Rp_MDl).
rewrite polyXnD1_eqP => i rngi. 
rewrite !rcoeff_sum /= eq_sym.
rewrite (BCA.bigD1 _ _ i) /=;  1, 2: by rewrite (mem_range, range_uniq).
rewrite rcoeffZ rcoeff_polyXn //= Zp.ZModpRing.mulr1.
rewrite BCA.big_seq_cond BCA.big1 /= => [j [/mem_range rngj @/predC1 ne_ji] |].
+ by rewrite rcoeffZ rcoeff_polyXn // (eq_sym i) ne_ji /= Zp.ZModpRing.mulr0.
rewrite Zp.ZModpRing.addr0 rcoeff_sum /=. 
have ->: 
(BCA.bigi predT (fun (i0 : int) => (Rq2Rp (a.[i0] * b.[i0])).[i]) 0 l)
=
(BCA.bigi predT (fun (i0 : int) => Zq2Zp (a.[i0] * b.[i0]).[i]) 0 l).
+ by apply BCA.eq_bigr => j _ /=; rewrite Rq2RpE.   
admit.
qed.

op Zp2Zq (z : Zp) : Zq = Zq.inzmod (Zp.asint z).

op Rp2Rq (p : Rp) : Rq =
  BigRq.XnD1CA.bigi predT (fun (i : int) => Zp2Zq p.[i] ** exp Rq.iX i) 0 n.

op Rpv2Rqv (pv : Rp_vec) : Rq_vec = offunv (fun (i : int) => Rp2Rq pv.[i]).

lemma Zp2Zq0 : Zp2Zq Zp.zero = Zq.zero.
proof. by rewrite -eq_inzmod zeroE mod0z. qed.

lemma Rp2RqE (p : Rp) (i : int) : (Rp2Rq p).[i] = Zp2Zq p.[i].
proof.
case: (i < 0) => [lt0_i|]; first by rewrite !lt0_rcoeff // Zp2Zq0.
move/lerNgt=> ge0_i; case: (i < n); last first.
+ by move/lerNgt=> ge_ni; rewrite !gered_rcoeff // Zp2Zq0.
move=> lt_in; rewrite rcoeff_sum /= (Rq.BasePoly.BigCf.BCA.bigD1 _ _ i) /=;
              1,2: by rewrite (mem_range, range_uniq).
rewrite rcoeffZ rcoeff_polyXn //= Zq.ZModpRing.mulr1.
rewrite Rq.BasePoly.BigCf.BCA.big_seq_cond Rq.BasePoly.BigCf.BCA.big1 /=; last first.
+ by rewrite Zq.ZModpRing.addr0.
move=> j [/mem_range rgj @/predC1 ne_ji].
rewrite rcoeffZ rcoeff_polyXn // (eq_sym i j) ne_ji /=.
+ by rewrite Zq.ZModpRing.mulr0.
qed.

lemma Rpv2RqvE (p : Rp_vec) (i : int) : (Rpv2Rqv p).[i] = Rp2Rq p.[i].
proof.
rewrite /Rpv2Rqv /Mat_Rq.Vector."_.[_]" offunvK /vclamp.
case (0 <= i && i < l) => //; move/(Mat_Rp.Vector.getv_out p i) => ->.
rewrite /Rp2Rq eq_sym BigRq.XnD1CA.big_seq BigRq.XnD1CA.big1 => //= j /mem_range [ge0_j ltn_j].
by rewrite rcoeff0 Zp2Zq0 scale0p.
qed.

lemma Zp2Zq_Zq2Zp_inv (z : Zp) : Zq2Zp (Zp2Zq z) = z.
proof.
rewrite /Zq2Zp /Zp2Zq inzmodK modz_small 1: ge0_asint 2:asintK //=.
rewrite ger0_norm 2:(ltr_le_trans p _ _ (Zp.gtp_asint z)) /p /q; first smt(ge8_q).
by apply (ler_weexpn2l 2 _ ep eq _); 2: smt(ge2_ep geep1_eq).
qed.

lemma Rp2Rq_Rq2Rp_inv (p : Rp) : Rq2Rp (Rp2Rq p) = p.
proof.
rewrite /Rq2Rp polyXnD1_eqP => i [ge0_i ltn_i].
rewrite rcoeff_sum /= (BCA.bigD1 _ _  i) /=; 1, 2: by rewrite (mem_range, range_uniq).
rewrite rcoeffZ rcoeff_polyXn //= Rp2RqE Zp2Zq_Zq2Zp_inv Zp.ZModpRing.mulr1.
rewrite BCA.big_seq_cond BCA.big1 /=; last by rewrite Zp.ZModpRing.addr0.
move => j [/mem_range rgj @/predC1 ne_ji].
by rewrite rcoeffZ rcoeff_polyXn // (eq_sym i j) ne_ji Zp.ZModpRing.mulr0 //.
qed.

lemma Rpv2Rqv_Rqv2Rpv_inv (pv : Rp_vec) : Rqv2Rpv (Rpv2Rqv pv) = pv.
proof.
rewrite /Rqv2Rpv eq_vectorP => i rngi.
by rewrite {1}/Mat_Rp.Vector."_.[_]" offunvK /vclamp rngi /= Rpv2RqvE Rp2Rq_Rq2Rp_inv.
qed.

lemma Rq2Rp_DG23 (b : Rp_vec) (s : Rq_vec) : 
       Rq2Rp (dotp (Rpv2Rqv b) s + h1) = dotp b (Rqv2Rpv s) + Rq2Rp h1.
proof. by rewrite Rq2Rp_DDl Rq2Rp_DotDl Rpv2Rqv_Rqv2Rpv_inv. qed.

op scaleZq2Zp (z : Zq) : Zp = Zp.inzmod (scale (Zq.asint z) eq ep).
op scaleZp2Zp (z : Zp) : Zp = Zp.inzmod (scale (Zp.asint z) ep ep).
op scaleZp2Zppq (z : Zp) : Zppq = Zppq.inzmod (scale (Zp.asint z) ep (2 * ep - eq)).
op scaleZp2Z2t (z : Zp) : Z2t = Z2t.inzmod (scale (Zp.asint z) ep (et + 1)).
op scaleZp2Z2 (z : Zp) : Z2 = Z2.inzmod (scale (Zp.asint z) ep 1).
op scaleZppq2Z2t (z : Zppq) : Z2t = Z2t.inzmod (scale (Zppq.asint z) (2 * ep - eq) (et + 1)).

op scaleRq2Rp (p : Rq) : Rp = 
  BigRp.XnD1CA.bigi predT (fun (i : int) => scaleZq2Zp p.[i] ** exp Rp.iX i) 0 n.
op scaleRp2Rp (p : Rp) : Rp = 
  BigRp.XnD1CA.bigi predT (fun (i : int) => scaleZp2Zp p.[i] ** exp Rp.iX i) 0 n.
op scaleRp2Rppq (p : Rp) : Rppq = 
  BigRppq.XnD1CA.bigi predT (fun (i : int) => scaleZp2Zppq p.[i] ** exp Rppq.iX i) 0 n.
op scaleRp2R2t (p : Rp) : R2t = 
  BigR2t.XnD1CA.bigi predT (fun (i : int) => scaleZp2Z2t p.[i] ** exp R2t.iX i) 0 n.
op scaleRp2R2 (p : Rp) : R2 = 
  BigR2.XnD1CA.bigi predT (fun (i : int) => scaleZp2Z2 p.[i] ** exp R2.iX i) 0 n.
op scaleRppq2R2t (p : Rppq) : R2t = 
  BigR2t.XnD1CA.bigi predT (fun (i : int) => scaleZppq2Z2t p.[i] ** exp R2t.iX i) 0 n.

op scaleRqv2Rpv (pv : Rq_vec) : Rp_vec = offunv (fun (i : int) => scaleRq2Rp pv.[i]).

lemma scaleZp2Zp_id (z : Zp) : scaleZp2Zp z = z.
proof. by rewrite /scaleZp2Zp scale_id 2: Zp.asintK. qed.

lemma scaleRp2Rp_id (p : Rp) : scaleRp2Rp p = p.
proof. 
rewrite /scaleRp2Rp polyXnD1_eqP => i rngi; rewrite rcoeff_sum /=.
rewrite (BCA.bigD1 _ _ i) /=; 1, 2: by rewrite (mem_range, range_uniq).
rewrite BCA.big_seq_cond BCA.big1 => /= [j [/mem_range rngj @/predC1 ne_ji] |];
        rewrite scaleZp2Zp_id rcoeffZ rcoeff_polyXn //= ?((eq_sym i j), ne_ji) /=.
+ by apply Zp.ZModpRing.mulr0.
+ by rewrite Zp.ZModpRing.mulr1 Zp.ZModpRing.addr0.
qed.

lemma scaleZp2Zppq2Z2t_comp (x : Zp) :
      scaleZp2Z2t x = scaleZppq2Z2t (scaleZp2Zppq x).
proof.
rewrite /scaleZp2Z2t /scaleZppq2Z2t /scaleZp2Zppq Zppq.inzmodK -Z2t.eq_inzmod; do 2! congr.
rewrite (modz_small _ (p * p %/ q)) /scale /shr; first split => [| ?].
+ by apply /divz_ge0 /Zp.ge0_asint /expr_gt0.
+ rewrite ger0_norm; first by apply /(lez_trans 2) /ge2_ppq. 
  apply ltz_divLR; first by apply expr_gt0. 
  have ge2epeq_ep: 2 * ep - eq <= ep by smt(geep1_eq).
  rewrite -eq_22epeq_ppq -exprD_nneg; smt(geeq1_2ep Zp.gtp_asint).
by apply /(scale_comp (Zp.asint x) _ _ _ (Zp.ge0_asint x)); smt(ge1_et1 geep1_eq sec_assumption).
qed.

lemma scaleRp2Rppq2R2t_comp (x : Rp) :
      scaleRp2R2t x = scaleRppq2R2t (scaleRp2Rppq x).
proof.
rewrite /scaleRp2R2t /scaleRppq2R2t /scaleRp2Rppq polyXnD1_eqP => i rngi. 
rewrite !(rcoeff_sum, (R2t.BasePoly.BigCf.BCA.bigD1 _ _ i)) /=; first 4 smt(mem_range range_uniq).
congr; last first.
+ rewrite R2t.BasePoly.BigCf.BCA.big_seq_cond eq_sym R2t.BasePoly.BigCf.BCA.big_seq_cond.
  by rewrite !R2t.BasePoly.BigCf.BCA.big1 //= => 
             [j [/mem_range rngj @/predC1 ne_ji] | j [/mem_range rngj @/predC1 ne_ji]];
             rewrite rcoeffZ rcoeff_polyXn 2:(eq_sym i) 2:ne_ji //= Z2t.ZModpRing.mulr0.
+ rewrite 2!rcoeffZ rcoeff_polyXn //= 2!Z2t.ZModpRing.mulr1 scaleZp2Zppq2Z2t_comp; congr.
  rewrite rcoeff_sum (Rppq.BasePoly.BigCf.BCA.bigD1 _ _ i) /=; first 2 smt(mem_range range_uniq).
  rewrite Rppq.BasePoly.BigCf.BCA.big_seq_cond Rppq.BasePoly.BigCf.BCA.big1 => 
          [j [/mem_range rngj @/predC1 ne_ji] /= |]; rewrite rcoeffZ rcoeff_polyXn //=.
  - by rewrite (eq_sym i) ne_ji /= Zppq.ZModpRing.mulr0.
  by rewrite Zppq.ZModpRing.addr0 Zppq.ZModpRing.mulr1.
qed.

op Zp2Zppq (z : Zp) : Zppq = Zppq.inzmod (Zp.asint z).

op Rp2Rppq (p : Rp) : Rppq =
  BigRppq.XnD1CA.bigi predT (fun (i : int) => Zp2Zppq p.[i] ** exp Rppq.iX i) 0 n.

lemma Zp2Zppq0 : Zp2Zppq Zp.zero = Zppq.zero.
proof. by rewrite -eq_inzmod zeroE. qed.

lemma Rp2RppqE (p : Rp) (i : int) : (Rp2Rppq p).[i] = Zp2Zppq p.[i].
proof.
case: (i < 0) => [lt0_i|]; first by rewrite !lt0_rcoeff // Zp2Zppq0.
move/lerNgt=> ge0_i; case: (i < n); last first.
- by move/lerNgt=> ge_ni; rewrite !gered_rcoeff // Zp2Zppq0.
move=> lt_in; rewrite rcoeff_sum /= (Rppq.BasePoly.BigCf.BCA.bigD1 _ _ i) /=;
  1,2: by rewrite (mem_range, range_uniq).
rewrite rcoeffZ rcoeff_polyXn //= Zppq.ZModpRing.mulr1.
rewrite Rppq.BasePoly.BigCf.BCA.big_seq_cond Rppq.BasePoly.BigCf.BCA.big1 /=; last first.
- by rewrite Zppq.ZModpRing.addr0.
move=> j [/mem_range rgj @/predC1 ne_ji].
rewrite rcoeffZ rcoeff_polyXn // (eq_sym i j) ne_ji /=.
- by rewrite Zppq.ZModpRing.mulr0.
qed.

lemma cmuZq_red23 (z : Zq) (m : Z2) :
      Zp2Zppq ((scaleZq2Zp z) + (Zp.inzmod (shl (Z2.asint m) (2 * ep - eq - 1))))
      =
      scaleZp2Zppq ((Zq2Zp z) + Zp.inzmod (shl (Z2.asint m) (ep - 1))).
proof.
rewrite /Zp2Zppq /Zq2Zp /scaleZq2Zp /scaleZp2Zppq /scale /shr /shl !Zp.inzmodK !modzDm 
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


op shl_enc_2 (x : R2, ex : int) : Rp =  
  BigRp.XnD1CA.bigi predT (fun (i : int) => 
  Zp.inzmod (shl (Z2.asint x.[i]) ex) ** exp Rp.iX i) 0 n.
   
op shl_dec_2 (x : R2t) : Rp =
  BigRp.XnD1CA.bigi predT (fun (i : int) => 
  Zp.inzmod (shl (Z2t.asint x.[i]) (ep - et - 1)) ** exp Rp.iX i) 0 n.

lemma cmu_red23 (p : Rq) (m : R2) :
      Rp2Rppq ((scaleRq2Rp p) + (shl_enc_2 m (2 * ep - eq - 1)))
      =
      scaleRp2Rppq ((Rq2Rp p) + (shl_enc_2 m (ep - 1))).
proof.
rewrite polyXnD1_eqP => i rngi.
rewrite /Rp2Rppq /scaleRp2Rppq.
rewrite 2!rcoeff_sum /=.
rewrite !(Rppq.BasePoly.BigCf.BCA.bigD1 _ _ i) /=; first 4 smt(mem_range range_uniq).
rewrite Rppq.BasePoly.BigCf.BCA.big_seq_cond eq_sym Rppq.BasePoly.BigCf.BCA.big_seq_cond.
rewrite !Rppq.BasePoly.BigCf.BCA.big1 /= 3:2!Zppq.ZModpRing.addr0 =>
        [j [/mem_range rngj @/predC1 ne_ji] | j [/mem_range rngj @/predC1 ne_ji] |];
        first 2 by rewrite rcoeffZ rcoeff_polyXn // (eq_sym i) ne_ji /= Zppq.ZModpRing.mulr0.
rewrite 2!rcoeffZ rcoeff_polyXn //= 2!Zppq.ZModpRing.mulr1.
rewrite /Rq2Rp /shl_enc_2. rewrite -BigRp.XnD1CA.big_split /=.
rewrite rcoeff_sum /=.
rewrite (BCA.bigD1 _ _ i) /=; first 2 smt(mem_range range_uniq).
rewrite BCA.big_seq_cond BCA.big1 2:Zp.ZModpRing.addr0 => [j [/mem_range rngj @/predC1 ne_ji]|] /=.
by rewrite rcoeffD 2!rcoeffZ !rcoeff_polyXn // (eq_sym i) ne_ji /= 2!Zp.ZModpRing.mulr0 Zp.ZModpRing.addr0.
rewrite rcoeffD 2!rcoeffZ !rcoeff_polyXn //= 2!Zp.ZModpRing.mulr1.
rewrite /scaleRq2Rp -BigRp.XnD1CA.big_split /= rcoeff_sum /=.
rewrite (BCA.bigD1 _ _ i) /=; first 2 smt(mem_range range_uniq).
rewrite BCA.big_seq_cond BCA.big1 2:Zp.ZModpRing.addr0 => [j [/mem_range rngj @/predC1 ne_ji]|] /=.
by rewrite rcoeffD 2!rcoeffZ !rcoeff_polyXn // (eq_sym i) ne_ji /= 2!Zp.ZModpRing.mulr0 Zp.ZModpRing.addr0.
rewrite rcoeffD 2!rcoeffZ !rcoeff_polyXn //= 2!Zp.ZModpRing.mulr1.
by rewrite eq_sym; apply cmuZq_red23.
qed.

(* ------------------------------------------------------------------------------------- *)
(*  Saber's PKE Scheme                                                                   *)
(* ------------------------------------------------------------------------------------- *)

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
      m' <- scale_Rp_R2 (v  - (shl_dec cm) + (mod_p_Rq h2));
      
      return Some (m_encode m');
   }
}.
