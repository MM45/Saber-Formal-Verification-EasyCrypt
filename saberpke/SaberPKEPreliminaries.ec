(* ------------------------------------------------------------------------------------- *)
(*  Require/Import Theories                                                              *)
(* ------------------------------------------------------------------------------------- *)

(* --- Built-in --- *)
require import AllCore List Ring RealExp ZModP IntDiv Bigalg StdRing StdOrder FloorCeil.
require import Distr DInterval DList DMap.
require (*--*) Matrix PKE.
(*---*) import RField RealOrder IntOrder IntID.

(* --- Local --- *)
require (*--*) PolyReduce.

(* ------------------------------------------------------------------------------------- *)
(*  General Preliminaries                                                                *)
(* ------------------------------------------------------------------------------------- *)

lemma ltz_weexpn2l x m n: 2 <= x => 0 <= m => 0 <= n => m < n => exp x m < exp x n.
proof.
move => ge2_x ge0_m ge0_n gtm_n; have -> : n = (n - m) + m by ring.
rewrite exprD_nneg ?(ltr_pmull, expr_gt0, exprn_egt1, neq_ltz); smt().
qed.

lemma ltz_expeqb x m n: 1 <= x => 0 <= m => 0 <= n => exp x m < exp x n => m < n.
proof.
move => ge1_x ge0_m ge0_n; rewrite &(contraLR) !ltzNge /= => lem_n. 
by apply ler_weexpn2l; smt().
qed.

lemma lez_expeqb x m n: 2 <= x => 0 <= m => 0 <= n => exp x m <= exp x n => m <= n.
proof.
move => ge2_x ge0_m ge0_n; rewrite !lez_eqVlt; case => [eq_exp | lt_exp].
+ left; apply (ieexprIn x); smt().
+ right; apply (ltz_expeqb x); smt().
qed.

lemma modz_pow2_mul (n p i : int) : 0 <= p <= n =>
  ((i %% 2 ^ p) * 2 ^ (n - p)) %% 2 ^ n = (i * 2 ^ (n - p)) %% 2 ^ n.
proof.
move => rng_p; case (p = 0) => [-> /= | neq0_p].
+ by rewrite expr0 /= modzMl.
+ rewrite modzE eq_sym modzE {1 3}(_ : 2 ^ n = 2 ^ (n - p) * 2 ^ p) 1:-exprD_nneg; first 3 smt().
  rewrite {2}(mulzC i) {2}(mulzC (i %% 2 ^ p)) eq_sym !divzMpl; first 2 smt(expr_gt0). 
  rewrite pdiv_small /=; 1: smt(modz_ge0 ltz_pmod expr_gt0).
  rewrite modzE mulrBl -mulrA -exprD_nneg; first 2 smt().
  by rewrite (addzC p) -addzA.
qed.


op round (x : real) : int = floor (x + 0.5).

lemma floor_intDlt1 (n : int) (x : real) :
  0%r <= x < 1%r => floor (n%r + x) = n.
proof.
case=> ge0_x lt1_x; rewrite &(floorE) ler_addl ge0_x /=.
by rewrite fromintD ltr_add2l.
qed.

lemma round_int (n : int) : round n%r = n.
proof.
by apply: floor_intDlt1 => /=; rewrite RealOrder.invr_ge0 RealOrder.invr_lt1.
qed.

lemma round0 : round 0%r = 0. 
proof. by apply (round_int 0). qed.

lemma floor_divz (m n : int) : 0 <= n => m %/ n = floor (m%r / n%r).
proof.
rewrite ler_eqVlt; case=> [<-/=|]; first by rewrite from_int_floor.
move=> gt0_n; rewrite eq_sym &(floorE); split=> [|_].
- by rewrite ler_pdivl_mulr 1:/# -fromintM le_fromint lez_floor //#.
- rewrite fromintD ltr_pdivr_mulr 1:/# -fromintD -fromintM.
  by rewrite lt_fromint &(ltz_ceil).
qed.

lemma round_div_pow2 (x r : int) : 0 < r =>
  round (x%r / (2^r)%r) = (x + 2^(r - 1)) %/ 2^r.
proof.
move=> gt0_r; rewrite floor_divz 1:expr_ge0 //.
rewrite fromintD mulrDl /round; do 2! congr.
by rewrite -!fromintXn 1,2:/# -exprN -exprD // addrAC /= exprN1.
qed.

(* ------------------------------------------------------------------------------------- *)
(*  Saber Preliminaries                                                                  *)
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
axiom sec_assumption_og: q %/ p <= p %/ (2 * t).
axiom ge1_l: 1 <= l.

lemma ge0_et: 0 <= et by apply /(lez_add2l (-1) 1 (et + 1)) /ge1_et1.
lemma ge2_ep: 2 <= ep by apply /(lez_trans (et + 2) 2 ep) /geet2_ep /(lez_add2r 2 0 et) /ge0_et.
lemma ge3_eq: 3 <= eq by apply /(lez_trans (ep + 1) 3 eq) /geep1_eq /(lez_add2r 1 2 ep) /ge2_ep.

lemma ge1_n : 1 <= n by rewrite exprn_ege1 1:ge0_en.
lemma ge0_n: 0 <= n by smt(ge1_n).
lemma ge1_t: 1 <= t by rewrite exprn_ege1 1:ge0_et.
lemma ge2_2t: 2 <= 2 * t by move: (ler_pmul2l 2 _ 1 t); rewrite // ge1_t //.
lemma ge4_p: 4 <= p by move: (ler_weexpn2l 2 _ 2 ep); rewrite //= ge2_ep /= expr2.
lemma ge8_q: 8 <= q by move: (ler_weexpn2l 2 _ 3 eq); rewrite //= ge3_eq /= (IntID.exprS 2 2) // expr2.

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

lemma sec_assumption_exp: eq - ep <= ep - et - 1.
proof.
move: sec_assumption_og.
have ->: q %/ p = 2 ^ (eq - ep).
+ rewrite eq_sym eqz_div 2:p_div_q; 1: smt(ge4_p).
  rewrite /p /q -exprD_nneg; smt(geep1_eq ge2_ep).
have ->: p %/ (2 * t) = 2 ^ (ep - et - 1).
+ rewrite eq_sym eqz_div 2: twot_div_p; 1: smt(ge1_t).
  rewrite /t -exprS 1:ge0_et -exprD_nneg; smt(geet2_ep ge0_et).
apply lez_expeqb; smt(geep1_eq geet2_ep).
qed.

lemma geeq1_2ep: eq + 1 <= 2 * ep.
proof.
have le0_eq2ep: eq - ep - ep <= -1.
+ apply (lez_trans (-et - 1) (eq - ep - ep) (-1)). 
+ by move: (lez_add2l (-ep) (eq - ep) (ep - et - 1)); rewrite sec_assumption_exp addzC 2!addzA.
+ by rewrite -(lez_add2r (et + 1) (-et - 1) (-1)) addzA addzC addzA /= ge0_et.
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
+ have ->: p * p %/ q * q = p * p.
  - by rewrite -(dvdz_eq q (p * p)) q_div_pp.
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
+  by rewrite -(dvdz_eq q (p * p)) q_div_pp.
rewrite /p /q -exprD_nneg; first by rewrite subz_ge0 (lez_trans (eq + 1) eq (2 * ep)); 
        [rewrite (lez_addl _ 1) | apply geeq1_2ep].
by apply /(lez_trans 3 0 eq) /ge3_eq.
rewrite -exprD_nneg; first 2 by rewrite (lez_trans 2 0 ep); [| apply ge2_ep || apply ge2_ep ].
+ by congr; rewrite -addzA /= mulzC -mul1r2z /ofint_id intmulz.
qed.


(* --- Types, Operators and Distributions --- *)
abstract theory PolyZ.
clone import ZModRing as Zmod.

clone import PolyReduce.PolyReduceZp as Rmod with
  type Zp <- Zmod.zmod,
    op p  <- Zmod.p,
    op n  <- n,
theory Zp <= Zmod 

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
    op size      <- l,

  type ZR.t      <- Rq,
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
  
  proof ge0_size by apply (lez_trans 1 _ _ _ ge1_l),
        ZR.addrA by exact Rq.ComRing.addrA,
        ZR.addrC by exact Rq.ComRing.addrC, 
        ZR.add0r by exact Rq.ComRing.add0r,
        ZR.addNr by exact Rq.ComRing.addNr,
        ZR.oner_neq0 by exact Rq.ComRing.oner_neq0,
        ZR.mulrA by exact Rq.ComRing.mulrA,
        ZR.mulrC by exact Rq.ComRing.mulrC,
        ZR.mul1r by exact Rq.ComRing.mul1r,
        ZR.mulrDl by exact Rq.ComRing.mulrDl,
        ZR.mulVr by exact Rq.ComRing.mulVr,
        ZR.unitP by exact Rq.ComRing.unitP,
        ZR.unitout by exact Rq.ComRing.unitout.
    
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
  op size      <- l,

  type ZR.t      <- Rp,
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

  proof ge0_size by apply (lez_trans 1 _ _ _ ge1_l),
        ZR.addrA by exact Rp.ComRing.addrA,
        ZR.addrC by exact Rp.ComRing.addrC, 
        ZR.add0r by exact Rp.ComRing.add0r,
        ZR.addNr by exact Rp.ComRing.addNr,
        ZR.oner_neq0 by exact Rp.ComRing.oner_neq0,
        ZR.mulrA by exact Rp.ComRing.mulrA,
        ZR.mulrC by exact Rp.ComRing.mulrC,
        ZR.mul1r by exact Rp.ComRing.mul1r,
        ZR.mulrDl by exact Rp.ComRing.mulrDl,
        ZR.mulVr by exact Rp.ComRing.mulVr,
        ZR.unitP by exact Rp.ComRing.unitP,
        ZR.unitout by exact Rp.ComRing.unitout.

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

(* - Support of dsmallRq_vec - *)
lemma supp_dsmallRq_vec (x : Rq_vec) :
  x \in dsmallRq_vec <=> forall (i : int), 0 <= i < l => x.[i] \in dsmallRq.
proof.
split => [+ i rng_i| memxele]; rewrite supp_dmap.
+ elim => xlist [/supp_djoin [sizexl /allP /= zipxl]].
  rewrite size_nseq maxrE lezNgt -lez_add1r ge1_l /= eq_sym in sizexl.
  rewrite eq_vectorP => h1; move: (h1 i); rewrite rng_i /=.
  rewrite offunvE 1:rng_i => xi_nth.  
  move: (mem_nth witness xlist i); rewrite sizexl rng_i /= -xi_nth.
  move /(mem_zip_nseqL dsmallRq x.[i]); rewrite sizexl => memzipnseq.
  by move: (zipxl ((dsmallRq, x.[i])) memzipnseq).
+ pose xlist := mkseq (Mat_Rq.Vector.tofunv x) l.
  exists xlist; split; first rewrite supp_djoin; split; 1: by rewrite size_nseq size_mkseq.
  - rewrite allP /= => y memyzip.
    move: (mem_zip_fst (nseq l dsmallRq) xlist y) (mem_zip_snd (nseq l dsmallRq) xlist y).
    rewrite memyzip //= /xlist mem_nseq -lez_add1r ge1_l /= => <- /mkseqP.
    elim => i [rng_i ->]; by apply memxele.
  - rewrite /xlist /= eq_vectorP => i rng_i.
    by rewrite offunvE 1:rng_i nth_mkseq.
qed.

(* - Constants - *)
const h1 : Rq = 
  BigRq.XnD1CA.bigi predT (fun (i : int) => Zq.inzmod (2 ^ (eq - ep - 1)) ** exp Rq.iX i) 0 n.
const h2 : Rq = 
  BigRq.XnD1CA.bigi predT (fun (i : int) => 
  Zq.inzmod (2 ^ (ep - 2) - 2 ^ (ep - et - 2)) ** exp Rq.iX i) 0 n.
const h : Rq_vec = vectc h1.

const q4_Rq : Rq =
  BigRq.XnD1CA.bigi predT (fun (i : int) => Zq.inzmod (2 ^ (eq - 2)) ** exp Rq.iX i) 0 n.
const q4t_Rq : Rq =
  BigRq.XnD1CA.bigi predT (fun (i : int) => Zq.inzmod (2 ^ (eq - et - 2)) ** exp Rq.iX i) 0 n.

(* - Auxiliary - *)
(* Ring Instances for ring Tactic *)
instance ring with R2
  op rzero = R2.zeroXnD1
  op rone  = R2.oneXnD1
  op add   = R2.( + )
  op opp   = R2.([-])
  op mul   = R2.( * )
  op expr  = R2.ComRing.exp
  op ofint = R2.ComRing.ofint

  proof oner_neq0 by apply R2.ComRing.oner_neq0
  proof addrA     by apply R2.ComRing.addrA
  proof addrC     by apply R2.ComRing.addrC
  proof addr0     by apply R2.ComRing.addr0
  proof addrN     by apply R2.ComRing.addrN
  proof mulr1     by apply R2.ComRing.mulr1
  proof mulrA     by apply R2.ComRing.mulrA
  proof mulrC     by apply R2.ComRing.mulrC
  proof mulrDl    by apply R2.ComRing.mulrDl
  proof expr0     by apply R2.ComRing.expr0
  proof ofint0    by apply R2.ComRing.ofint0
  proof ofint1    by apply R2.ComRing.ofint1
  proof exprS     by apply R2.ComRing.exprS
  proof ofintS    by apply R2.ComRing.ofintS
  proof ofintN    by apply R2.ComRing.ofintN.

instance ring with Rp
  op rzero = Rp.zeroXnD1
  op rone  = Rp.oneXnD1
  op add   = Rp.( + )
  op opp   = Rp.([-])
  op mul   = Rp.( * )
  op expr  = Rp.ComRing.exp
  op ofint = Rp.ComRing.ofint

  proof oner_neq0 by apply Rp.ComRing.oner_neq0
  proof addrA     by apply Rp.ComRing.addrA
  proof addrC     by apply Rp.ComRing.addrC
  proof addr0     by apply Rp.ComRing.addr0
  proof addrN     by apply Rp.ComRing.addrN
  proof mulr1     by apply Rp.ComRing.mulr1
  proof mulrA     by apply Rp.ComRing.mulrA
  proof mulrC     by apply Rp.ComRing.mulrC
  proof mulrDl    by apply Rp.ComRing.mulrDl
  proof expr0     by apply Rp.ComRing.expr0
  proof ofint0    by apply Rp.ComRing.ofint0
  proof ofint1    by apply Rp.ComRing.ofint1
  proof exprS     by apply Rp.ComRing.exprS
  proof ofintS    by apply Rp.ComRing.ofintS
  proof ofintN    by apply Rp.ComRing.ofintN.

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

(* -- Cryptographic Types and Distributions  -- *)
type seed.

op [lossless full uniform] dseed : seed distr.

(* -- Operations -- *)
op gen : seed -> Rq_mat.

(* - Modular Reduction/Modulus Conversion - *)
op Zq2Zp (z : Zq) : Zp = Zp.inzmod (Zq.asint z).
op Zp2Zq (z : Zp) : Zq = Zq.inzmod (Zp.asint z).
op Zp2Zppq (z : Zp) : Zppq = Zppq.inzmod (Zp.asint z).

(* Lift Modular Reduction/Modulus Conversion to Polynomials *)
op Rq2Rp (p : Rq) : Rp =
  BigRp.XnD1CA.bigi predT (fun (i : int) => Zq2Zp p.[i] ** exp Rp.iX i) 0 n.
op Rp2Rq (p : Rp) : Rq =
  BigRq.XnD1CA.bigi predT (fun (i : int) => Zp2Zq p.[i] ** exp Rq.iX i) 0 n.
op Rp2Rppq (p : Rp) : Rppq =
  BigRppq.XnD1CA.bigi predT (fun (i : int) => Zp2Zppq p.[i] ** exp Rppq.iX i) 0 n.

(* Lift Modular Reduction/Modulus Conversion to Polynomial Vectors *)
op Rqv2Rpv (pv : Rq_vec) : Rp_vec = offunv (fun (i : int) => Rq2Rp pv.[i]).
op Rpv2Rqv (pv : Rp_vec) : Rq_vec = offunv (fun (i : int) => Rp2Rq pv.[i]).

(* - Scaling (Bit-shift + Modulus Conversion) - *)
op shl (x : int, ex : int) : int = x * 2 ^ ex.
op shr (x : int, ex : int) : int = x %/ 2 ^ ex.

op downscale (x : int, ea : int, eb : int) : int = shr x (ea - eb).
op upscale (x : int, ea : int, eb : int) : int = shl x (ea - eb).

op downscaleround (x : int, ea : int, eb : int) : int = round(x%r / (2 ^ (ea - eb))%r).

(* Z Scaling Without Modulus Conversion *)
op upscaleZq (z : Zq, ez : int) : Zq = Zq.inzmod (upscale (Zq.asint z) ez 0).

(* Z Downscaling *)
op scaleZq2Zp (z : Zq) : Zp = Zp.inzmod (downscale (Zq.asint z) eq ep).
op scaleZq2Z2 (z : Zq) : Z2 = Z2.inzmod (downscale (Zq.asint z) eq 1).
op scaleZq2Z2t (z : Zq) : Z2t = Z2t.inzmod (downscale (Zq.asint z) eq (et + 1)).
op scaleZp2Zppq (z : Zp) : Zppq = Zppq.inzmod (downscale (Zp.asint z) ep (2 * ep - eq)).
op scaleZp2Z2t (z : Zp) : Z2t = Z2t.inzmod (downscale (Zp.asint z) ep (et + 1)).
op scaleZp2Z2 (z : Zp) : Z2 = Z2.inzmod (downscale (Zp.asint z) ep 1).
op scaleZppq2Z2t (z : Zppq) : Z2t = Z2t.inzmod (downscale (Zppq.asint z) (2 * ep - eq) (et + 1)).

op scaleroundZq2Zp (z : Zq) : Zp = Zp.inzmod (downscaleround (Zq.asint z) eq ep).
  
(* Z Upscaling *)
op scaleZ22Zp (z : Z2) : Zp = Zp.inzmod (upscale (Z2.asint z) ep 1).
op scaleZ22Zq (z : Z2) : Zq = Zq.inzmod (upscale (Z2.asint z) eq 1).
op scaleZ2t2Zp (z : Z2t) : Zp = Zp.inzmod (upscale (Z2t.asint z) ep (et + 1)).
op scaleZ2t2Zq (z : Z2t) : Zq = Zq.inzmod (upscale (Z2t.asint z) eq (et + 1)).
op scaleZp2Zq (z : Zp) : Zq = Zq.inzmod (upscale (Zp.asint z) eq ep).

(* Z Variable Scaling *)
op scaleZ22Zp_var (z : Z2) (ez : int) : Zp = Zp.inzmod (upscale (Z2.asint z) ez 0).
op scaleZ2t2Zp_var (z : Z2t) (ez : int) : Zp = Zp.inzmod (upscale (Z2t.asint z) ez 0).

(* Lift Scaling Without Modulus Conversion to Polynomials *)
op upscaleRq (p : Rq, er : int) : Rq = 
  BigRq.XnD1CA.bigi predT (fun i => (upscaleZq p.[i] er) ** exp Rq.iX i) 0 n.

(* Lift Downscaling to Polynomials *)
op scaleRq2Rp (p : Rq) : Rp = 
  BigRp.XnD1CA.bigi predT (fun (i : int) => scaleZq2Zp p.[i] ** exp Rp.iX i) 0 n.
op scaleRq2R2t (p : Rq) : R2t =
  BigR2t.XnD1CA.bigi predT (fun i => scaleZq2Z2t p.[i] ** exp R2t.iX i) 0 n.
op scaleRq2R2 (p : Rq) : R2 =
  BigR2.XnD1CA.bigi predT (fun i => scaleZq2Z2 p.[i] ** exp R2.iX i) 0 n. 
op scaleRp2Rppq (p : Rp) : Rppq = 
  BigRppq.XnD1CA.bigi predT (fun (i : int) => scaleZp2Zppq p.[i] ** exp Rppq.iX i) 0 n.
op scaleRp2R2t (p : Rp) : R2t = 
  BigR2t.XnD1CA.bigi predT (fun (i : int) => scaleZp2Z2t p.[i] ** exp R2t.iX i) 0 n.
op scaleRp2R2 (p : Rp) : R2 = 
  BigR2.XnD1CA.bigi predT (fun (i : int) => scaleZp2Z2 p.[i] ** exp R2.iX i) 0 n.
op scaleRppq2R2t (p : Rppq) : R2t = 
  BigR2t.XnD1CA.bigi predT (fun (i : int) => scaleZppq2Z2t p.[i] ** exp R2t.iX i) 0 n.

op scaleroundRq2Rp (p : Rq) : Rp = 
  BigRp.XnD1CA.bigi predT (fun (i : int) => scaleroundZq2Zp p.[i] ** exp Rp.iX i) 0 n.
  
(* Lift Upscaling to Polynomials *)
op scaleR22Rp (p : R2) : Rp =
  BigRp.XnD1CA.bigi predT (fun i => scaleZ22Zp p.[i] ** exp Rp.iX i) 0 n.
op scaleR22Rq (p : R2) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZ22Zq p.[i] ** exp Rq.iX i) 0 n.
op scaleR2t2Rp (p : R2t) : Rp =
  BigRp.XnD1CA.bigi predT (fun i => scaleZ2t2Zp p.[i] ** exp Rp.iX i) 0 n.
op scaleR2t2Rq (p : R2t) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZ2t2Zq p.[i] ** exp Rq.iX i) 0 n.
op scaleRp2Rq (p : Rp) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZp2Zq p.[i] ** exp Rq.iX i) 0 n.

(* Lift Variable Scaling to Polynomials *)
op scaleR22Rp_var (p : R2) (ep : int) : Rp =
  BigRp.XnD1CA.bigi predT (fun i => (scaleZ22Zp_var p.[i] ep) ** exp Rp.iX i) 0 n.
op scaleR2t2Rp_var (p : R2t) (ep : int) : Rp =
  BigRp.XnD1CA.bigi predT (fun i => (scaleZ2t2Zp_var p.[i] ep) ** exp Rp.iX i) 0 n.

(* Lift Downscaling to Polynomial Vectors *)
op scaleRqv2Rpv (pv : Rq_vec) : Rp_vec = offunv (fun (i : int) => scaleRq2Rp pv.[i]).

op scaleroundRqv2Rpv (pv : Rq_vec) : Rp_vec = offunv (fun (i : int) => scaleroundRq2Rp pv.[i]).

(* Lift Upscaling to Polynomial Vectors *)
op scaleRpv2Rqv (pv : Rp_vec) : Rq_vec = offunv (fun i => scaleRp2Rq pv.[i]).

(* Possible Values of Z types *)
lemma Z2_asint_values (z : Z2) : asint z = 0 \/ asint z = 1.
proof. 
case (asint z = 0) => [-> //| /= /neq_ltz].
case; move: (Z2.rg_asint z); case => [/lezNgt //| _].
by rewrite -!lez_add1r -(lez_add2l (-1)) /= eqz_leq => -> ->.
qed.

(* Modular Reduction/Modulo Conversion *)
lemma Zq2Zp0 : Zq2Zp Zq.zero = Zp.zero.
proof. by rewrite -eq_inzmod zeroE. qed.

lemma Zp2Zq0 : Zp2Zq Zp.zero = Zq.zero.
proof. by rewrite -eq_inzmod zeroE. qed.

lemma Zp2Zppq0 : Zp2Zppq Zp.zero = Zppq.zero.
proof. by rewrite -eq_inzmod zeroE. qed.

lemma Zq2Zp_DM : morphism_2 Zq2Zp Zq.( + ) Zp.( + ).
proof. by move => x y; rewrite /Zq2Zp /( + ) !inzmodK /inzmod modzDm modz_dvd 1:p_div_q. qed.

lemma Zq2Zp_BM : morphism_2 Zq2Zp Zq.( - ) Zp.( - ).
proof. 
by move => x y; rewrite /Zq2Zp /( + ) !inzmodK modzNm /inzmod modzDm modzDmr modz_dvd 1:p_div_q. 
qed.

lemma Zq2Zp_MM : morphism_2 Zq2Zp Zq.( * ) Zp.( * ).
proof. by move => x y; rewrite /Zq2Zp /( * ) !inzmodK /inzmod modzMm modz_dvd 1:p_div_q. qed.

lemma Zq2Zp_DM_big_BPCf (F : int -> Zq) (r : int list) :
      Zq2Zp (Rq.BasePoly.BigCf.BCA.big predT F r)
      =
      BCA.big predT (Zq2Zp \o F) r.
proof.
elim: r; first by rewrite BCA.big_nil Rq.BasePoly.BigCf.BCA.big_nil Zq2Zp0.
move => x l @/(\o) IH; rewrite BCA.big_consT Rq.BasePoly.BigCf.BCA.big_consT /=.
by rewrite (Zq2Zp_DM (F x) (Rq.BasePoly.BigCf.BCA.big predT F l)); congr.
qed.

lemma Zp2Zq_Zq2Zp_inv (z : Zp) : Zq2Zp (Zp2Zq z) = z.
proof.
rewrite /Zq2Zp /Zp2Zq inzmodK modz_small 1: ge0_asint 2:asintK //=.
rewrite ger0_norm 2:(ltr_le_trans p _ _ (Zp.gtp_asint z)) /p /q; first smt(ge8_q).
by apply (ler_weexpn2l 2 _ ep eq _); 2: smt(ge2_ep geep1_eq).
qed.

lemma Zq2Zp_Zp2Zq_small_inv (z : Zq) : asint z < p => Zp2Zq (Zq2Zp z) = z.
proof.
move => ltp_z; by rewrite /Zq2Zp /Zp2Zq -{2}asintK inzmodK pmod_small 2?(ge0_asint, ltp_z).
qed.

(* Polynomial Lift Modular Reduction/Modulo Conversion *)
lemma Rq2Rp0 : Rq2Rp Rq.zeroXnD1 = Rp.zeroXnD1.
proof. by rewrite polyXnD1_eqP => *; rewrite rcoeffZ_sum //= 2!rcoeff0 Zq2Zp0. qed.  

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

lemma Rq2Rp_DM : morphism_2 Rq2Rp Rq.( + ) Rp.( + ).
proof.
move=> x y; rewrite polyXnD1_eqP => i [ge0_i ltn_i].
by rewrite eq_sym rcoeffD !Rq2RpE rcoeffD (Zq2Zp_DM x.[i] y.[i]).
qed.

lemma Rq2Rp_MM : morphism_2 Rq2Rp Rq.( * ) Rp.( * ).
proof.
move => x y; rewrite polyXnD1_eqP => i rng_i; rewrite Rq2RpE !rcoeffM 1,2://# eq_sym.
rewrite Zq2Zp_DM_big_BPCf /(\o) 2!BCA.big_seq &(BCA.eq_bigr) /= => j /mem_range rng_j. 
by rewrite !Rq2RpE Zq2Zp_BM 2!Zq2Zp_MM.
qed.

lemma Rq2Rp_DM_big_Mat (F : int -> Rq) (r : int list) :
      Rq2Rp (Mat_Rq.Big.BAdd.big predT F r)
      =
      Big.BAdd.big predT (Rq2Rp \o F) r.
proof.
elim: r; first by rewrite Big.BAdd.big_nil Mat_Rq.Big.BAdd.big_nil Rq2Rp0.
move => x l @/(\o) IH; rewrite Big.BAdd.big_consT Mat_Rq.Big.BAdd.big_consT /=.
by rewrite Rq2Rp_DM; congr.
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

(* Polynomial Vector Lift Modular Reduction/Modulo Conversion *)
lemma Rqv2RpvE (p : Rq_vec) (i : int) : (Rqv2Rpv p).[i] = Rq2Rp p.[i].
proof.
rewrite /Rqv2Rpv /Mat_Rp.Vector."_.[_]" offunvK /vclamp.
case (0 <= i && i < l) => //; move/(Mat_Rq.Vector.getv_out p i) => ->.
rewrite /Rq2Rp eq_sym BigRp.XnD1CA.big_seq BigRp.XnD1CA.big1 => //= j; case/mem_range => ge0_j ltn_j.
have ->: Zq2Zp Rq.zeroXnD1.[j] = Zp.zero; 2: rewrite /( ** ) scale0p //.
by rewrite /zeror /"_.[_]" piK 1:reducedP 1:degC // -/Rq.BasePoly."_.[_]" poly0E /Zq2Zp Zq.zeroE.
qed.

lemma Rpv2RqvE (p : Rp_vec) (i : int) : (Rpv2Rqv p).[i] = Rp2Rq p.[i].
proof.
rewrite /Rpv2Rqv /Mat_Rq.Vector."_.[_]" offunvK /vclamp.
case (0 <= i && i < l) => //; move/(Mat_Rp.Vector.getv_out p i) => ->.
rewrite /Rp2Rq eq_sym BigRq.XnD1CA.big_seq BigRq.XnD1CA.big1 => //= j /mem_range [ge0_j ltn_j].
by rewrite rcoeff0 Zp2Zq0 scale0p.
qed.

lemma Rpv2Rqv_Rqv2Rpv_inv (pv : Rp_vec) : Rqv2Rpv (Rpv2Rqv pv) = pv.
proof.
rewrite /Rqv2Rpv eq_vectorP => i rngi.
by rewrite {1}/Mat_Rp.Vector."_.[_]" offunvK /vclamp rngi /= Rpv2RqvE Rp2Rq_Rq2Rp_inv.
qed.

(* Remaining Dependent Modulo Reduction/Conversion Properties *)
lemma Rq2Rp_DotDl (a : Rq_vec) (b : Rq_vec) : Rq2Rp (dotp a b) = dotp (Rqv2Rpv a) (Rqv2Rpv b).
proof.
rewrite /dotp Rq2Rp_DM_big_Mat /(\o) !Big.BAdd.big_seq &(Big.BAdd.eq_bigr) /= => j /mem_range rng_j. 
by rewrite Rq2Rp_MM 2!Rqv2RpvE.
qed.

lemma Rq2Rp_DotDll (a : Rq_vec) (b : Rp_vec) : Rq2Rp (dotp a (Rpv2Rqv b)) = dotp (Rqv2Rpv a) b.
proof. by rewrite Rq2Rp_DotDl dotpC Rpv2Rqv_Rqv2Rpv_inv dotpC. qed.

lemma Rq2Rp_DotDlr (a : Rp_vec) (b : Rq_vec) : Rq2Rp (dotp (Rpv2Rqv a) b) = dotp a (Rqv2Rpv b).
proof. by rewrite Rq2Rp_DotDl Rpv2Rqv_Rqv2Rpv_inv. qed.

(* - Distribution Mapping - *)
lemma duni_Zq2Zp : dmap DZqP.dunifin Zq2Zp = DZpP.dunifin.
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

lemma dRq2dRp : dmap dRq Rq2Rp = dRp.
proof.
rewrite /dRq /dRp /Rq.dpolyXnD1 /Rp.dpolyXnD1 -duni_Zq2Zp.
rewrite !(dmap_comp, dlist_dmap) &(eq_dmap_in).
move=> xs /(supp_dlist_size _ _ _ ge0_n) => szxs @/(\o).
apply/Rp.polyXnD1_eqP=> i rgi; rewrite Rq2RpE.
rewrite !piK; ~-1: by rewrite (reduced_polyL) ?size_map szxs.
by rewrite !polyLE (nth_map Zq.zero) ?szxs.
qed.

lemma dRqv2dRpv: dmap dRq_vec Rqv2Rpv = dRp_vec.
proof.
rewrite /dRp_vec /dRp /dRq_vec /dRq /Rq.dpolyXnD1 /Rp.dpolyXnD1 /dvector -duni_Zq2Zp.
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

clone import DMapSampling as DMapRqv2Rpv with
   type t1 <- Rq_vec,
   type t2 <- Rp_vec

   rename [module] "S" as "Rqv2RpvSampl".

(* - Scaling - *)
(* Integer Scaling *)
lemma downscale0 (ea eb : int) : downscale 0 ea eb = 0.
proof. by []. qed.

lemma upscale0 (ea eb : int) : upscale 0 ea eb = 0.
proof. by []. qed.

lemma downscale_id (x ea eb : int) : ea = eb => downscale x ea eb = x.
proof. by move=> eq_eaeb; rewrite /downscale /shr eq_eaeb addzN expr0. qed.

lemma upscale_id (x ea eb : int) : ea = eb => upscale x ea eb = x.
proof. by move=> eq_eaeb; rewrite /upscale /shl eq_eaeb addzN expr0. qed.

lemma downscale_DM (x y ea eb : int) : 
  2 ^ (ea - eb) %| x \/  2 ^ (ea - eb) %| y => 
  downscale (x + y) ea eb = downscale x ea eb + downscale y ea eb.
proof. by case; rewrite /downscale /shr; [apply divzDl | apply divzDr]. qed.

lemma upscale_DM (ea eb : int) : morphism_2 (fun x => upscale x ea eb) Int.(+) Int.(+).
proof. by move => x y; rewrite /upscale /shl mulrDl. qed.

lemma downscale_BM (x y ea eb: int) :
 2 ^ (ea - eb) %| y => downscale (x - y) ea eb = downscale x ea eb - downscale y ea eb.
proof.
move => divy; rewrite /downscale /shr &(mulIf (2 ^ (ea - eb))) 1:lt0r_neq0 1:expr_gt0 // mulrBl.
rewrite (divzK _ y) // 2!divzE -modzDmr; rewrite &(dvdzN) dvdzE in divy; rewrite divy; by ring.
qed.

lemma upscale_BM (x y ea eb: int) :
  upscale (x - y) ea eb = upscale x ea eb - upscale y ea eb.
proof. by rewrite /upscale /shl mulrBl. qed.

lemma downscale_comp (x ea eab eb : int) :
      0 <= x => 0 <= eb => eb <= eab => eab <= ea =>
      downscale x ea eb = downscale (downscale x ea eab) eab eb. 
proof. 
move=> ge0_x ge0_eb geeb_eab geeab_ea; rewrite /downscale /shr. 
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

lemma upscale_comp (x ea eb eab : int) : 
  eb <= eab => eab <= ea =>
  upscale x ea eb = upscale (upscale x ea eab) eab eb.
proof.
move => geeb_eab geeab_ea.
by rewrite /upscale /shl mulzA -exprD_nneg //#.
qed.

lemma upscale_comp_comm (x ea eb eab : int) : 
  eb <= eab => eab <= ea =>
  upscale x ea eb = upscale (upscale x eab eb) ea eab.
proof.
move => geeb_eab geeab_ea.
by rewrite /upscale /shl mulzA -exprD_nneg //#.
qed.

lemma upscale_MAl (x y ea eb : int) : upscale (x * y) ea eb = upscale x ea eb * y.
proof. by rewrite /upscale /shl mulrAC. qed.

(* Z Scaling *)
lemma scaleZ22Zp_var0 (ez : int) : scaleZ22Zp_var Z2.zero ez = Zp.zero.
proof. by rewrite /scaleZ22Zp_var zeroE. qed.

lemma scaleZ22Zp0 : scaleZ22Zp Z2.zero = Zp.zero.
proof. by rewrite /scaleZ22Zp zeroE. qed.

lemma scaleZ22Zq0 : scaleZ22Zq Z2.zero = Zq.zero.
proof. by rewrite /scaleZ22Zq zeroE. qed.

lemma scaleZq2Zp0 : scaleZq2Zp Zq.zero = Zp.zero.
proof. by rewrite /scaleZq2Zp zeroE. qed.

lemma scaleZp2Zq0 : scaleZp2Zq Zp.zero = Zq.zero.
proof. by rewrite /scaleZp2Zq zeroE. qed.

lemma scaleroundZq2Zp0 : scaleroundZq2Zp Zq.zero = Zp.zero.
proof. by rewrite /scaleroundZq2Zp /downscaleround zeroE mul0r round0. qed.

lemma upscaleZq0 (ez : int) : upscaleZq Zq.zero ez = Zq.zero.
proof. by rewrite /upscaleZq zeroE. qed. 

lemma upscaleZq_eqep_small (z : Zq) : 
  asint z < p => upscaleZq z (eq - ep) = scaleZp2Zq (Zq2Zp z).
proof.
move => ltp_z.
by rewrite -eq_inzmod /upscale /shl /Zq2Zp inzmodK (pmod_small (Zq.asint z)) 1:ge0_asint.
qed.

lemma upscaleZq_eqep_DM (z1 z2 : Zq) :
  upscaleZq (z1 + z2) (eq - ep) = upscaleZq z1 (eq - ep) + upscaleZq z2 (eq - ep).
proof.
by rewrite /upscaleZq -inzmodD -upscale_DM addE -eq_inzmod /upscale /shl /= /q modzMml.
qed.

lemma scaleZp2Z2_DM (z1 z2 : Zp) : 
  2 ^ (ep - 1) %| Zp.asint z1 \/  2 ^ (ep - 1) %| Zp.asint z2 => 
  scaleZp2Z2 (z1 + z2) = scaleZp2Z2 z1 + scaleZp2Z2 z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZp2Z2 -inzmodD -downscale_DM ?(divz1, divz2) //;
    rewrite addE /p /downscale /shr /inzmod modz_pow2_div; 1, 2, 4, 5: smt(Zp.ge0_asint ge2_ep);
    congr; by rewrite opprD addzA /= expr1 modz_mod.
qed.

lemma scaleZp2Z2t_DM (z1 z2 : Zp) : 
  2 ^ (ep - (et + 1)) %| Zp.asint z1 \/  2 ^ (ep - (et + 1)) %| Zp.asint z2 => 
  scaleZp2Z2t (z1 + z2) = scaleZp2Z2t z1 + scaleZp2Z2t z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZp2Z2t -inzmodD -downscale_DM ?(divz1, divz2) //;
    rewrite addE /p /downscale /shr /inzmod /t -exprS 1:ge0_et modz_pow2_div;
    1, 2, 4, 5: smt(Zp.ge0_asint geet2_ep ge0_et); congr; rewrite modz_dvd_pow; smt(ge0_et).
qed.

lemma scaleZq2Z2_DM (z1 z2 : Zq) : 
  2 ^ (eq - 1) %| Zq.asint z1 \/  2 ^ (eq - 1) %| Zq.asint z2 => 
  scaleZq2Z2 (z1 + z2) = scaleZq2Z2 z1 + scaleZq2Z2 z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZq2Z2 -inzmodD -downscale_DM ?(divz1, divz2) //;
    rewrite addE /q /downscale /shr /inzmod modz_pow2_div; 1, 2, 4, 5: smt(Zq.ge0_asint ge3_eq);
    congr; by rewrite opprD addzA /= expr1 modz_mod.
qed.

lemma scaleZq2Z2t_DM (z1 z2 : Zq) : 
  2 ^ (eq - (et + 1)) %| Zq.asint z1 \/  2 ^ (eq - (et + 1)) %| Zq.asint z2 => 
  scaleZq2Z2t (z1 + z2) = scaleZq2Z2t z1 + scaleZq2Z2t z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZq2Z2t -inzmodD -downscale_DM ?(divz1, divz2) //;
    rewrite addE /q /downscale /shr /inzmod /t -exprS 1:ge0_et modz_pow2_div;
    1, 2, 4, 5: smt(Zq.ge0_asint geet2_ep geep1_eq ge0_et); congr; rewrite modz_dvd_pow; smt(ge0_et).
qed.

lemma scaleZ2t2Zq_DM (z1 z2 : Z2t) : scaleZ2t2Zq (z1 + z2) = scaleZ2t2Zq z1 + scaleZ2t2Zq z2.
proof.
rewrite /scaleZ2t2Zq -inzmodD /upscale /shl -mulrDl addE -eq_inzmod /p /q /t -{1}(Ring.IntID.expr1 2)
        -exprD_nneg 2:ge0_et // (Ring.IntID.addrC 1 et) modz_pow2_mul //.
+ smt(ge0_et geet2_ep geep1_eq).
qed.

lemma scaleZp2Zq_DM (z1 z2 : Zp) : scaleZp2Zq (z1 + z2) = scaleZp2Zq z1 + scaleZp2Zq z2.
proof.
rewrite /scaleZp2Zq -inzmodD /upscale /shl -mulrDl addE -eq_inzmod /p /q modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.

lemma scaleZ22Zq_PN (z : Z2) : scaleZ22Zq z = scaleZ22Zq (- z).
proof.
rewrite /scaleZ22Zq /upscale /shl -eq_inzmod !inzmodK; do 3! congr.
case (asint z = 0) => [-> //| /neq_ltz [lt0_z | gt0_z]]; move: (Z2.rg_asint z); case => ge0_z lt2_z.
+ by rewrite ltzNge in lt0_z.
+ rewrite -lez_add1r -(lez_add2l (-1)) /= in lt2_z; rewrite -lez_add1r /= in gt0_z.
  by move: (eqz_leq (asint z) 1); rewrite gt0_z lt2_z /= => ->.
qed.

lemma scaleZ2t2Zp_N (z : Z2t) : scaleZ2t2Zp (- z) = - scaleZ2t2Zp z.
proof.
rewrite /scaleZ2t2Zp /upscale /shl -inzmodN oppE -eq_inzmod -modz_pow2_mul; 1: smt(ge0_et geet2_ep).
rewrite /t /p -{1}(Ring.IntID.expr1 2) -exprD_nneg 2:ge0_et // (Ring.IntID.addrC 1 et) modz_mod
        modz_pow2_mul; 1: smt(ge0_et geet2_ep).
by rewrite mulNr.
qed.

lemma scaleZ2t2Zq_N (z : Z2t) : scaleZ2t2Zq (- z) = - scaleZ2t2Zq z.
proof.
rewrite /scaleZ2t2Zq /upscale /shl -inzmodN oppE -eq_inzmod -modz_pow2_mul;
         1: smt(ge0_et geet2_ep geep1_eq).
rewrite /t /q -{1}(Ring.IntID.expr1 2) -exprD_nneg 2:ge0_et // (Ring.IntID.addrC 1 et) modz_mod
        modz_pow2_mul; 1: smt(ge0_et geet2_ep geep1_eq).
by rewrite mulNr.
qed.

lemma scaleZ22Zq_N (z : Z2) : scaleZ22Zq (- z) = - scaleZ22Zq z.
proof.
rewrite /scaleZ22Zq /upscale /shl -inzmodN oppE -eq_inzmod /q -modz_pow2_mul; 1: smt(ge3_eq).
rewrite expr1 modz_mod -{1}(Ring.IntID.expr1 2) modz_pow2_mul; 1: smt(ge3_eq).
by rewrite mulNr.
qed.

lemma scaleZp2Zq_N (z : Zp) : scaleZp2Zq (- z) = - scaleZp2Zq z.
proof.
rewrite /scaleZp2Zq /upscale /shl -eq_inzmod !inzmodK /p /q modz_pow2_mul; 1: smt(ge2_ep geep1_eq).
by rewrite modzNm mulNr.
qed.

lemma upscaleZq_eqep_BM (z1 z2 : Zq) : 
  upscaleZq (z1 - z2) (eq - ep) = upscaleZq z1 (eq - ep) - upscaleZq z2 (eq - ep).
proof.
by rewrite /upscaleZq -inzmodB /upscale /shl addE oppE -mulrBl -eq_inzmod /p /q modzDmr modzMml.
qed.

lemma scaleZp2Zq_BM (z1 z2 : Zp) : scaleZp2Zq (z1 - z2) = scaleZp2Zq z1 - scaleZp2Zq z2.
proof.
rewrite /scaleZp2Zq -inzmodB /upscale /shl addE oppE -mulrBl -eq_inzmod /p /q.
rewrite modzDmr modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.

lemma upscaleZq_eqep_MAl (z1 z2 : Zq) :
  upscaleZq (z1 * z2) (eq - ep) = upscaleZq z1 (eq - ep) * z2.
proof.
by rewrite /upscaleZq -{2}(Zq.asintK z2) -inzmodM -upscale_MAl mulE 
           -eq_inzmod /upscale /shl /q modzMml.
qed.

lemma scaleZp2Zq_MA (z1 z2 : Zp) : scaleZp2Zq (z1 * z2) = scaleZp2Zq z1 * Zp2Zq z2.
proof.
rewrite /scaleZp2Zq /Zp2Zq -inzmodM /upscale /shl mulrAC mulE -eq_inzmod /p /q modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.

lemma upscaleZq_eqep_DM_big_BPCf (F : int -> Zq) (r: int list) :
  upscaleZq (Rq.BasePoly.BigCf.BCA.big predT F r) (eq - ep)
  =
  Rq.BasePoly.BigCf.BCA.big predT ((fun (z : Zq) => upscaleZq z (eq - ep)) \o F) r.
proof.
elim: r => [| @/(\o) x l ih]. 
+ by rewrite !Rq.BasePoly.BigCf.BCA.big_nil upscaleZq0.
+ by rewrite !Rq.BasePoly.BigCf.BCA.big_consT upscaleZq_eqep_DM; congr.
qed.

lemma scaleZp2Zq_DM_big_BPCf (F : int -> Zp) (r: int list) :
  scaleZp2Zq (Rp.BasePoly.BigCf.BCA.big predT F r)
  =
  Rq.BasePoly.BigCf.BCA.big predT (scaleZp2Zq \o F) r.
proof.
elim: r => [| @/(\o) x l ih]. 
+ by rewrite Rp.BasePoly.BigCf.BCA.big_nil Rq.BasePoly.BigCf.BCA.big_nil scaleZp2Zq0.
+ rewrite Rp.BasePoly.BigCf.BCA.big_consT Rq.BasePoly.BigCf.BCA.big_consT /=.
  by rewrite scaleZp2Zq_DM; congr.
qed.

lemma scaleZp2Zppq2Z2t_comp (z : Zp) :
      scaleZp2Z2t z = scaleZppq2Z2t (scaleZp2Zppq z).
proof.
rewrite /scaleZp2Z2t /scaleZppq2Z2t /scaleZp2Zppq !inzmodK -eq_inzmod; do 2! congr.
rewrite -eq_22epeq_ppq pmod_small 2:&(downscale_comp);
        last 4 smt(Zp.ge0_asint ge0_et sec_assumption_exp geep1_eq).
rewrite /downscale /shr ltz_divLR 1:expr_gt0 // -exprD_nneg; 
        smt(divz_ge0 expr_gt0 Zp.ge0_asint Zp.gtp_asint geeq1_2ep geep1_eq).
qed.

lemma scaleZp2Zq2Z2_comp (z : Zp) : scaleZp2Z2 z = scaleZq2Z2 (scaleZp2Zq z).
proof.
rewrite /scaleZq2Z2 /scaleZp2Zq /scaleZp2Z2 /downscale /upscale /shr /shl -eq_inzmod !inzmodK /p /q.
rewrite modz_pow2_div 1:?(mulr_ge0, ge0_asint, expr_ge0); 1, 2: smt(geep1_eq ge3_eq).
have ->: 2 ^ (eq - 1) = 2 ^ (ep - 1) * 2 ^ (eq - ep).
+ by rewrite -exprD_nneg; 1, 2: smt(ge2_ep geep1_eq); congr; ring.
by rewrite divzMpr 1:expr_gt0 2:opprD 2:addrA //= expr1 modz_mod.
qed.

lemma scaleZp2Zq2Z2t_comp (z : Zp) : scaleZp2Z2t z = scaleZq2Z2t (scaleZp2Zq z).
proof.
rewrite /scaleZq2Z2t /scaleZp2Zq /scaleZp2Z2t /downscale /upscale /shr /shl -eq_inzmod !inzmodK /p /q.
rewrite modz_pow2_div 1:?(mulr_ge0, ge0_asint, expr_ge0); 1, 2: smt(ge0_et geet2_ep geep1_eq).
rewrite /t -{2 7}(IntID.expr1 2) -exprD_nneg 3:modz_dvd_pow; first 3 smt(ge0_et).
do 2! congr; have ->: 2 ^ (eq - (et + 1)) = 2 ^ (ep - (et + 1)) * 2 ^ (eq - ep).
+ rewrite -exprD_nneg; 1, 2: smt(geet2_ep geep1_eq); congr; ring.
by rewrite divzMpr 1:expr_gt0.
qed.

lemma scaleZ22Zp2Zq_comp (z : Z2) : scaleZ22Zq z = scaleZp2Zq (scaleZ22Zp z).
proof.
rewrite -eq_inzmod !inzmodK /p /q (pmod_small _ (2 ^ ep)); last first.
+ by rewrite (upscale_comp_comm _ eq 1 ep); smt(ge2_ep geep1_eq).
+ rewrite /upscale /shl; split => [| ?]; first by rewrite mulr_ge0 1:ge0_asint expr_ge0.
  rewrite -ltz_divRL 1:expr_gt0 // 1:dvdz_exp2l; first smt(ge2_ep).
  have -> //=: 2 ^ ep = 2 * 2 ^ (ep - 1).
  - by rewrite -{2}expr1 -exprD_nneg; 1, 2: smt(ge2_ep); congr; ring.
  by rewrite mulzK 1:neq_ltz 1:expr_gt0 3:Z2.gtp_asint.
qed.

lemma scaleZ2t2Zp2Zq_comp (z : Z2t) : scaleZ2t2Zq z = scaleZp2Zq (scaleZ2t2Zp z).
proof.
rewrite -eq_inzmod !inzmodK /p /q (pmod_small _ (2 ^ ep)); last first.
+ by rewrite (upscale_comp_comm _ eq (et + 1) ep); smt(geet2_ep geep1_eq).
+ rewrite /upscale /shl; split => [| ?]; first by rewrite mulr_ge0 1:ge0_asint expr_ge0.
  rewrite -ltz_divRL 1:expr_gt0 // 1:dvdz_exp2l; first smt(geet2_ep ge0_et).
  have -> //=: 2 ^ ep = 2 ^ (et + 1) * 2 ^ (ep - (et + 1)).
  - by rewrite -exprD_nneg; 1, 2: smt(ge0_et geet2_ep); congr; ring.
  rewrite mulzK 1:neq_ltz 1:expr_gt0 3:exprD_nneg 5:2?(expr1, mulzC) 5:-/t; smt(ge0_et Z2t.gtp_asint).
qed.

lemma scaleZ22Zq_scaleZq2Z2_inv (z : Z2) : scaleZq2Z2 (scaleZ22Zq z) = z.
proof. 
rewrite /scaleZq2Z2 /scaleZ22Zq /downscale /upscale /shr /shl inzmodK /q modz_pow2_div;
        1, 2: smt(mulr_ge0 expr_ge0 Z2.ge0_asint ge3_eq).
by rewrite mulzK 2:opprD 2:addzA /= 2:expr1 2:-inzmodK 2:!asintK // neq_ltz; right; rewrite expr_gt0.
qed.

lemma scaleZq2Z2_DM_invl (z1 : Z2) (z2 : Zq) : 
  scaleZq2Z2 (scaleZ22Zq z1 + z2) = z1 + scaleZq2Z2 z2.
proof. 
rewrite scaleZq2Z2_DM 2:scaleZ22Zq_scaleZq2Z2_inv //; left.
rewrite /scaleZ22Zq /upscale /shl inzmodK pmod_small 2:dvdz_mull 2:dvdzz.
move: (Z2_asint_values z1); case => -> /= @/q.
+ by rewrite expr_gt0.
+ by rewrite expr_ge0 //= ltz_weexpn2l; smt(ge3_eq).
qed.

lemma eq_scaleZq2Zp_scaleroundZq2Zp (z : Zq) :
  scaleZq2Zp (z + Zq.inzmod (2 ^ (eq - ep - 1))) = scaleroundZq2Zp z.
proof.
rewrite /scaleZq2Zp /scaleroundZq2Zp /downscale /downscaleround /shr.
rewrite round_div_pow2; first smt(subr_ge0 geep1_eq). 
rewrite addE inzmodK modzDmr /q /inzmod; congr.
rewrite (modz_pow2_div _ _ (asint z + 2 ^ (eq - ep -1))). 
+ by rewrite addr_ge0 1:ge0_asint expr_ge0. 
+ by smt(geep1_eq ge2_ep).
by rewrite (: (eq - (eq - ep)) = ep) 1:/# -/p modz_mod. 
qed.

(* Polynomial Scaling *)
lemma scaleRq2Rp0 : scaleRq2Rp Rq.zeroXnD1 = Rp.zeroXnD1.
proof. by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= !rcoeff0 scaleZq2Zp0. qed.

lemma scaleRp2Rq0 : scaleRp2Rq Rp.zeroXnD1 = Rq.zeroXnD1.
proof. by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= !rcoeff0 scaleZp2Zq0. qed.

lemma scaleroundRq2Rp0 : scaleroundRq2Rp Rq.zeroXnD1 = Rp.zeroXnD1.
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= !rcoeff0 scaleroundZq2Zp0. 
qed.

lemma upscaleRq0 (ez : int) : upscaleRq Rq.zeroXnD1 ez = Rq.zeroXnD1.
proof. by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= !rcoeff0 upscaleZq0. qed.

lemma upscaleRq_eqep_small (x : Rq) : 
  (forall (i : int), 0 <= i < n => asint x.[i] < p) => 
  upscaleRq x (eq - ep) = scaleRp2Rq (Rq2Rp x).
proof.
move => val_coeff. 
rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //= rcoeffZ_sum //=.
by move: (val_coeff i rng_i); apply upscaleZq_eqep_small.
qed.

lemma upscaleRqE (p : Rq) (ex : int) (i : int) : (upscaleRq p ex).[i] = upscaleZq p.[i] ex.
proof.
case (i < 0) => [lt0_i | /lezNgt ge0_i]; 1: by rewrite !lt0_rcoeff 3:upscaleZq0.
case (i < n) => [ltn_i | /lezNgt gen_i]; last by rewrite !gered_rcoeff 3:upscaleZq0.
by rewrite rcoeffZ_sum //.
qed.

lemma scaleRq2RpE (p : Rq) (i : int) : (scaleRq2Rp p).[i] = scaleZq2Zp p.[i].
proof.
case (i < 0) => [lt0_i | /lezNgt ge0_i]; 1: by rewrite !lt0_rcoeff 3:scaleZq2Zp0.
case (i < n) => [ltn_i | /lezNgt gen_i]; last by rewrite !gered_rcoeff 3:scaleZq2Zp0.
by rewrite rcoeffZ_sum //.
qed.

lemma scaleR22Rp_varE (p : R2) (ex : int) (i : int) : 
  (scaleR22Rp_var p ex).[i] = (scaleZ22Zp_var p.[i] ex).
proof.
case (i < 0) => [lt0_i | /lezNgt ge0_i]; 1: by rewrite !lt0_rcoeff 3:scaleZ22Zp_var0.
case (i < n) => [ltn_i | /lezNgt gen_i]; last by rewrite !gered_rcoeff 3:scaleZ22Zp_var0.
by rewrite rcoeffZ_sum //.
qed.

lemma scaleR22RpE (p : R2) (i : int) : (scaleR22Rp p).[i] = scaleZ22Zp p.[i].
proof.
case (i < 0) => [lt0_i | /lezNgt ge0_i]; 1: by rewrite !lt0_rcoeff 3:scaleZ22Zp0.
case (i < n) => [ltn_i | /lezNgt gen_i]; last by rewrite !gered_rcoeff 3:scaleZ22Zp0.
by rewrite rcoeffZ_sum //.
qed.

lemma scaleR22RqE (p : R2) (i : int) : (scaleR22Rq p).[i] = scaleZ22Zq p.[i].
proof.
case (i < 0) => [lt0_i | /lezNgt ge0_i]; 1: by rewrite !lt0_rcoeff 3:scaleZ22Zq0.
case (i < n) => [ltn_i | /lezNgt gen_i]; last by rewrite !gered_rcoeff 3:scaleZ22Zq0.
by rewrite rcoeffZ_sum //.
qed.

lemma scaleRp2RqE (p : Rp) (i : int) : (scaleRp2Rq p).[i] = scaleZp2Zq p.[i].
proof.
case (i < 0) => [lt0_i | /lezNgt ge0_i]; 1: by rewrite !lt0_rcoeff 3:scaleZp2Zq0.
case (i < n) => [ltn_i | /lezNgt gen_i]; last by rewrite !gered_rcoeff 3:scaleZp2Zq0.
rewrite /scaleRp2Rq rcoeffZ_sum //=. 
qed.

lemma scaleRq2R2t_DM (p1 p2 : Rq) : 
  ((forall (i : int), 0 <= i < n =>  2 ^ (eq - (et + 1)) %| Zq.asint p1.[i]) \/  
  (forall (i : int), 0 <= i < n =>  2 ^ (eq - (et + 1)) %| Zq.asint p2.[i])) =>
  scaleRq2R2t (p1 + p2) = scaleRq2R2t p1 + scaleRq2R2t p2.
proof.
case => [divz1 | divz2]; rewrite /scaleRq2R2t eq_sym -BigR2t.XnD1CA.big_split /=;
    rewrite !BigR2t.XnD1CA.big_seq &(BigR2t.XnD1CA.eq_bigr) /= => i /mem_range rng_i;
    rewrite -scaleDl eq_sym rcoeffD scaleZq2Z2t_DM ?(divz1, divz2) //.
qed.

lemma upscaleRq_eqep_DM (p1 p2 : Rq) :
  upscaleRq (p1 + p2) (eq - ep) = upscaleRq p1 (eq - ep) + upscaleRq p2 (eq - ep).
proof.
rewrite -BigRq.XnD1CA.big_split /= polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= rcoeffD. 
have ->:
  (fun (i0 : int) => 
   upscaleZq p1.[i0] (eq - ep) ** exp Rq.iX i0 + upscaleZq p2.[i0] (eq - ep) ** exp Rq.iX i0)
  =
  (fun (i0 : int) => 
   (upscaleZq p1.[i0] (eq - ep) + upscaleZq p2.[i0] (eq - ep)) ** exp Rq.iX i0).
+ by rewrite fun_ext /(==) => x; rewrite scaleDl.
by rewrite rcoeffZ_sum //= upscaleZq_eqep_DM.
qed.

lemma scaleRp2R2t_DM (p1 p2 : Rp) : 
  ((forall (i : int), 0 <= i < n =>  2 ^ (ep - (et + 1)) %| Zp.asint p1.[i]) \/  
  (forall (i : int), 0 <= i < n =>  2 ^ (ep - (et + 1)) %| Zp.asint p2.[i])) =>
  scaleRp2R2t (p1 + p2) = scaleRp2R2t p1 + scaleRp2R2t p2.
proof.
case => [divz1 | divz2]; rewrite /scaleRp2R2t eq_sym -BigR2t.XnD1CA.big_split /=;
    rewrite !BigR2t.XnD1CA.big_seq &(BigR2t.XnD1CA.eq_bigr) /= => i /mem_range rng_i;
    rewrite -scaleDl eq_sym rcoeffD scaleZp2Z2t_DM ?(divz1, divz2) //.
qed.

lemma scaleRp2Rq_DM (p1 p2 : Rp) : scaleRp2Rq (p1 + p2) = scaleRp2Rq p1 + scaleRp2Rq p2.
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffD !scaleRp2RqE rcoeffD scaleZp2Zq_DM.
qed.

lemma scaleR22Rq_PN (p : R2) : scaleR22Rq p = scaleR22Rq (- p).
proof.
rewrite /scaleR22Rq !BigRq.XnD1CA.big_seq &(BigRq.XnD1CA.eq_bigr) /= => *.
by rewrite -rcoeffN scaleZ22Zq_PN.
qed.

lemma scaleR2t2Rp_N (p : R2t) : scaleR2t2Rp (- p) = - scaleR2t2Rp p.
proof.
rewrite /scaleR2t2Rp Rp.polyXnD1_sumN /= !BigRp.XnD1CA.big_seq &(BigRp.XnD1CA.eq_bigr) /= => *.
by rewrite -rcoeffN scaleZ2t2Zp_N scaleN.
qed.

lemma scaleR2t2Rq_N (p : R2t) : scaleR2t2Rq (- p) = - scaleR2t2Rq p.
proof.
rewrite /scaleR2t2Rq Rq.polyXnD1_sumN /= !BigRq.XnD1CA.big_seq &(BigRq.XnD1CA.eq_bigr) /= => *.
by rewrite -rcoeffN scaleZ2t2Zq_N scaleN.
qed.

lemma scaleR22Rq_N (p : R2) : scaleR22Rq (- p) = - scaleR22Rq p.
proof.
rewrite /scaleR22Rq Rq.polyXnD1_sumN /= !BigRq.XnD1CA.big_seq &(BigRq.XnD1CA.eq_bigr) /= => *.
by rewrite -rcoeffN scaleZ22Zq_N scaleN.
qed.

lemma scaleRp2Rq_N (p : Rp): scaleRp2Rq (- p) = - scaleRp2Rq p.
proof.
rewrite /scaleRp2Rq Rq.polyXnD1_sumN /= !BigRq.XnD1CA.big_seq &(BigRq.XnD1CA.eq_bigr) /= => *. 
by rewrite -rcoeffN scaleZp2Zq_N -scaleN.
qed.

lemma scaleRp2Rq_BM (p1 p2 : Rp) : scaleRp2Rq (p1 - p2) = scaleRp2Rq p1 - scaleRp2Rq p2.
proof. by rewrite scaleRp2Rq_DM -Rq.ComRing.addrC scaleRp2Rq_N Rq.ComRing.addrC. qed.

lemma upscaleRq_eqep_MAl (p1 p2 : Rq) :
  upscaleRq (p1 * p2) (eq - ep) = upscaleRq p1 (eq - ep) * p2.
proof.
rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= !rcoeffM // upscaleZq_eqep_DM_big_BPCf /(\o).
rewrite !Rq.BasePoly.BigCf.BCA.big_seq &(Rq.BasePoly.BigCf.BCA.eq_bigr) /= => j /mem_range rng_j.
by rewrite upscaleZq_eqep_BM !upscaleZq_eqep_MAl upscaleRqE.
qed.

lemma scaleRp2Rq_MA (p1 p2 : Rp) : scaleRp2Rq (p1 * p2) = scaleRp2Rq p1 * Rp2Rq p2.
proof.
rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= !rcoeffM // scaleZp2Zq_DM_big_BPCf /(\o). 
rewrite !Rq.BasePoly.BigCf.BCA.big_seq &(Rq.BasePoly.BigCf.BCA.eq_bigr) /= => j /mem_range rng_j.
by rewrite scaleZp2Zq_BM !scaleZp2Zq_MA -scaleRp2RqE -!Rp2RqE.
qed.

lemma upscaleRq_eqep_DM_big_Mat (F : int -> Rq) (r : int list) :
  upscaleRq (Mat_Rq.Big.BAdd.big predT F r) (eq - ep)
  =
  Mat_Rq.Big.BAdd.big predT ((fun (p : Rq) => upscaleRq p (eq - ep)) \o F) r.
proof.
elim: r => [| @/(\o) x l ih].
+ by rewrite !Mat_Rq.Big.BAdd.big_nil upscaleRq0.
+ by rewrite !Mat_Rq.Big.BAdd.big_consT /= upscaleRq_eqep_DM; congr.
qed.

lemma scaleRp2Rq_DM_big_Mat (F : int -> Rp) (r : int list) :
  scaleRp2Rq (Mat_Rp.Big.BAdd.big predT F r)
  =
  Mat_Rq.Big.BAdd.big predT (scaleRp2Rq \o F) r.
proof.
elim: r => [| @/(\o) x l ih].
+ by rewrite Mat_Rp.Big.BAdd.big_nil Mat_Rq.Big.BAdd.big_nil scaleRp2Rq0.
+ rewrite Mat_Rp.Big.BAdd.big_consT Mat_Rq.Big.BAdd.big_consT /=.
  by rewrite scaleRp2Rq_DM; congr.
qed.

lemma scaleRp2Rq_DM_big_XnD1 (F : int -> Rp) (r : int list) :
  scaleRp2Rq (BigRp.XnD1CA.big predT F r)
  =
  BigRq.XnD1CA.big predT (scaleRp2Rq \o F) r.
proof.
elim: r => [| @/(\o) x l ih].
+ by rewrite BigRp.XnD1CA.big_nil BigRq.XnD1CA.big_nil scaleRp2Rq0.
+ rewrite BigRp.XnD1CA.big_consT BigRq.XnD1CA.big_consT /=.
  by rewrite scaleRp2Rq_DM; congr.
qed.

lemma scaleRp2Rppq2R2t_comp (p : Rp) : scaleRp2R2t p = scaleRppq2R2t (scaleRp2Rppq p).
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //= rcoeffZ_sum //= scaleZp2Zppq2Z2t_comp.
qed.

lemma scaleRp2Rq2R2_comp (p : Rp) : scaleRp2R2 p = scaleRq2R2 (scaleRp2Rq p).
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //= rcoeffZ_sum //= scaleZp2Zq2Z2_comp.
qed.

lemma scaleRp2Rq2R2t_comp (p : Rp) : scaleRp2R2t p = scaleRq2R2t (scaleRp2Rq p).
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //= rcoeffZ_sum //= scaleZp2Zq2Z2t_comp.
qed.

lemma scaleR2t2Rp2Rq_comp (p : R2t) : scaleR2t2Rq p = scaleRp2Rq (scaleR2t2Rp p).
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //= rcoeffZ_sum //= scaleZ2t2Zp2Zq_comp.
qed.

lemma scaleR22Rp2Rq_comp (p : R2) : scaleR22Rq p = scaleRp2Rq (scaleR22Rp p).
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //= rcoeffZ_sum //= scaleZ22Zp2Zq_comp.
qed.

lemma scaleR22Rq_scaleRq2R2_inv (p : R2) : scaleRq2R2 (scaleR22Rq p) = p.
proof. 
by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= rcoeffZ_sum //= scaleZ22Zq_scaleZq2Z2_inv.
qed.

lemma scaleRq2R2_DM_invl (p1 : R2) (p2 : Rq) : 
  scaleRq2R2 (scaleR22Rq p1 + p2) = p1 + scaleRq2R2 p2.
proof.
rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffZ_sum //= 2!rcoeffD. 
by rewrite rcoeffZ_sum //= rcoeffZ_sum //=  scaleZq2Z2_DM_invl.
qed.

lemma eq_scaleRq2Rp_scaleroundRq2Rp (p : Rq) :
  scaleRq2Rp (p + h1) = scaleroundRq2Rp p.
proof.
rewrite polyXnD1_eqP => i rng_i. 
by rewrite ?rcoeffZ_sum //= rcoeffD /h1 rcoeffZ_sum //= eq_scaleZq2Zp_scaleroundZq2Zp.
qed.

(* Polynomial Vector Scaling *)
lemma scaleRpv2RqvE (pv : Rp_vec) (i : int) : (scaleRpv2Rqv pv).[i] = scaleRp2Rq pv.[i].
proof.
rewrite /scaleRpv2Rqv /Mat_Rq.Vector."_.[_]" offunvK /vclamp.
by case (0 <= i && i < l) => // rng_i; rewrite getv_out // scaleRp2Rq0.
qed.

lemma eq_scaleRqv2Rpv_scaleroundRqv2Rpv (pv : Rq_vec) :
  scaleRqv2Rpv (pv + h) = scaleroundRqv2Rpv pv.
proof.
rewrite /scaleRqv2Rpv /scaleroundRqv2Rpv; congr.
rewrite fun_ext /(==) => i; rewrite offunD /h.
case (0 <= i < l) => rng_i.
+ by rewrite offunCE // eq_scaleRq2Rp_scaleroundRq2Rp.
+ by rewrite ?getv_out // addr0 scaleroundRq2Rp0 scaleRq2Rp0.
qed.

(* Remaining Dependent Scaling Properties *)
lemma upscaleRq_eqep_DotDll (a : Rp_vec) (b : Rq_vec) : 
  upscaleRq (dotp (Rpv2Rqv a) b) (eq - ep) = dotp (scaleRpv2Rqv a) b.
proof.
rewrite /dotp upscaleRq_eqep_DM_big_Mat.
rewrite !Mat_Rq.Big.BAdd.big_seq &(Mat_Rq.Big.BAdd.eq_bigr) /= /(\o) => i /mem_range rng_i.
rewrite upscaleRq_eqep_MAl; congr; rewrite eq_sym scaleRpv2RqvE polyXnD1_eqP => j rng_j.
rewrite !rcoeffZ_sum //= Rpv2RqvE Rp2RqE /scaleZp2Zq /upscaleZq /Zp2Zq !inzmodK -eq_inzmod /upscale.
do 3! congr; rewrite //= pmod_small // ge0_asint /= (ltz_trans p) ?gtp_asint ltz_weexpn2l;
                     smt(ge2_ep geet2_ep geep1_eq).
qed.

(* - Specific to Security Proof - *)
lemma Rq2Rp_DG23 (b : Rq_vec) (s : Rq_vec) : 
       Rq2Rp (dotp b s + h1) = dotp (Rqv2Rpv b) (Rqv2Rpv s) + Rq2Rp h1.
proof. by rewrite (Rq2Rp_DM (dotp b s) h1) Rq2Rp_DotDl. qed.

lemma eq_comp23_Zq (z : Zq) (m : Z2) :
      Zp2Zppq ((scaleZq2Zp z) + (scaleZ22Zp_var m (2 * ep - eq - 1)))
      =
      scaleZp2Zppq ((Zq2Zp z) + (scaleZ22Zp m)).
proof.
rewrite /Zp2Zppq /Zq2Zp /scaleZq2Zp /scaleZp2Zppq /scaleZ22Zp /scaleZ22Zp_var 
        /downscale /upscale /shr /shl. 
rewrite !Zp.inzmodK !modzDm {2}(mulzC 2) -(intmulz ep) mulr2z !opprD !addzA /= (addzC _ eq).
rewrite -eq_inzmod /p -eq_22epeq_ppq modz_dvd_pow; 1: smt(geeq1_2ep geep1_eq).
rewrite modz_pow2_div 1:addr_ge0 2:mulr_ge0 3:expr_ge0 ?ge0_asint //; first smt(geep1_eq geeq1_2ep).
rewrite eq_sym modz_dvd_pow; 1:smt(geeq1_2ep geep1_eq); do 2! congr.
rewrite divzDr; first case: (Z2.asint m = 0) => [-> /= | /neq_ltz]; first by apply dvdz0. 
+ case; first by rewrite ltzNge Z2.ge0_asint.
  move: (Z2.gtp_asint m); rewrite -2!lez_add1r -(ler_add2l (-1)) /= => le1_m ge1_m. 
  have -> /=: Z2.asint m = 1 by rewrite (eqz_leq (Z2.asint m) 1).
  by rewrite dvdz_exp2l; smt(geep1_eq geeq1_2ep).
have ->: 2 ^ (ep - 1) = 2 ^ (2 * ep - eq - 1) * 2 ^ (eq - ep).
+ by rewrite -exprD_nneg; 1, 2: smt(geeq1_2ep geep1_eq); congr; ring.
by rewrite -mulzA mulzK 1:ltr0_neq0 1:expr_gt0.
qed.

lemma eq_comp23 (p : Rq) (m : R2) :
      Rp2Rppq ((scaleRq2Rp p) + (scaleR22Rp_var m (2 * ep - eq - 1)))
      =
      scaleRp2Rppq ((Rq2Rp p) + (scaleR22Rp m)).
proof.
rewrite polyXnD1_eqP => i rng_i; rewrite !rcoeffZ_sum //=.
by rewrite 2!rcoeffD scaleRq2RpE scaleR22Rp_varE Rq2RpE scaleR22RpE eq_comp23_Zq.
qed.

(* - Specific to Equivalence Between Descriptions of PKE - *)
lemma eq_scaleZp2ZqZq2Zp_upscaleZq (z : Zq) : scaleZp2Zq (Zq2Zp z) = upscaleZq z (eq - ep).
proof.
rewrite /scaleZp2Zq /Zq2Zp /upscaleZq /upscale /shl /= -eq_inzmod inzmodK /p /q.
by rewrite modz_pow2_mul; first smt(ge2_ep geep1_eq).
qed.

lemma eq_scaleRp2RqRq2Rp_upscaleRq (p : Rq) : scaleRp2Rq (Rq2Rp p) = upscaleRq p (eq - ep).
proof.
rewrite polyXnD1_eqP => i rng_i.
by rewrite scaleRp2RqE Rq2RpE eq_sym upscaleRqE eq_scaleZp2ZqZq2Zp_upscaleZq.
qed.

lemma eq_scaleRp2R2tRq2Rp_scaleRq2R2tupscaleRq (p : Rq) :
  scaleRp2R2t (Rq2Rp p)
  =
  scaleRq2R2t (upscaleRq p (eq - ep)).
proof. by rewrite -eq_scaleRp2RqRq2Rp_upscaleRq scaleRp2Rq2R2t_comp. qed.

lemma eq_comp_enc_altenc (b : Rp_vec) (s : Rq_vec) (m : R2) : 
  scaleRp2R2t ((dotp b (Rqv2Rpv s)) + Rq2Rp h1 + scaleR22Rp m) 
  =
  scaleRq2R2t ((dotp (scaleRpv2Rqv b) s) + upscaleRq h1 (eq - ep) + scaleR22Rq m).
proof.
rewrite -upscaleRq_eqep_DotDll -upscaleRq_eqep_DM -Rq2Rp_DotDlr -Rq2Rp_DM.
rewrite scaleRq2R2t_DM 2:scaleRp2R2t_DM; first 2 right => i rng_i; 
        rewrite ?(scaleR22RqE, scaleR22RpE) /scaleZ22Zq /scaleZ22Zp; move: (Z2_asint_values m.[i]); 
        case => ->; rewrite ?zeroE ?dvdz0 /upscale /shl /= inzmodK pmod_small ?expr_ge0 /= 
        ?ltz_weexpn2l //= ?dvdz_exp2l; smt(ge0_et ge3_eq ge2_ep geet2_ep geep1_eq).
by congr; [apply eq_scaleRp2R2tRq2Rp_scaleRq2R2tupscaleRq | 
           rewrite scaleR22Rp2Rq_comp scaleRp2Rq2R2t_comp].
qed.

lemma eq_comp_dec_altdec (b' : Rp_vec) (s : Rq_vec) (c : R2t):
  scaleRp2R2 ((dotp b' (Rqv2Rpv s)) + Rq2Rp h1 - scaleR2t2Rp c + Rq2Rp h2)
  =
  scaleRq2R2 ((dotp (scaleRpv2Rqv b') s) + upscaleRq h1 (eq - ep) - scaleR2t2Rq c 
  + upscaleRq h2 (eq - ep)).
proof.
have ->: 
  (dotp b' (Rqv2Rpv s)) + Rq2Rp h1 - scaleR2t2Rp c + Rq2Rp h2
  =
  (dotp b' (Rqv2Rpv s)) + Rq2Rp h1 + Rq2Rp h2 - scaleR2t2Rp c by ring.
have ->:
  (dotp (scaleRpv2Rqv b') s + upscaleRq h1 (eq - ep) - scaleR2t2Rq c) + upscaleRq h2 (eq - ep)
  =
  (dotp (scaleRpv2Rqv b') s + upscaleRq h1 (eq - ep) + upscaleRq h2 (eq - ep) - scaleR2t2Rq c) 
  by ring.
rewrite -upscaleRq_eqep_DotDll -2!upscaleRq_eqep_DM -Rq2Rp_DotDlr -2!Rq2Rp_DM scaleRp2Rq2R2_comp. 
congr; rewrite scaleRp2Rq_DM; congr.
+ by rewrite eq_scaleRp2RqRq2Rp_upscaleRq.
+ by rewrite -scaleR2t2Rp_N -scaleR2t2Rq_N scaleR2t2Rp2Rq_comp.
qed.

(* ------------------------------------------------------------------------------------- *)
(*  Saber's PKE Scheme                                                                   *)
(* ------------------------------------------------------------------------------------- *)

(* --- General --- *)
clone import PKE as Saber_PKE with
  type pkey <- seed * Rp_vec,
  type skey <- Rq_vec,
  type plaintext <- R2,
  type ciphertext <- R2t * Rp_vec.


(* --- Actual --- *)
module Saber_PKE_Scheme : Scheme = {
   proc kg() : (seed * Rp_vec) * Rq_vec = {
      var sd: seed;
      var _A: Rq_mat;
      var s: Rq_vec;
      var b: Rp_vec;
      
      sd <$ dseed;
      _A <- gen sd;
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
      _A <- gen sd;
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

(* --- Actual (Alternative Description) --- *)
module Saber_PKE_Scheme_Alt : Scheme = {
   proc kg() : (seed * Rp_vec) * Rq_vec = {
      var sd: seed;
      var _A: Rq_mat;
      var s: Rq_vec;
      var b: Rp_vec;
      
      sd <$ dseed;
      _A <- gen sd;
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
      _A <- gen sd;
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
lemma eqv_kg: equiv[Saber_PKE_Scheme.kg ~ Saber_PKE_Scheme_Alt.kg : true ==> ={res}].
proof. by proc; auto. qed.

(* - Equivalence of Encryption - *)
lemma eqv_enc: equiv[Saber_PKE_Scheme.enc ~ Saber_PKE_Scheme_Alt.enc : ={pk, m} ==> ={res}].
proof.
proc.
auto => /> *. 
by apply eq_comp_enc_altenc.
qed.

(* - Equivalence of Decryption - *)
lemma eqv_dec: equiv[Saber_PKE_Scheme.dec ~ Saber_PKE_Scheme_Alt.dec : ={sk, c} ==> ={res}].
proof.
proc.
auto => /> ?. 
by apply eq_comp_dec_altdec.
qed.
