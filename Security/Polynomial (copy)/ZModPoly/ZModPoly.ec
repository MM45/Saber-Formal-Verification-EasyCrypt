pragma Goals:printall.

(*
----------------------------------- 
 Require/Import EasyCrypt Theories
-----------------------------------
*)
(* --- Built-in --- *)
require import AllCore List Ring Bigalg StdBigop StdOrder IntDiv ZModP.
require (*--*) Subtype.
(*---*) import Bigint IntID IntOrder.

(*
----------------------------------- 
 ZModRingPoly
-----------------------------------
*)
abstract theory ZModRingPoly.

const p : { int | 2 <= p } as ge2_coeffp.

type coeff.
type poly.

clone import ZModRing as Coeff with
    op p <- p,
    type zmod <- coeff
  proof ge2_p by apply ge2_coeffp.

clone import BigComRing as BigCf with
    type t <- coeff,
    pred CR.unit <- Coeff.unit,
    op CR.zeror <- Coeff.zero,
    op CR.oner <- Coeff.one,
    op CR.( + ) <- Coeff.( + ),
    op CR.([-]) <- Coeff.([-]),
    op CR.( * ) <- Coeff.( * ),
    op CR.invr <- Coeff.inv,
    op CR.intmul <- Coeff.ZModpRing.intmul,
    op CR.ofint <- Coeff.ZModpRing.ofint,
    op CR.exp <- Coeff.ZModpRing.exp
  proof CR.addrA by apply Coeff.ZModpRing.addrA
  proof CR.addrC by apply Coeff.ZModpRing.addrC
  proof CR.add0r by apply Coeff.ZModpRing.add0r
  proof CR.addNr by apply Coeff.ZModpRing.addNr
  proof CR.oner_neq0 by apply Coeff.ZModpRing.oner_neq0
  proof CR.mulrA by apply Coeff.ZModpRing.mulrA
  proof CR.mulrC by apply Coeff.ZModpRing.mulrC
  proof CR.mul1r by apply Coeff.ZModpRing.mul1r
  proof CR.mulrDl by apply Coeff.ZModpRing.mulrDl
  proof CR.mulVr by apply Coeff.ZModpRing.mulVr
  proof CR.unitP by apply Coeff.ZModpRing.unitP
  proof CR.unitout by apply Coeff.ZModpRing.unitout

  rename [theory] "BAdd" as "BCA"
         [theory] "BMul" as "BCM"

  remove abbrev CR.(-)
  remove abbrev CR.(/).

(* ---------------------------------------------------------------------------------------------- *)
type prepoly = int -> coeff.

inductive ispoly (p : prepoly) =
| IsPoly of
      (forall c, c < 0 => p c = zero)
    & (exists d, forall c, (d < c)%Int => p c = zero).

clone include Subtype with 
    type T   <- prepoly,
    type sT  <- poly,
    pred P   <- ispoly,
    op wsT <- (fun _ => zero)
  rename "insub" as "to_poly"
  rename "val"   as "of_poly".

op "_.[_]" (p : poly) (i : int) = (of_poly p) i.

lemma lt0_coeff p c : c < 0 => p.[c] = zero.
proof.
  by move=> lt0_c; rewrite /"_.[_]"; case: (of_polyP p) => /(_ _ lt0_c).
qed.

op deg (p : poly) = argmin idfun (fun i => forall j, (i <= j)%Int => p.[j] = zero).

lemma gedeg_coeff (p : poly) (c : int) : deg p <= c => p.[c] = zero.
proof.
  move=> le_p_c; pose P p i := forall j, (i <= j)%Int => p.[j] = zero.
  case: (of_polyP p) => [wf_p [d hd]]; move: (argminP idfun (P p)).
  move/(_ (max (d+1) 0) _ _) => @/P @/idfun /=; first exact: maxrr.
  - by move=> j le_d_j; apply: hd => /#.
  by apply; apply: le_p_c.
qed.

lemma gedeg_coeff_contra (p : poly) (c : int) : p.[c] <> zero => c < deg p.
proof. move: (gedeg_coeff p c); rewrite lerNgt; apply (contraR (c < deg p) (p.[c] = zero)). qed.

lemma ge0_deg p : 0 <= deg p.
proof. rewrite /deg &(ge0_argmin). qed.

op prepolyC  (c   : coeff) = fun i => if i = 0 then c else zero.
op prepolyXn (k   : int  ) = fun i => if 0 <= k /\ i = k then one else zero.
op prepolyD  (p q : poly ) = fun i => p.[i] + q.[i].
op prepolyN  (p   : poly ) = fun i => - p.[i].

op prepolyM (p q : poly) = fun k =>
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (k+1).

op prepolyZ (z : coeff) (p : poly) = fun k =>
  z * p.[k].

lemma ispolyC (c : coeff) : ispoly (prepolyC c).
proof.
  split=> @/prepolyC [c' ?|]; first by rewrite ltr_eqF.
  by exists 0 => c' gt1_c'; rewrite gtr_eqF.
qed.

lemma ispolyXn (k : int) : ispoly (prepolyXn k).
proof.
  split=> @/prepolyXn [c lt0_c|].
  + by case: (0 <= k) => //= ge0_k; rewrite ltr_eqF //#.
  + by exists k => c gt1_c; rewrite gtr_eqF.
qed.

lemma ispolyN (p : poly) : ispoly (prepolyN p).
proof.
  split=> @/prepolyN [c lt0_c|]; first by rewrite ZModpRing.oppr_eq0 lt0_coeff.
  by exists (deg p) => c => /ltrW /gedeg_coeff ->; rewrite ZModpRing.oppr0.
qed.

lemma ispolyD (p q : poly) : ispoly (prepolyD p q).
proof.
  split=> @/prepolyD [c lt0_c|]; first by rewrite !lt0_coeff // ZModpRing.addr0.
  by exists (1 + max (deg p) (deg q)) => c le; rewrite !gedeg_coeff ?ZModpRing.addr0 //#.
qed.

lemma ispolyM (p q : poly) : ispoly (prepolyM p q).
proof.
  split => @/prepolyM [c lt0_c|]; 1: by rewrite BCA.big_geq //#.
  exists (deg p + deg q + 1) => c ltc; rewrite BCA.big_seq BCA.big1 //= => i.
  rewrite mem_range => -[gt0_i lt_ic]; rewrite /( * ) /zero -eq_inzmod mod0z.
  have ->: asint p.[i] * asint q.[c - i] = 0; first rewrite mulf_eq0.
  case: (p.[i] = zero); first rewrite -asint_eq inzmodK mod0z.
   by move=> eq_0p; left; apply eq_0p.
   move=> neq_0p; right. 
    have gti_dp: i < deg p.
     by move: neq_0p; apply gedeg_coeff_contra. 
    rewrite -zeroE asint_eq; apply /gedeg_coeff /ltzW /(ltz_trans (deg q + 1)); first by rewrite ltz_addl.
     rewrite (ler_lt_trans (deg p + deg q + 1 - i)); last by rewrite (ltz_add2r (-i)).
      rewrite addzAC -addzA addzAC addzA -addzA -addzC (lez_addr _ (deg p - i)) -(lez_add2r i) -addzA /=.
      by apply ltzW in gti_dp.
    by apply mod0z.
qed.

lemma ispolyZ z p : ispoly (prepolyZ z p).
proof.  
  split => @/prepolyZ [c lt0_c|]; [| exists (deg p + 1) => c gtc]; rewrite /( * ) -eq_inzmod mod0z;
           have ->: asint z * asint p.[c] = 0; [| by apply mod0z | | by apply mod0z];
           rewrite mulf_eq0 -zeroE (asint_eq (p.[c])); right; 
           [by apply lt0_coeff | apply gedeg_coeff].
  by apply ltzW in gtc; apply /(ler_trans (deg p + 1)) /gtc; rewrite lez_addl.  
qed.

lemma poly_eqP (p q : poly) : p = q <=> (forall c, 0 <= c => p.[c] = q.[c]).
proof.
  split=> [->//|eq_coeff]; apply/of_poly_inj/fun_ext => c.
  case: (c < 0) => [lt0_c|/lerNgt /=]; last by apply: eq_coeff.
  by rewrite -/"_.[_]" !lt0_coeff.
qed.

op polyC  c   = to_polyd (prepolyC  c).
op polyXn k   = to_polyd (prepolyXn k).
op polyN  p   = to_polyd (prepolyN  p).
op polyD  p q = to_polyd (prepolyD  p q).
op polyM  p q = to_polyd (prepolyM p q).
op polyZ  z p = to_polyd (prepolyZ z p).

abbrev poly0  = polyC  zero.
abbrev poly1  = polyC  one.
abbrev polyX  = polyXn 1.
abbrev X      = polyXn 1.
abbrev ( + )  = polyD.
abbrev [ - ]  = polyN.
abbrev ( - )  = fun p q => p + (-q).
abbrev ( * )  = polyM.
abbrev ( ** ) = polyZ.

(* -------------------------------------------------------------------- *)
lemma coeffE p k : ispoly p => (to_polyd p).[k] = p k.
proof. by move=> ?; rewrite /"_.[_]" to_polydK. qed.

lemma polyCE c k : (polyC c).[k] = if k = 0 then c else zero.
proof. by rewrite coeffE 1:ispolyC. qed.

lemma poly0E k : poly0.[k] = zero.
proof. by rewrite polyCE if_same. qed.

lemma polyNE p k : (-p).[k] = - p.[k].
proof. by rewrite coeffE 1:ispolyN. qed.

lemma polyDE p q k : (p + q).[k] = p.[k] + q.[k].
proof. by rewrite coeffE 1:ispolyD. qed.

lemma polyME p q k : (p * q).[k] =
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (k+1).
proof. by rewrite coeffE 1:ispolyM. qed.

lemma polyZE z p k : (z ** p).[k] = z * p.[k].
proof. by rewrite coeffE 1:ispolyZ. qed.

hint rewrite coeffpE : poly0E polyDE polyNE polyME polyZE.

(* -------------------------------------------------------------------- *)
lemma degP p c :
     0 < c
  => p.[c-1] <> zero
  => (forall i, c <= i => p.[i] = zero)
  => deg p = c.
proof.
  move=> ge0_c nz_p_cB1 degc @/deg; apply: argmin_eq => @/idfun /=.
  - by apply/ltrW. - by apply: degc.
  move=> j [ge0_j lt_jc]; rewrite negb_forall /=.
  by exists (c-1); apply/negP => /(_ _); first by move=> /#.
qed.

(* -------------------------------------------------------------------- *)
lemma degC c : deg (polyC c) = if c = zero then 0 else 1.
proof.
  case: (c = zero) => [->|nz_c]; last first.
  - apply: degP => //=; first by rewrite polyCE.
   by move=> i ge1_i; rewrite polyCE gtr_eqF //#.
  rewrite /deg; apply: argmin_eq => @/idfun //=.
  - by move=> j _; rewrite poly0E.
  - by move=> j; apply: contraL => _ /#.
qed.

lemma degC_le c : deg (polyC c) <= 1.
proof. by rewrite degC; case: (c = zero). qed.

lemma deg0 : deg poly0 = 0.
proof. by rewrite degC. qed.

lemma deg1 : deg poly1 = 1.
proof.
  apply: degP => //=; first by rewrite polyCE /= ZModpRing.oner_neq0.
  by move=> c ge1_c; rewrite polyCE gtr_eqF //#.
qed.

lemma deg_eq0 p : (deg p = 0) <=> (p = poly0).
proof.
  split=> [z_degp|->]; last by rewrite deg0.
  apply/poly_eqP=> c ge0_c; rewrite poly0E.
  by apply/gedeg_coeff; rewrite z_degp.
qed.

lemma deg_eq1 p : (deg p = 1) <=> (exists c, c <> zero /\ p = polyC c).
proof.
  split=> [eq1_degp|[c [nz_c ->>]]]; last first.
  + by apply: degP => //= => [|i ge1_i]; rewrite polyCE //= gtr_eqF /#.
  have pC: forall i, 1 <= i => p.[i] = zero.
  + by move=> i ge1_i; apply: gedeg_coeff; rewrite eq1_degp.
  exists p.[0]; split; last first.
  + apply/poly_eqP => c /ler_eqVlt -[<<-|]; first by rewrite polyCE.
    by move=> gt0_c; rewrite polyCE gtr_eqF //= &(pC) /#.
  apply: contraL eq1_degp => z_p0; suff ->: p = poly0 by rewrite deg0.
  apply/poly_eqP=> c; rewrite poly0E => /ler_eqVlt [<<-//|].
  by move=> gt0_c; apply: pC => /#.
qed.

lemma coeff_degB1_neq0 p : p <> poly0 => p.[deg p - 1] <> zero.
proof.
  rewrite -deg_eq0 eqr_le ge0_deg /= -ltrNge => gt0_deg.
  pose P i := forall j, (i <= j)%Int => p.[j] = zero.
  apply/negP => zp; have := argmin_min idfun P (deg p - 1) _; 1: smt().
  move=> @/idfun /= j /ler_eqVlt [<<-//| ltj].
  by apply: gedeg_coeff => /#.
qed.

(* -------------------------------------------------------------------- *)
clone import Ring.ZModule as ZPoly with
    type t <- poly,
    op zeror <- poly0,
    op (+) <- polyD,
    op [-] <- polyN
  proof *.

  realize addrA.
  proof. by move=> p q r; apply/poly_eqP=> c; rewrite !coeffpE ZModpRing.addrA. qed.

  realize addrC.
  proof. by move=> p q; apply/poly_eqP=> c; rewrite !coeffpE ZModpRing.addrC. qed.

  realize add0r.
  proof. by move=> p; apply/poly_eqP => c; rewrite !coeffpE ZModpRing.add0r. qed.

  realize addNr.
  proof. by move=> p; apply/poly_eqP => c; rewrite !coeffpE ZModpRing.addNr. qed.

lemma polyMEw M p q k : (k <= M)%Int => (p * q).[k] =
  BCA.bigi predT (fun i => p.[i] * q.[k-i]) 0 (M+1).
proof. 
  move=> le_kM; case: (k < 0) => [lt0_k|/lerNgt ge0_k].
  + rewrite lt0_coeff // BCA.big_seq BCA.big1 //= => i.
    case/mem_range=> [ge0_i lt_iM]; rewrite /( * ) -eq_inzmod mod0z.
    have ->: asint p.[i] * asint q.[k - i] = 0; [rewrite mulf_eq0 -zeroE; right | by apply mod0z].
     rewrite (asint_eq q.[k - i]) lt0_coeff //.
     by apply /(ler_lt_trans k) /lt0_k /(lez_add2r i); rewrite -addzA /= (lez_addl k).
  rewrite (@BCA.big_cat_int (k+1)) 1,2:/# -polyME.
  rewrite BCA.big_seq BCA.big1 2:ZModpRing.addr0 //= => i /mem_range.
  case=> [lt_ki lt_iM]; rewrite /( * ) -eq_inzmod mod0z.
    have ->: asint p.[i] * asint q.[k - i] = 0; [rewrite mulf_eq0 -zeroE; right | by apply mod0z].
     by rewrite (asint_eq q.[k - i]) lt0_coeff // -(ltz_add2r i) -addzA /= -lez_add1r addzC.
qed.

lemma mulpC : commutative ( * ).
proof.
  move=> p q; apply: poly_eqP => k ge0_k; rewrite !polyME.
  pose F j := k - j; rewrite (@BCA.big_reindex _ _ F F) 1:/#.
  rewrite predT_comp /(\o) /=; pose s := map _ _.
  apply: (eq_trans _ _ _ (BCA.eq_big_perm _ _ _ (range 0 (k+1)) _)).
  + rewrite uniq_perm_eq 2:&(range_uniq) /s.
    * rewrite map_inj_in_uniq 2:&(range_uniq) => x y.
      by rewrite !mem_range /F /#.
    * move=> x; split => [/mapP[y []]|]; 1: by rewrite !mem_range /#.
      rewrite !mem_range => *; apply/mapP; exists (F x).
      by rewrite !mem_range /F /#.
  + by apply: BCA.eq_bigr => /= i _ @/F; rewrite ZModpRing.mulrC /#.
qed.

lemma polyMEwr M p q k : (k <= M)%Int => (p * q).[k] =
  BCA.bigi predT (fun i => p.[k-i] * q.[i]) 0 (M+1).
proof.
  rewrite mulpC => /polyMEw ->; apply: BCA.eq_bigr.
  by move=> i _ /=; rewrite  ZModpRing.mulrC.
qed.

lemma polyMEr p q k : (p * q).[k] =
  BCA.bigi predT (fun i => p.[k-i] * q.[i]) 0 (k+1).
proof. by rewrite (@polyMEwr k). qed.

lemma mulpA : associative ( * ).
proof.
  move=> p q r; apply: poly_eqP => k ge0_k.
  have ->: ((p * q) * r).[k] =
    BCA.bigi predT (fun i =>
      BCA.bigi predT (fun j => p.[j] * q.[k - i - j] * r.[i]) 0 (k+1)) 0 (k+1).
  + rewrite polyMEr !BCA.big_seq &(BCA.eq_bigr) => /= i.
    case/mem_range => ge0_i lt_i_Sk; rewrite (@polyMEw k) 1:/#.
    by rewrite BCA.mulr_suml &(BCA.eq_bigr).
  have ->: (p * (q * r)).[k] =
    BCA.bigi predT (fun i =>
      BCA.bigi predT (fun j => p.[i] * q.[k - i - j] * r.[j]) 0 (k+1)) 0 (k+1).
  + rewrite polyME !BCA.big_seq &(BCA.eq_bigr) => /= i.
    case/mem_range => g0_i lt_i_Sk; rewrite (@polyMEwr k) 1:/#.
    by rewrite BCA.mulr_sumr &(BCA.eq_bigr) => /= j _; rewrite ZModpRing.mulrA.
  rewrite BCA.exchange_big &(BCA.eq_bigr) => /= i _.
  by rewrite &(BCA.eq_bigr) => /= j _ /#.
qed.

lemma mul1p : left_id poly1 polyM.
proof.
  move=> p; apply: poly_eqP => c ge0_c.
  rewrite polyME BCA.big_int_recl //= polyCE /= ZModpRing.mul1r.
  rewrite BCA.big_seq BCA.big1 -1:?addr0 //=; last by rewrite ZModpRing.addr0.
  move=> i; rewrite mem_range=> -[ge0_i _]; rewrite polyCE.
  by rewrite addz1_neq0 //= ZModpRing.mul0r.
qed.

lemma mul0p : left_zero poly0 polyM.
proof.
  move=> p; apply/poly_eqP=> c _; rewrite poly0E polyME.
  by rewrite BCA.big1 //= => i _; rewrite poly0E ZModpRing.mul0r.
qed.

lemma mulpDl: left_distributive polyM polyD.
proof.
  move=> p q r; apply: poly_eqP => c ge0_c; rewrite !(polyME, polyDE).
  by rewrite -BCA.big_split &(BCA.eq_bigr) => /= i _; rewrite polyDE ZModpRing.mulrDl.
qed.

lemma onep_neq0 : poly1 <> poly0.
proof. by apply/negP => /poly_eqP /(_ 0); rewrite !polyCE /= ZModpRing.oner_neq0. qed.

(*
pred nilpotent (a : coeff) = exists (n : int), inzmod (exp (asint a) n) = zero.
pred unitp (p : poly) = Coeff.unit p.[0] /\ forall (i : int), 0 < i => nilpotent p.[i].

op polyV (p : poly) =
  if deg p = 1 then polyC (Coeff.inv p.[0]) else p.

lemma degV (p : poly) : deg (polyV p) = deg p.
proof.
rewrite /polyV; case: (deg p = 1); last done.
by case/deg_eq1=> c [nz_c ->>]; rewrite !degC polyCE /= ZModpRing.invr_eq0.
qed.
*)

clone import Ring.ComRing as PolyRing with
    type t <- poly ,
    op zeror <- poly0,
    op oner <- poly1,
    op ( + ) <- polyD,
    op [ - ] <- polyN,
    op ( * ) <- polyM
  proof addrA     by apply ZPoly.addrA
  proof addrC     by apply ZPoly.addrC
  proof add0r     by apply ZPoly.add0r
  proof addNr     by apply ZPoly.addNr
  proof mulrA     by apply mulpA
  proof mulrC     by apply mulpC
  proof mul1r     by apply mul1p
  proof mulrDl    by apply mulpDl
  proof oner_neq0 by apply onep_neq0.

(*
realize unitout.
proof.

move=> p @/unitp @/polyV; case: (deg p = 1) => //=.
move=> dp_eq1 unitN_p0; apply/poly_eqP => c ge0_c.
case: (c < 1) => [lt1_c|/lerNgt ge1_c]; last first.
- rewrite !(@gedeg_coeff _ c) 2:dp_eq1 //.
  by apply/(ler_trans _ _ _ _ ge1_c)/degC_le.
- suff ->: c = 0; first by rewrite polyCE /= invr_out //; apply /ZModpRing.unitout /unitN_p0.
  by rewrite eqr_le ge0_c /= -ltz1.
qed.


realize mulVr.
proof.
move=> p inv_p; apply/poly_eqP=> c /ler_eqVlt [<<-|].
+ rewrite polyCE /= polyME /= BCA.big_int1 /= /polyV.
  by case: inv_p => -> inv_p0 /=; rewrite polyCE /= ZModpRing.mulVr.
+ move=> gt0_c; rewrite polyME polyCE gtr_eqF //=.
  rewrite BCA.big_seq BCA.big1 //= => i; rewrite mem_range.
  case: inv_p => @/polyV ^ degp -> inv_p0 [+ lt_i_Sc] - /ler_eqVlt [<<-|] /=.
  - by rewrite (gedeg_coeff _ c) -1:ZModpRing.mulr0 // degp /#.
  - move=> gt0_i; rewrite (gedeg_coeff _ i) -1:ZModpRing.mul0r //.
    by apply/(ler_trans _ _ _ (degC_le _)) => /#.
qed.

realize unitP.
proof. admit. qed.
(*
move=> p q ^pMqE /(congr1 deg); rewrite deg1.
move/(congr1 ((+) 1)) => /=; rewrite addrC; move: pMqE.
case: (deg p = 0) => [/deg_eq0->|nz_p].
- by rewrite mulpC mul0p eq_sym onep_neq0.
case: (deg q = 0) => [/deg_eq0->|nz_q].
- by rewrite mul0p eq_sym onep_neq0.
rewrite degM -1?deg_eq0 // => ME eq.
have {eq}[]: deg p = 1 /\ deg q = 1 by smt(ge0_deg).
move/deg_eq1=> [cp [nz_cp ->>]]; move/deg_eq1=> [cq [nz_cq ->>]].
move/poly_eqP: ME => /(_ 0 _) //; rewrite polyCE /=.
rewrite polyME BCA.big_int1 /= => /unitP @/unitp -> /=.
by rewrite deg_eq1; exists cp.
qed. *)
*)

(* -------------------------------------------------------------------- *)
theory BigPoly.
clone include BigComRing with
    type t <- poly,
    op CR.zeror <- poly0,
    op CR.oner <- poly1,
    op CR.( + ) <- polyD,
    op CR.([-]) <- polyN,
    op CR.( * ) <- polyM,
    op CR.intmul <- PolyRing.intmul,
    op CR.ofint <- PolyRing.ofint,
    op CR.exp <- PolyRing.exp
  proof CR.addrA     by apply: PolyRing.addrA    
  proof CR.addrC     by apply: PolyRing.addrC    
  proof CR.add0r     by apply: PolyRing.add0r    
  proof CR.addNr     by apply: PolyRing.addNr    
  proof CR.oner_neq0 by apply: PolyRing.oner_neq0
  proof CR.mulrA     by apply: PolyRing.mulrA    
  proof CR.mulrC     by apply: PolyRing.mulrC    
  proof CR.mul1r     by apply: PolyRing.mul1r    
  proof CR.mulrDl    by apply: PolyRing.mulrDl

  rename [theory] "BAdd" as "PCA"
         [theory] "BMul" as "PCM"

  remove abbrev CR.(-)
  remove abbrev CR.(/).

lemma polysumE ['a] P F s k :
  (PCA.big<:'a> P F s).[k] = BCA.big P (fun i => (F i).[k]) s.
proof.
  elim: s => /= [|x s ih]; first by rewrite poly0E.
  rewrite !BCA.big_cons -ih PCA.big_cons /=.
  by rewrite -polyDE -(fun_if (fun q => q.[k])).
qed.

end BigPoly.

import BigPoly.

(* -------------------------------------------------------------------- *)
op peval (p : poly) (a : coeff) =
  BCA.bigi predT (fun i => p.[i] * ZModpRing.exp a i) 0 (deg p + 1).

(* -------------------------------------------------------------------- *)
abbrev root p a = peval p a = zero.

end ZModRingPoly.
