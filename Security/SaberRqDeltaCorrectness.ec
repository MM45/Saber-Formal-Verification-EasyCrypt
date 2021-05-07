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
(*  Adversary Prototypes               *)
(* ----------------------------------- *)

module type Adv_Cor = {
   proc choose(pk : pkey, sk : skey) : plaintext
}.

(* ----------------------------------- *)
(*  Saber PKE Correctness Game         *)
(* ----------------------------------- *)

module Saber_PKE_Correctness (A : Adv_Cor) = {
   proc main() : bool = {
      var m: plaintext;
      var m': plaintext option;
      var c: ciphertext;
      var pk: pkey;
      var sk: skey;
      
      (pk, sk) <@ Saber_PKE_Scheme.kg();
      m <@ A.choose(pk, sk);
      c <@ Saber_PKE_Scheme.enc(pk, m);
      m' <@ Saber_PKE_Scheme.dec(sk, c);

      return (Some m = m');
   }
}.

(* ----------------------------------- *)
(* All Rq                              *)
(* ----------------------------------- *)

op scaleZq2Z2 (z : Zq) : Z2 = Z2.inzmod (downscale (Zq.asint z) eq 1).
op scaleZq2Z2t (z : Zq) : Z2t = Z2t.inzmod (downscale (Zq.asint z) eq (et + 1)).

op scaleRq2R2 (p : Rq) : R2 =
  BigR2.XnD1CA.bigi predT (fun i => scaleZq2Z2 p.[i] ** exp R2.iX i) 0 n. 
op scaleRq2R2t (p : Rq) : R2t =
  BigR2t.XnD1CA.bigi predT (fun i => scaleZq2Z2t p.[i] ** exp R2t.iX i) 0 n. 

op upscale (x : int, ea : int, eb : int) : int = shl x (ea - eb).

op scaleZ22Zq (z : Z2) : Zq = Zq.inzmod (upscale (Z2.asint z) eq 1).
op scaleZ2t2Zq (z : Z2t) : Zq = Zq.inzmod (upscale (Z2t.asint z) eq (et + 1)).
op scaleZp2Zq (z : Zp) : Zq = Zq.inzmod (upscale (Zp.asint z) eq ep).

op scaleR22Rq (p : R2) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZ22Zq p.[i] ** exp Rq.iX i) 0 n.
op scaleR2t2Rq (p : R2t) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZ2t2Zq p.[i] ** exp Rq.iX i) 0 n.
op scaleRp2Rq (p : Rp) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZp2Zq p.[i] ** exp Rq.iX i) 0 n.

op scaleRpv2Rqv (pv : Rp_vec) : Rq_vec = offunv (fun i => scaleRp2Rq pv.[i]).

op scaleZq (z : Zq, ez : int) : Zq = Zq.inzmod (upscale (Zq.asint z) ez 0).
 
op scaleRq (p : Rq, er : int) : Rq = 
  BigRq.XnD1CA.bigi predT (fun i => (scaleZq p.[i] er) ** exp Rq.iX i) 0 n.

lemma upscale_DM (ea eb : int) : morphism_2 (fun x => upscale x ea eb) Int.(+) Int.(+).
proof. by move => x y; rewrite /upscale /shl mulrDl. qed.

lemma scale_DM (x y ea eb : int) : 
  2 ^ (ea - eb) %| x \/  2 ^ (ea - eb) %| y => 
  downscale (x + y) ea eb = downscale x ea eb + downscale y ea eb.
proof. by case; rewrite /scale /shr; [apply divzDl | apply divzDr]. qed.

lemma scaleZp2Z2t_DM (z1 z2 : Zp) : 
  2 ^ (ep - (et + 1)) %| Zp.asint z1 \/  2 ^ (ep - (et + 1)) %| Zp.asint z2 => 
  scaleZp2Z2t (z1 + z2) = scaleZp2Z2t z1 + scaleZp2Z2t z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZp2Z2t -inzmodD -scale_DM ?(divz1, divz2) //;
    rewrite addE /p /downscale /shr /inzmod /t -exprS 1:ge0_et modz_pow2_div;
    1, 2, 4, 5: smt(Zp.ge0_asint geet2_ep ge0_et); congr; rewrite modz_dvd_pow; smt(ge0_et).
qed.

lemma scaleZq2Z2t_DM (z1 z2 : Zq) : 
  2 ^ (eq - (et + 1)) %| Zq.asint z1 \/  2 ^ (eq - (et + 1)) %| Zq.asint z2 => 
  scaleZq2Z2t (z1 + z2) = scaleZq2Z2t z1 + scaleZq2Z2t z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZq2Z2t -inzmodD -scale_DM ?(divz1, divz2) //;
    rewrite addE /q /downscale /shr /inzmod /t -exprS 1:ge0_et modz_pow2_div;
    1, 2, 4, 5: smt(Zq.ge0_asint geet2_ep geep1_eq ge0_et); congr; rewrite modz_dvd_pow; smt(ge0_et).
qed.

(*
scaleRp2R2t
  (dotp (pk_decode pk{2}).`2 (Rqv2Rpv s'L) + Rq2Rp h1 +
   shl_enc (m_decode m{2}) (ep - 1)) 
=
scaleRq2R2t
  (dotp (scaleRpv2Rqv (pk_decode pk{2}).`2) s'L + scaleRq h1 (eq - ep) +
   scaleR22Rq (m_decode m{2}))
*)
lemma scaleRp2R2t_DM (p1 p2 : Rp) : 
  ((forall (i : int), 0 <= i < n =>  2 ^ (ep - (et + 1)) %| Zp.asint p1.[i]) \/  
  (forall (i : int), 0 <= i < n =>  2 ^ (ep - (et + 1)) %| Zp.asint p2.[i])) =>
  scaleRp2R2t (p1 + p2) = scaleRp2R2t p1 + scaleRp2R2t p2.
proof.
case => [divz1 | divz2]; rewrite /scaleRp2R2t eq_sym -BigR2t.XnD1CA.big_split /=;
    rewrite !BigR2t.XnD1CA.big_seq &(BigR2t.XnD1CA.eq_bigr) /= => i /mem_range rng_i;
    rewrite -scaleDl eq_sym rcoeffD scaleZp2Z2t_DM ?(divz1, divz2) //.
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

lemma scaleZp2Zq0 : scaleZp2Zq Zp.zero = Zq.zero.
proof. by rewrite /scaleZp2Zq /upscale /shl zeroE. qed.

lemma scaleZp2Zq_DM (z1 z2 : Zp) : scaleZp2Zq (z1 + z2) = scaleZp2Zq z1 + scaleZp2Zq z2.
proof.
rewrite /scaleZp2Zq -inzmodD /upscale /shl -mulrDl addE -eq_inzmod /p /q modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.

lemma scaleZp2Zq_BM (z1 z2 : Zp) : scaleZp2Zq (z1 - z2) = scaleZp2Zq z1 - scaleZp2Zq z2.
proof.
rewrite /scaleZp2Zq -inzmodB /upscale /shl addE oppE -mulrBl -eq_inzmod /p /q.
rewrite modzDmr modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.

lemma scaleZp2Zq_MA (z1 z2 : Zp) : scaleZp2Zq (z1 * z2) = scaleZp2Zq z1 * Zp2Zq z2.
proof.
rewrite /scaleZp2Zq /Zp2Zq -inzmodM /upscale /shl mulrAC mulE -eq_inzmod /p /q modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.


lemma scaleZp2Zq_DM_big (F : int -> Zp) (r: int list) :
  scaleZp2Zq (Rp.BasePoly.BigCf.BCA.big predT F r)
  =
  Rq.BasePoly.BigCf.BCA.big predT (scaleZp2Zq \o F) r.
proof.
elim: r => [| @/(\o) x l ih]. 
+ by rewrite Rp.BasePoly.BigCf.BCA.big_nil Rq.BasePoly.BigCf.BCA.big_nil scaleZp2Zq0.
+ rewrite Rp.BasePoly.BigCf.BCA.big_consT Rq.BasePoly.BigCf.BCA.big_consT /=.
  by rewrite scaleZp2Zq_DM; congr.
qed.

lemma scaleRp2RqE (p : Rp) (i : int) : (scaleRp2Rq p).[i] = scaleZp2Zq p.[i].
proof.
case (i < 0) => [lt0_i | /lezNgt ge0_i]; 1: by rewrite !lt0_rcoeff 3:scaleZp2Zq0.
case (i < n) => [ltn_i | /lezNgt gen_i]; last by rewrite !gered_rcoeff 3:scaleZp2Zq0.
rewrite /scaleRp2Rq rcoeff_sum /=. 
have ->: 
  (fun (i0 : int) => (scaleZp2Zq p.[i0] ** exp Rq.iX i0).[i])
  =
  (fun (i0 : int) => scaleZp2Zq p.[i0] * (exp Rq.iX i0).[i]).
+ by rewrite fun_ext /( == ) => x; apply Rq.rcoeffZ.
rewrite (Rq.BasePoly.BigCf.BCA.bigD1 _ _ i) /=; 1, 2: by rewrite (mem_range, range_uniq).
rewrite Rq.BasePoly.BigCf.BCA.big_seq_cond Rq.BasePoly.BigCf.BCA.big1 /= 2:Zq.ZModpRing.addr0
        => [j [/mem_range rng_j @/predC1 ne_ji]|].
+ by rewrite rcoeff_polyXn // (eq_sym i j) ne_ji /= Zq.ZModpRing.mulr0.
+ by rewrite rcoeff_polyXn //= Zq.ZModpRing.mulr1.
qed.

lemma scaleRp2Rq_DM (p1 p2 : Rp) : scaleRp2Rq (p1 + p2) = scaleRp2Rq p1 + scaleRp2Rq p2.
proof.
by rewrite polyXnD1_eqP => i rng_i; rewrite rcoeffD !scaleRp2RqE rcoeffD scaleZp2Zq_DM.
qed.

lemma scaleRp2Rq_MA (p1 p2 : Rp) : scaleRp2Rq (p1 * p2) = scaleRp2Rq p1 * Rp2Rq p2.
proof.
rewrite polyXnD1_eqP => i rng_i; rewrite scaleRp2RqE !rcoeffM // scaleZp2Zq_DM_big /(\o). 
rewrite !Rq.BasePoly.BigCf.BCA.big_seq &(Rq.BasePoly.BigCf.BCA.eq_bigr) /= => j /mem_range rng_j.
by rewrite scaleZp2Zq_BM !scaleZp2Zq_MA -scaleRp2RqE -!Rp2RqE.
qed.

lemma scaleRp2Rq0 : scaleRp2Rq Rp.zeroXnD1 = Rq.zeroXnD1.
proof. by rewrite polyXnD1_eqP => i rng_i; rewrite scaleRp2RqE !rcoeff0 scaleZp2Zq0. qed.

lemma scaleRp2Rq_DM_big (F : int -> Rp) (r : int list) :
  scaleRp2Rq (Mat_Rp.Big.BAdd.big predT F r)
  =
  Big.BAdd.big predT (scaleRp2Rq \o F) r.
proof.
elim: r => [| @/(\o) x l ih].
+ by rewrite Mat_Rp.Big.BAdd.big_nil Big.BAdd.big_nil scaleRp2Rq0.
+ rewrite Mat_Rp.Big.BAdd.big_consT Big.BAdd.big_consT /=.
  by rewrite scaleRp2Rq_DM; congr.
qed.

lemma scaleRpv2RqvE (pv : Rp_vec) (i : int) : (scaleRpv2Rqv pv).[i] = scaleRp2Rq pv.[i].
proof.
rewrite /scaleRpv2Rqv /Mat_Rq.Vector."_.[_]" offunvK /vclamp.
by case (0 <= i && i < l) => // rng_i; rewrite getv_out // scaleRp2Rq0.
qed.

(* 
lemma Zq2Zp_DM_big (F : int -> Zq) (r : int list) :
      Zq2Zp (Rq.BasePoly.BigCf.BCA.big predT F r)
      =
      BCA.big predT (Zq2Zp \o F) r.
proof.
elim: r; first by rewrite BCA.big_nil Rq.BasePoly.BigCf.BCA.big_nil Zq2Zp0.
move => x l @/(\o) IH; rewrite BCA.big_cons Rq.BasePoly.BigCf.BCA.big_cons {1 4}/predT /=.
by rewrite (Zq2Zp_DM (F x) (Rq.BasePoly.BigCf.BCA.big predT F l)); congr.
qed.
*)

lemma Zp2Zq0 : Zp2Zq Zp.zero = Zq.zero.
proof. by rewrite /Zp2Zq -asintK !zeroE. qed.

lemma Zq2Zp_Zp2Zq_small_inv (z : Zq) : asint z < p => Zp2Zq (Zq2Zp z) = z.
proof.
move => ltp_z; by rewrite /Zq2Zp /Zp2Zq -{2}asintK inzmodK pmod_small 2?(ge0_asint, ltp_z).
qed.

(*
lemma Zp2Zq_DM : morphism_2 Zp2Zq Zp.( + ) Zq.( + ).
proof.
move => x y. rewrite /Zp2Zq addE -inzmodD -eq_inzmod.
qed.

lemma Zp2Zq_DM_big (F : int -> Zp) (r : int list) :
      Zp2Zq (Rp.BasePoly.BigCf.BCA.big predT F r)
      =
      Rq.BasePoly.BigCf.BCA.big predT (Zp2Zq \o F) r.
proof.
elim: r; first by rewrite Rp.BasePoly.BigCf.BCA.big_nil Rq.BasePoly.BigCf.BCA.big_nil Zp2Zq0.
move => x l @/(\o) ih; rewrite  Rp.BasePoly.BigCf.BCA.big_consT Rq.BasePoly.BigCf.BCA.big_consT.
by rewrite Zp2Zq_DM; congr.
qed.
*)

lemma Rq2Rp_Rp2Rq_small_inv (p : Rq) : p \in dsmallRq => Rp2Rq (Rq2Rp p) = p.
proof.
move /supp_dsmallRq => val_coeff; rewrite polyXnD1_eqP => i rngi.
by rewrite rcoeffZ_sum //= rcoeffZ_sum //= Zq2Zp_Zp2Zq_small_inv 1:(val_coeff i).
qed.

(* dotp (q/p * b) s + (q/p * h1)  =  q / p * (dotp b s + h1) *)
(* dotp (q/p * b) s = q/p * (dotp b s) *) 
lemma scaleRp2Rq_DotDM (b : Rp_vec) (s : Rq_vec) : 
  s \in dsmallRq_vec => dotp (scaleRpv2Rqv b) s = scaleRp2Rq (dotp b (Rqv2Rpv s)).
proof.
move /supp_dsmallRq_vec => val_coeff.
rewrite /dotp scaleRp2Rq_DM_big /(\o).
rewrite !Big.BAdd.big_seq &(Big.BAdd.eq_bigr) /= => i /mem_range rng_i.
by rewrite Rqv2RpvE scaleRp2Rq_MA scaleRpv2RqvE Rq2Rp_Rp2Rq_small_inv 1:val_coeff.
qed.

lemma scaleRq_h1 : scaleRq h1 (eq - ep) = scaleRp2Rq (Rq2Rp h1).
proof.
rewrite polyXnD1_eqP => i rng_i.
rewrite rcoeffZ_sum //= eq_sym rcoeffZ_sum //=. 
rewrite /Rq2Rp. rewrite (Rp.rcoeffZ_sum (fun (i0 : int) => Zq2Zp h1.[i0])) //=.
rewrite rcoeffZ_sum //=. rewrite /scaleZp2Zq /scaleZq /Zq2Zp -eq_inzmod.
rewrite !inzmodK. rewrite /q /p modz_dvd_pow. smt(ge2_ep geep1_eq).
have tt: 2 ^ (eq - ep - 1) < 2 ^ ep. admit.
rewrite !(pmod_small (2 ^ (eq - ep - 1))). admit. admit.
trivial.
qed. 

lemma scaleRq_h2 : scaleRq h2 (eq - ep) = scaleRp2Rq (Rq2Rp h2).
proof.
rewrite polyXnD1_eqP => i rng_i.
rewrite rcoeffZ_sum //= eq_sym rcoeffZ_sum //=. 
rewrite /Rq2Rp. rewrite (Rp.rcoeffZ_sum (fun (i0 : int) => Zq2Zp h2.[i0])) //=.
rewrite rcoeffZ_sum //=. rewrite /scaleZp2Zq /scaleZq /Zq2Zp -eq_inzmod.
rewrite !inzmodK.  rewrite /q /p modz_dvd_pow. smt(ge2_ep geep1_eq).
have tt: (2 ^ (ep - 2) - 2 ^ (ep - et - 2)) < 2 ^ ep. admit.
rewrite !(pmod_small ((2 ^ (ep - 2) - 2 ^ (ep - et - 2)))). admit. admit.
trivial.
qed.

lemma scaleZp2Z2_DM (z1 z2 : Zp) : 
  2 ^ (ep - 1) %| Zp.asint z1 \/  2 ^ (ep - 1) %| Zp.asint z2 => 
  scaleZp2Z2 (z1 + z2) = scaleZp2Z2 z1 + scaleZp2Z2 z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZp2Z2 -inzmodD -scale_DM ?(divz1, divz2) //;
    rewrite addE /p /downscale /shr /inzmod modz_pow2_div; 1, 2, 4, 5: smt(Zp.ge0_asint ge2_ep);
    congr; by rewrite opprD addzA /= expr1 modz_mod.
qed.

lemma scale_BM (x y ea eb: int) :
 2 ^ (ea - eb) %| y => downscale (x - y) ea eb = downscale x ea eb - downscale y ea eb.
proof.
move => divy; rewrite /downscale /shr &(mulIf (2 ^ (ea - eb))) 1:lt0r_neq0 1:expr_gt0 // mulrBl.
rewrite (divzK _ y) // 2!divzE -modzDmr.
rewrite &(dvdzN) dvdzE in divy; rewrite divy.
by ring.
qed.

lemma scaleZq2Z2_DM (z1 z2 : Zq) : 
  2 ^ (eq - 1) %| Zq.asint z1 \/  2 ^ (eq - 1) %| Zq.asint z2 => 
  scaleZq2Z2 (z1 + z2) = scaleZq2Z2 z1 + scaleZq2Z2 z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZq2Z2 -inzmodD -scale_DM ?(divz1, divz2) //;
    rewrite addE /q /downscale /shr /inzmod modz_pow2_div; 1, 2, 4, 5: smt(Zq.ge0_asint ge3_eq);
    congr; by rewrite opprD addzA /= expr1 modz_mod.
qed.

lemma scaleRp2R2_DM (p1 p2 : Rp) : 
  ((forall (i : int), 0 <= i < n =>  2 ^ (ep - 1) %| Zp.asint p1.[i]) \/  
  (forall (i : int), 0 <= i < n =>  2 ^ (ep - 1) %| Zp.asint p2.[i])) =>
  scaleRp2R2 (p1 + p2) = scaleRp2R2 p1 + scaleRp2R2 p2.
proof.
case => [divz1 | divz2]; rewrite /scaleRp2R2 eq_sym -BigR2.XnD1CA.big_split /=;
    rewrite !BigR2.XnD1CA.big_seq &(BigR2.XnD1CA.eq_bigr) /= => i /mem_range rng_i;
    rewrite -scaleDl eq_sym rcoeffD scaleZp2Z2_DM ?(divz1, divz2) //.
qed.

lemma scaleRq2R2_DM (p1 p2 : Rq) : 
  ((forall (i : int), 0 <= i < n =>  2 ^ (eq - 1) %| Zq.asint p1.[i]) \/  
  (forall (i : int), 0 <= i < n =>  2 ^ (eq - 1) %| Zq.asint p2.[i])) =>
  scaleRq2R2 (p1 + p2) = scaleRq2R2 p1 + scaleRq2R2 p2.
proof.
case => [divz1 | divz2]; rewrite /scaleRq2R2 eq_sym -BigR2.XnD1CA.big_split /=;
    rewrite !BigR2.XnD1CA.big_seq &(BigR2.XnD1CA.eq_bigr) /= => i /mem_range rng_i;
    rewrite -scaleDl eq_sym rcoeffD scaleZq2Z2_DM ?(divz1, divz2) //.
qed.

lemma scaleR2t2Rq_shldec_c (c : R2t) :
  scaleR2t2Rq c = scaleRp2Rq (shl_dec c).
proof.
   rewrite /scaleR2t2Rq /scaleRp2Rq.
rewrite polyXnD1_eqP => i rngi.
rewrite !rcoeffZ_sum //=.
rewrite /shl_dec rcoeffZ_sum //=.
rewrite /scaleZp2Zq /upscale /shl inzmodK.
rewrite /scaleZ2t2Zq /upscale /shl -eq_inzmod.
rewrite /p /q modz_pow2_mul. smt(ge2_ep geep1_eq).
rewrite mulzA.
rewrite -exprD_nneg; 1, 2: smt(geet2_ep geep1_eq). do 4! congr. by ring.
qed. 

lemma scaleZp2Zq_N (z : Zp) : scaleZp2Zq (- z) = - scaleZp2Zq z.
proof.
rewrite /scaleZp2Zq /upscale /shl -eq_inzmod !inzmodK /p /q modz_pow2_mul; 1: smt(ge2_ep geep1_eq).
by rewrite modzNm mulNr.
qed.

lemma scaleRp2Rq_N (p : Rp): scaleRp2Rq (- p) = - scaleRp2Rq p.
proof.
rewrite /scaleRp2Rq polyXnD1_sumN /= polyXnD1_eqP => i rng_i.
rewrite rcoeffZ_sum //; pose F k := - scaleZp2Zq p.[k].
have -> /=:
  ((BigRq.XnD1CA.bigi predT (fun (i0 : int) => - scaleZp2Zq p.[i0] ** exp Rq.iX i0) 0 n))
  = 
  ((BigRq.XnD1CA.bigi predT (fun (i0 : int) => F i0 ** exp Rq.iX i0) 0 n)).
+ by rewrite 2!BigRq.XnD1CA.big_seq &(BigRq.XnD1CA.eq_bigr) /= => *; rewrite -scaleN.
by rewrite rcoeffZ_sum // /F -rcoeffN scaleZp2Zq_N.
qed.

lemma scaleRp2Rq_BM (p1 p2 : Rp) : scaleRp2Rq (p1 - p2) = scaleRp2Rq p1 - scaleRp2Rq p2.
proof. by rewrite scaleRp2Rq_DM -Rq.ComRing.addrC scaleRp2Rq_N Rq.ComRing.addrC. qed.

lemma scaleZp2Zq2Z2_comp (z : Zp) : scaleZq2Z2 (scaleZp2Zq z) = scaleZp2Z2 z.
proof.
rewrite /scaleZq2Z2 /scaleZp2Zq /scaleZp2Z2 /downscale /upscale /shr /shl -eq_inzmod !inzmodK /p /q.
rewrite modz_pow2_div 1:?(mulr_ge0, ge0_asint, expr_ge0); 1, 2: smt(geep1_eq ge3_eq).
have ->: 2 ^ (eq - 1) = 2 ^ (ep - 1) * 2 ^ (eq - ep).
+ by rewrite -exprD_nneg; 1, 2: smt(ge2_ep geep1_eq); congr; ring.
by rewrite divzMpr 1:expr_gt0 2:opprD 2:addrA //= expr1 modz_mod.
qed.

module Saber_PKE_Scheme_Rq : Scheme = {
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
      v' <- (dotp bq s') + (scaleRq h1 (eq - ep));
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
      
      v <- (dotp bq' s) + (scaleRq h1 (eq - ep));
      m' <- scaleRq2R2 (v  - cmq + (scaleRq h2 (eq - ep)));
      
      return Some (m_encode m');
   }
}.


lemma eq_kg: equiv[Saber_PKE_Scheme.kg ~ Saber_PKE_Scheme_Rq.kg : true ==> ={res}].
proof.
by proc; sim.
qed.

lemma eq_enc: equiv[Saber_PKE_Scheme.enc ~ Saber_PKE_Scheme_Rq.enc : ={pk, m} ==> ={res}].
proof.
proc.
auto; progress. 
congr; rewrite &(pw_eq) //.
rewrite scaleRp2R2t_DM 2: scaleRq2R2t_DM; 1, 2: right => i rng_i.
+ rewrite rcoeffZ_sum //= inzmodK /shl.
  case (asint (m_decode m{2}).[i] = 0) => [-> /= | neq0_m].
  - by apply dvdz0.
  - have -> /=:  (Z2.asint (m_decode m{2}).[i]) = 1. admit.
    rewrite pmod_small. admit.
    by apply dvdz_exp2l; smt(ge0_et geet2_ep). 
+ rewrite rcoeffZ_sum //= inzmodK /upscale /shl. 
  case (asint (m_decode m{2}).[i] = 0) => [-> /= | neq0_m].
  - by apply dvdz0.
  - have -> /=:  (Z2.asint (m_decode m{2}).[i]) = 1. admit.
    rewrite pmod_small. admit.
    by apply dvdz_exp2l; smt(ge0_et geet2_ep geep1_eq). 
congr; last first.
+ rewrite polyXnD1_eqP /shl_enc /scaleR22Rq => i rngi.
  rewrite !rcoeffZ_sum //= !rcoeffZ_sum //=.
  rewrite eq_sym /scaleZq2Z2t /scaleZ22Zq inzmodK.
  rewrite eq_sym /scaleZp2Z2t inzmodK -eq_inzmod.
  rewrite /upscale /shl (pmod_small _ p) 2:(pmod_small _ q). admit. admit.
  rewrite /downscale /shr (_ : 2 ^ (ep - 1) = 2 ^ (ep - (et + 1)) * 2 ^ et).
  rewrite -exprD_nneg; 1, 2: smt(geet2_ep ge0_et). congr. ring.
  rewrite (mulzC _ (2 ^ et)) -mulzA mulzK. admit.
  rewrite (_ : 2 ^ (eq - 1) = 2 ^ (eq - (et + 1)) * 2 ^ et).
  rewrite -exprD_nneg; 1, 2: smt(geet2_ep geep1_eq ge0_et).
  congr. ring.
  rewrite eq_sym (mulzC _ (2 ^ et)) -mulzA mulzK. admit. trivial.
+ rewrite eq_sym scaleRp2Rq_DotDM // scaleRq_h1 -scaleRp2Rq_DM.
  rewrite polyXnD1_eqP => i rng_i.
  rewrite !rcoeffZ_sum //= rcoeffZ_sum //=. 
  rewrite /scaleZq2Z2t /scaleZp2Zq !inzmodK.
  rewrite /scaleZp2Z2t -eq_inzmod /downscale /upscale /shr /shl /q /t -exprS 1:ge0_et.
  rewrite modz_pow2_div. admit. smt(ge0_et geet2_ep geep1_eq).
  rewrite (_ : 2 ^ (eq - (eq - (et + 1))) = 2 ^ (et + 1)) 2:modz_mod. congr; ring.
  rewrite (_ : 2 ^ (eq - (et + 1)) = 2 ^ (eq - ep) * 2 ^ (ep - (et + 1))).
  rewrite -exprD_nneg; 1,2: smt(geet2_ep geep1_eq). congr; ring.
  rewrite -(mulzC (2 ^ (ep - (et + 1)))) divzMpr. admit.
  trivial.
qed.

lemma eq_dec: equiv[Saber_PKE_Scheme.dec ~ Saber_PKE_Scheme_Rq.dec : 
  ={sk, c} /\ 
  sk_decode_s sk{1} \in dsmallRq_vec /\
  sk_decode_s sk{2} \in dsmallRq_vec
  ==> 
  ={res}].
proof.
proc.
auto; progress.
congr.
rewrite scaleRp2Rq_DotDM //.
rewrite scaleRq_h1 scaleRq_h2 scaleR2t2Rq_shldec_c.
rewrite Rq.ComRing.addrC.
rewrite Rp.ComRing.addrC.
rewrite Rq.ComRing.addrA.
rewrite Rp.ComRing.addrA.
rewrite -scaleRp2Rq_DM.
rewrite -scaleRp2Rq_DM.
rewrite -scaleRp2Rq_BM.
rewrite polyXnD1_eqP => i rng_i; rewrite eq_sym /scaleRq2R2 !rcoeffZ_sum //= rcoeffZ_sum //=.
rewrite scaleZp2Zq2Z2_comp. trivial.
qed.

(* TODO:
- Change definitions of regular scheme regarding encoding/decoding such that
  we can use the types of the artifacts in above proof (i.e., dont use encoding/decoding
  when unnecessary, and when necesarry, a seperate one for regular scheme with concrete typing).
- Remove all admits.
- Define subtype for secret key (only taking values currently in dsmallRq_vec), and have that be the domain and range of s_encode and s_decode, respectively.
- Clean up.
*)
