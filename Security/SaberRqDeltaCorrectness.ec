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
(* Properties                          *)
(* ----------------------------------- *)

lemma shl_shr_error (x : int, ex : int) : shl (shr x ex) ex = x - (x %% 2 ^ ex).
proof. by rewrite /shr /shl divzE. qed.

(* ----------------------------------- *)
(* All Rq                              *)
(* ----------------------------------- *)

pragma Goals:printall.

op scaleZq2Z2 (z : Zq) : Z2 = Z2.inzmod (scale (Zq.asint z) eq 1).
op scaleZq2Z2t (z : Zq) : Z2t = Z2t.inzmod (scale (Zq.asint z) eq (et + 1)).

op scaleRq2R2 (p : Rq) : R2 =
  BigR2.XnD1CA.bigi predT (fun i => scaleZq2Z2 p.[i] ** exp R2.iX i) 0 n. 
op scaleRq2R2t (p : Rq) : R2t =
  BigR2t.XnD1CA.bigi predT (fun i => scaleZq2Z2t p.[i] ** exp R2t.iX i) 0 n. 

op scale_up (x : int, ea : int, eb : int) : int = shl x (ea - eb).

op scaleZ22Zq (z : Z2) : Zq = Zq.inzmod (scale_up (Z2.asint z) eq 1).
op scaleZ2t2Zq (z : Z2t) : Zq = Zq.inzmod (scale_up (Z2t.asint z) eq (et + 1)).
op scaleZp2Zq (z : Zp) : Zq = Zq.inzmod (scale_up (Zp.asint z) eq ep).

op scaleR22Rq (p : R2) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZ22Zq p.[i] ** exp Rq.iX i) 0 n.
op scaleR2t2Rq (p : R2t) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZ2t2Zq p.[i] ** exp Rq.iX i) 0 n.
op scaleRp2Rq (p : Rp) : Rq =
  BigRq.XnD1CA.bigi predT (fun i => scaleZp2Zq p.[i] ** exp Rq.iX i) 0 n.

op scaleRpv2Rqv (pv : Rp_vec) : Rq_vec = offunv (fun i => scaleRp2Rq pv.[i]).

op scaleZq (z : Zq, ez : int) : Zq = Zq.inzmod (scale_up (Zq.asint z) ez 0).
 
op scaleRq (p : Rq, er : int) : Rq = 
  BigRq.XnD1CA.bigi predT (fun i => (scaleZq p.[i] er) ** exp Rq.iX i) 0 n.

lemma scale_up_DM (ea eb : int) : morphism_2 (fun x => scale_up x ea eb) Int.(+) Int.(+).
proof. by move => x y; rewrite /scale_up /shl mulrDl. qed.

lemma scale_DM (x y ea eb : int) : 
  2 ^ (ea - eb) %| x \/  2 ^ (ea - eb) %| y => scale (x + y) ea eb = scale x ea eb + scale y ea eb.
proof. by case; rewrite /scale /shr; [apply divzDl | apply divzDr]. qed.

lemma scaleZp2Z2t_DM (z1 z2 : Zp) : 
  2 ^ (ep - (et + 1)) %| Zp.asint z1 \/  2 ^ (ep - (et + 1)) %| Zp.asint z2 => 
  scaleZp2Z2t (z1 + z2) = scaleZp2Z2t z1 + scaleZp2Z2t z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZp2Z2t -inzmodD -scale_DM ?(divz1, divz2) //;
    rewrite addE /p /scale /shr /inzmod /t -exprS 1:ge0_et modz_pow2_div;
    1, 2, 4, 5: smt(Zp.ge0_asint geet2_ep ge0_et); congr; rewrite modz_dvd_pow; smt(ge0_et).
qed.

lemma scaleZq2Z2t_DM (z1 z2 : Zq) : 
  2 ^ (eq - (et + 1)) %| Zq.asint z1 \/  2 ^ (eq - (et + 1)) %| Zq.asint z2 => 
  scaleZq2Z2t (z1 + z2) = scaleZq2Z2t z1 + scaleZq2Z2t z2.
proof. 
case => [divz1 | divz2]; rewrite /scaleZq2Z2t -inzmodD -scale_DM ?(divz1, divz2) //;
    rewrite addE /q /scale /shr /inzmod /t -exprS 1:ge0_et modz_pow2_div;
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
move => rng_p; case (p = 0) => [-> /=| neq0_p].
+ by rewrite expr0 /= modzMl.
+ rewrite modzE eq_sym modzE {1 3}(_ : 2 ^ n = 2 ^ (n - p) * 2 ^ p) 1:-exprD_nneg; first 3 smt().
  rewrite {2}(mulzC i) {2}(mulzC (i %% 2 ^ p)) eq_sym !divzMpl; first 2 smt(expr_gt0). 
  rewrite pdiv_small /=; 1: smt(modz_ge0 ltz_pmod expr_gt0).
  rewrite modzE mulrBl -mulrA -exprD_nneg; first 2 smt().
  by rewrite (addzC p) -addzA.
qed.

lemma scaleZp2Zq0 : scaleZp2Zq Zp.zero = Zq.zero.
proof. by rewrite /scaleZp2Zq /scale_up /shl zeroE. qed.

lemma scaleZp2Zq_DM (z1 z2 : Zp) : scaleZp2Zq (z1 + z2) = scaleZp2Zq z1 + scaleZp2Zq z2.
proof.
rewrite /scaleZp2Zq -inzmodD /scale_up /shl -mulrDl addE -eq_inzmod /p /q modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.

lemma scaleZp2Zq_BM (z1 z2 : Zp) : scaleZp2Zq (z1 - z2) = scaleZp2Zq z1 - scaleZp2Zq z2.
proof.
rewrite /scaleZp2Zq -inzmodB /scale_up /shl addE oppE -mulrBl -eq_inzmod /p /q.
rewrite modzDmr modz_pow2_mul //.
+ smt(ge2_ep geep1_eq).
qed.

lemma scaleZp2Zq_MA (z1 z2 : Zp) : scaleZp2Zq (z1 * z2) = scaleZp2Zq z1 * Zp2Zq z2.
proof.
rewrite /scaleZp2Zq /Zp2Zq -inzmodM /scale_up /shl mulrAC mulE -eq_inzmod /p /q modz_pow2_mul //.
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

(* dotp (q/p * b) s + (q/p * h1)  =  q / p * (dotp b s + h1) *)
(* dotp (q/p * b) s = q/p * (dotp b s) *) 
lemma test (b : Rp_vec) (s : Rq_vec) : 
  dotp (scaleRpv2Rqv b) s = scaleRp2Rq (dotp b (Rqv2Rpv s)).
proof.
rewrite /dotp scaleRp2Rq_DM_big /(\o).
rewrite !Big.BAdd.big_seq &(Big.BAdd.eq_bigr) /= => i /mem_range rng_i.
rewrite Rqv2RpvE scaleRp2Rq_MA.
(* Rq2Rp s.[i] = s.[i]*)
admit.
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
      
      return (pk_encode (sd, b), sk_encode s);
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
      pk_dec <- pk_decode pk;
      sd <- pk_dec.`1;
      b <- pk_dec.`2;
      _A <- gen sd;
      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      bq <- scaleRpv2Rqv b;
      v' <- (dotp bq s') + (scaleRq h1 (eq - ep));
      cm <- scaleRq2R2t (v' + (scaleR22Rq m_dec));
      
      return c_encode (cm, b');
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

      c_dec <- c_decode c;
      s <- sk_decode sk;
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
admit.
qed.

lemma eq_dec: equiv[Saber_PKE_Scheme.dec ~ Saber_PKE_Scheme_Rq.dec : ={sk, c} ==> ={res}].
proof.
proc.
auto; progress.
congr.
admit.
qed.
