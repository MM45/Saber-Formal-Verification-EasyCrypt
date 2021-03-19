prover ["Alt-Ergo"].

(*----- Require/Import/Include EasyCrypt Theories -----*)
require import AllCore Distr DBool.
require (*--*) Matrix PKE ROM.

(*----- CODE -----*)
(*--- Definitions and Initialization ---*)
(*- Constants -*)
const eq : int.
const ep : int.
const et : int.
const q : int = 2^eq. 
const p : int = 2^ep.
const t : int = 2^et.

axiom exp_relation: et + 1 < ep < eq.  
axiom sec_assumption: eq - ep <= ep - et -1. (* q %/ p <= p %/ 2*t. *)

(*- Types and Operators -*)
type Rq.
clone import Ring.ComRing as Rq with type t <- Rq.
clone Matrix as Mat_Rq with type R <- Rq.

type Rp.
clone import Ring.ComRing as Rp with type t <- Rp.
clone Matrix as Mat_Rp with type R <- Rp.

import Mat_Rq Mat_Rp.

type Rppq.
clone import Ring.ComRing as Rppq with type t <- Rppq.

type R2t.
clone import Ring.ComRing as R2t with type t <- R2t.

type R2.
clone import Ring.ComRing as R2 with type t <- R2.

type seed.
type pkey.
type skey.
type plaintext.
type ciphertext.

type Rq_vec = Mat_Rq.vector.
type Rq_mat = Mat_Rq.Matrix.matrix.
type Rp_vec = Mat_Rp.vector.
type Rp_mat = Mat_Rp.Matrix.matrix.

op sar ['a, 'b] : 'a -> 'b = fun (_ : 'a) => witness.
op sar_vec ['a, 'b] : 'a -> 'b = fun(_: 'a) => witness.

(*
op sar_Rp_R2 : Rp -> R2.
op sar_Rp_R2t : Rp -> R2t.
op sar_Rp_Rppq : Rp -> Rppq. 
op sar_Rq_Rp : Rq -> Rp.
op sar_vec_Rq_Rp : Rq_vec -> Rp_vec.
*)

op pk_encode ['a] : pkey -> 'a.
op pk_decode ['a] : 'a -> pkey. 
axiom pk_enc_dec_inv ['a] : forall (x : 'a), x = pk_encode (pk_decode x).

op m_encode ['a] : plaintext -> 'a.
op m_decode ['a] : 'a -> plaintext.
axiom m_enc_dec_inv ['a] : forall (x : 'a), x = m_encode (m_decode x).

op c_encode ['a] : ciphertext -> 'a.
op c_decode ['a] : 'a -> ciphertext.
axiom c_enc_dec_inv ['a] : forall (x : 'a), x = c_encode (c_decode x).

op [lossless full uniform] dseed : seed distr. 
op [lossless full uniform] dRq : Rq distr.
op [lossless full uniform] dRp : Rp distr.
op [lossless] dsmallRq : Rq distr.

op dRq_mat = Mat_Rq.Matrix.dmatrix dRq.
op dRq_vec = Mat_Rq.Matrix.dvector dRq.
op dsmallRq_vec = Mat_Rq.Matrix.dvector dsmallRq.

op dRp_vec = Mat_Rp.Matrix.dvector dRp.

(* Distribution of vector has same properties as the distribution of its elements *)
lemma dRq_vec_ll : is_lossless dRq_vec.
proof. apply /Mat_Rq.Matrix.dvector_ll /dRq_ll. qed.

lemma dRq_vec_uni : is_uniform dRq_vec.
proof. apply /Mat_Rq.Matrix.dvector_uni /dRq_uni. qed.

lemma dRq_vec_fu : is_full dRq_vec.
proof. apply /Mat_Rq.Matrix.dvector_fu /dRq_fu. qed.

lemma dRp_vec_ll : is_lossless dRp_vec.
proof. apply /Mat_Rp.Matrix.dvector_ll /dRp_ll. qed.

lemma dRp_vec_uni : is_uniform dRp_vec.
proof. apply /Mat_Rp.Matrix.dvector_uni /dRp_uni. qed.

lemma dRp_vec_fu : is_full dRp_vec.
proof. apply /Mat_Rp.Matrix.dvector_fu /dRp_fu. qed.

lemma dsmallRq_vec_ll : is_lossless dsmallRq_vec.
proof. apply /Mat_Rq.Matrix.dvector_ll /dsmallRq_ll. qed.

(* Distribution of matrix has same properties as the distribution of its elements *)
lemma dRq_mat_ll : is_lossless dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_ll /dRq_ll. qed.

lemma dRq_mat_uni : is_uniform dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_uni /dRq_uni. qed.

lemma dRq_mat_fu : is_full dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_fu /dRq_fu. qed.

op vec_mod_q_p : Rq_vec -> Rp_vec.
axiom vec_mod_q_p_small_coefficients: forall (x : Rq_vec), x \in dsmallRq_vec => x = vec_mod_q_p x. 
axiom vec_mod_q_p_maintains_uniformity: forall (x : Rq_vec), (forall (y : Rq_vec), mu1 ) 

(*- Cloning -*)
clone import ROM as MLWR_ROM with
   type in_t <- seed,
   type out_t <- Rq_mat,
   op dout <- fun (sd : seed) => dRq_mat,
   type d_in_t <- unit,
   type d_out_t <- bool.
import Lazy.

clone import PKE as HighLevelSaberPKE with
    type pkey <- pkey,
    type skey <- Rq_vec,
    type plaintext <- Rp,
    type ciphertext <- ciphertext. (*(R2t * Rp_vec).*)


(*- Module Types -*)
module type Adv_GMLWR = {
   proc guess(sd : seed, b : Rp_vec) : bool
}.

module type Adv_XMLWR = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool
}.


(*- Modules -*)
module GMLWR(A : Adv_GMLWR) = {
   proc main(u : bool) = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;

      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- sar_vec (_A *^ s);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.

module XMLWR(A : Adv_XMLWR) = {
   proc main(u : bool) = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var a : Rq_vec;
      var d : Rp;

      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- sar_vec (_A *^ s);
      }
      
      a <$ dRq_vec;

      if (u) {
         d <$ dRp;
      } else {
         d <- sar (dotp a s);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.

(* TODO: INTRODUCE R2t and R2, and adjust type of ciphertext and message accordingly*)
module HighLevelSaberScheme : Scheme = {
   proc kg() : pkey * Rq_vec = {
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      
      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallRq_vec;
      b <- sar_vec (_A *^ s);
      
      return (pk_decode (sd, b), s);
   }

   proc enc(pk : pkey, m : Rp) : ciphertext = {
      var sd : seed;
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var cm : R2t;
      var pk_enc : (seed * Rp_vec);
      
      pk_enc <- pk_encode pk;
      sd <- pk_enc.`1;
      b <- pk_enc.`2;
      _A <@ LRO.o(sd);
      s' <$ dsmallRq_vec;
      b' <- sar_vec ((trmx _A) *^ s');
      v' <- dotp b (sar_vec s');
      cm <- sar (v' + m);

      return c_decode (cm, b');
   }
   
   proc dec(sk: Rq_vec, c : ciphertext) : Rp option = {
      var s : Rq_vec;
      var b' : Rp_vec; 
      var v : Rp;
      var cm : R2t;
      var c_enc : (R2t * Rp_vec) ;
      
      c_enc <- c_encode c;
      cm <- c_enc.`1;
      b' <- c_enc.`2;
      s <- sk;
      v <- dotp b' (sar_vec s);

      return Some (v - sar cm);
   }
}.

module Game0(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : Rp;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var c : R2t;
      
      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallRq_vec;
      b <- sar_vec (_A *^ s);
      (m0, m1) <@ A.choose(pk_decode (sd, b));
      s' <$ dRq_vec;
      b' <- sar_vec ((trmx _A) *^ s');
      v' <- dotp b (sar_vec s');
      c <- sar (if u then v' + m1 else v' + m0);

      u' <@ A.guess(c_decode (c, b'));

      return u';
   }
}.

module Game1(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : Rp;

      var sd : seed;
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var c : R2t;
      
      sd <$ dseed;
      _A <@ LRO.o(sd);
      (* Skip (s <$ dsmallRq_vec); *)
      b <$ dRp_vec;
      (m0, m1) <@ A.choose(pk_decode (sd, b));
      s' <$ dRq_vec;
      b' <- sar_vec ((trmx _A) *^ s');
      v' <- dotp b (sar_vec s');
      c <- sar (if u then v' + m1 else v' + m0);

      u' <@ A.guess(c_decode (c, b'));

      return u';
   }
}.

module Game2(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : Rp;

      var sd : seed;
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var c : Rppq;
      
      sd <$ dseed;
      _A <@ LRO.o(sd);
      b <$ dRp_vec;
      (m0, m1) <@ A.choose(pk_decode (sd, b));
      s' <$ dRq_vec;
      b' <- sar_vec ((trmx _A) *^ s');
      v' <- dotp b (sar_vec s');
      c <- sar (if u then v' + m1 else v' + m0);

      u' <@ A.guess(c_decode (c, b'));

      return u';
   }
}.

module Game3(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : Rp;

      var sd : seed;
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var c : Rp;
      
      sd <$ dseed;
      _A <@ LRO.o(sd);
      b <$ dRq_vec;
      (m0, m1) <@ A.choose(pk_decode (sd, b));
      s' <$ dRq_vec;
      b' <- sar_vec ((trmx _A) *^ s');
      v' <- sar_vec (dotp b  s');
      c <- sar (if u then v' + m1 else v' + m0);

      u' <@ A.guess(c_decode (c, b'));

      return u';
   }
}.

module Game4(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : Rp;

      var sd : seed;
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var c : Rp;
      
      sd <$ dseed;
      _A <@ LRO.o(sd);
      b <$ dRq_vec;
      (m0, m1) <@ A.choose(pk_decode (sd, b));
      (* Skip (s' <$ dRq_vec;) *)
      b' <$ dRp_vec;
      v' <$ dRp;
      c <- sar (if u then v' + m1 else v' + m0);

      u' <@ A.guess(c_decode (c, b'));

      return u';
   }
}.

(*- (Reduction) Adversaries -*)
module B0(A : Adversary) : Adv_GMLWR = {
   proc guess(sd : seed, b : Rp_vec) : bool = {
      var w, w' : bool;
      var m0, m1 : Rp;
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var cm : R2t;

      w <$ dbool;
      _A <@ LRO.o(sd);
      (m0, m1) <@ A.choose(pk_decode (sd, b));
      s' <$ dsmallRq_vec;
      b' <- sar ((trmx _A) *^ s');
      v' <- dotp b (sar s');
      cm <- sar (if w then v' + m1 else v' + m0);
      w' <@ A.guess(c_decode (cm, b'));
      
      return (w = w');
   }
}.

module A2(A1 : Adversary) : Adversary = {
   proc choose(pk : pkey) : (Rp * Rp) = {
      var pk_enc : (seed * Rp_vec);
      var sd : seed;
      var b : Rp_vec;
      var m0, m1 : Rp;
      
      pk_enc <- pk_encode pk;
      sd <- pk_enc.`1;
      b <- pk_enc.`2;
      (m0, m1) <@ A1.choose(pk_decode (sd, b));

      return (m0, m1);
   }
   
   proc guess(c : ciphertext) : bool = {
      var u' : bool;
      var c_enc : (Rppq * Rp_vec);
      var cm : Rppq;
      var b' : Rp_vec;
      
      c_enc <- c_encode c;
      cm <- c_enc.`1;
      b' <- c_enc.`2;
      
      u' <@ A1.guess(c_decode (cm, b'));

      return u';
   }
}.

module A3(A2 : Adversary) : Adversary = {
   proc choose(pk : pkey) : (Rp * Rp) = {
      var pk_enc : (seed * Rq_vec);
      var sd : seed;
      var b : Rq_vec;
      var bp : Rp_vec;
      var m0, m1 : Rp;
      
      pk_enc <- pk_encode pk;
      sd <- pk_enc.`1;
      b <- pk_enc.`2;
      (m0, m1) <@ A1.choose(pk_decode (sd, b));

      return (m0, m1);
   }
   
   proc guess(c : ciphertext) : bool = {
      var u' : bool;
      var c_enc : (Rppq * Rp_vec);
      var cm : Rppq;
      var b' : Rp_vec;
      
      c_enc <- c_encode c;
      cm <- c_enc.`1;
      b' <- c_enc.`2;
      
      u' <@ A1.guess(c_decode (cm, b'));

      return u';
   }
}.

module B1(A : Adversary) : Adv_XMLWR = {

}.

(*- Game-Based Security Proof -*)
section.

declare module A : Adversary.

(* Saber's INDCPA == Game 0 *)
lemma Equivalence_SaberINDCPA_Game0 &m :
      `| Pr[CPA_R(HighLevelSaberScheme, A).main() @ &m : res] - Pr[CPA_L(HighLevelSaberScheme, A).main() @ &m : res] |
      =
      `| Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res] |.
proof.
  admit.
qed.

(* Game0 <> Game1 ==> GMLWR *)



(* Game1 ==> Game2 *)



(* Game2 ==> Game3 *)



(* Game3 <> Game4 ==> XMLWR *)



(* Final Result (Security Theorem) *)
