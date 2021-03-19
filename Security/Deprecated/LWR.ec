prover ["Alt-Ergo"].

pragma Goals:printall.

(*
----------------------------------- 
 Require/Import EasyCrypt Theories
-----------------------------------
*)
require import AllCore Distr DBool ZModP IntDiv.
require (*--*) Matrix PKE ROM.

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
axiom exp_relation: 0 < et + 1 < ep < eq.
axiom sec_assumption: eq - ep <= ep - et -1. (* q %/ p <= p %/ 2*t. *)
axiom module_dimension_ge1: 1 <= l.

lemma et_ge0: 0 <= et by smt.
lemma ep_ge2: 2 <= ep by smt.
lemma eq_ge3: 3 <= eq by smt.

(* --- Types, Operators and Distributions --- *)
(* -- Zq = Z/qZ -- *)
type Zq.

clone import ZModRing as Zq with
    op p <- q,
    type zmod <- Zq
  proof ge2_p by smt.

clone import MFinite as DZq with
    type t <- Zq,
    op Support.card <- q.

op dZq : Zq distr = DZq.dunifin.

clone Matrix as Mat_Zq with
    type R <- Zq,
    op size <- l
  proof ge0_size by smt.

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
  proof ge2_p by smt.

clone import MFinite as DZp with
    type t <- Zp,
    op Support.card <- p.

op dZp : Zp distr = DZp.dunifin.

clone Matrix as Mat_Zp with
    type R <- Zp,
    op size <- l
  proof ge0_size by smt.

type Zp_vec = Mat_Zp.vector.

op dZp_vec : Zp_vec distr = Mat_Zp.Matrix.dvector dZp.

(* -- Zppq = Z/ppqZ -- *)
type Zppq.

clone import ZModRing as Zppq with
    op p <- p * p %/ q,
    type zmod <- Zppq.

(* -- Z2t = Z/2tZ  -- *)
type Z2t.

clone import ZModRing as Z2t with
    op p <- 2 * t,
    type zmod <- Z2t
    proof ge2_p by smt.

(* -- Z2 = Z/2Z -- *)
type Z2.

clone import ZModRing as Z2 with
    op p <- 2,
    type zmod <- Z2
    proof ge2_p by smt.

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

op scale (x : int, ea : int, eb : int) : int = if eb < ea then x %/ (2^(ea - eb)) else x * 2^(eb - ea).

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

(* (x %/ a) %/ b == x %/ (a * b) *)
lemma scale_split (x ea eab eb : int):
      0 <= eb => eb <= eab => eab <= ea =>
      scale x ea eb = scale (scale x ea eab) eab eb. 
proof. admit. qed.

lemma scale_split_p_ppq_2t (x : Zp):
      scale_p_2t x = scale_ppq_2t (scale_p_ppq x).
proof. admit. qed.

lemma scale_id (x ea eb : int) : ea = eb => scale x ea eb = x.
proof. by move=> eq_eaeb; rewrite /scale eq_eaeb addzN expr0. qed.

lemma scale_p_p_id (x : Zp) : scale_p_p x = x.
proof. by rewrite /scale_p_p scale_id; [trivial | rewrite asintK]. qed.

(* --- ROM --- *)
clone import ROM as MLWR_ROM with
   type in_t <- seed,
   type out_t <- Zq_mat,
   op dout <- fun (sd: seed) => dZq_mat,
   type d_in_t <- unit,
   type d_out_t <- bool.
import Lazy.

(* --- PKE --- *)
clone import PKE as Saber_PKE with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

(* --- General Lemmas --- *)
lemma triangle_inequality (x y z : real) : `|x - z| <= `|x - y| + `|y - z| by smt.
lemma reverse_triangle_inequality (x y : real) : `|x - y| >= `| `| x | - `| y | | by smt. 

(*
--------------------------------
 Saber PKE Scheme (in ROM)
--------------------------------
*)
module Saber_PKE_Scheme_ROM : Scheme = {
   proc kg() : pkey * skey = {
      var sd: seed;
      var _A: Zq_mat;
      var s: Zq_vec;
      var b: Zp_vec;
      
      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallZq_vec;
      b <- scale_vec_q_p (_A *^ s + h);
      
      return (pk_encode (sd, b), sk_encode s);
   }

   proc enc(pk: pkey, m: plaintext) : ciphertext = {
      var pk_dec: seed * Zp_vec;
      var m_dec: Z2;

      var sd: seed;
      var _A: Zq_mat;
      var s': Zq_vec;
      var b, b': Zp_vec;
      var v': Zp;
      var cm: Z2t;
      
      m_dec <- m_decode m;
      pk_dec <- pk_decode pk;
      sd <- pk_dec.`1;
      b <- pk_dec.`2;
      _A <@ LRO.o(sd);
      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p ((trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cm <- scale_p_2t (v' + (Zp.inzmod (scale (Z2.asint m_dec) 1 ep)));
      
      return c_encode (cm, b');
   }

   proc dec(sk: skey, c: ciphertext) : plaintext option = {
      var c_dec: Z2t * Zp_vec;
      var cm: Z2t;
      var b': Zp_vec;
      var v: Zp;
      var s: Zq_vec;
      var m': Z2;

      c_dec <- c_decode c;
      s <- sk_decode sk;
      cm <- c_dec.`1;
      b' <- c_dec.`2;
      v <- (dotp b' (mod_p_Zq_vec s)) + (Zp.inzmod (Zq.asint h2));
      m' <- scale_p_2 (v - (Zp.inzmod (scale (Z2t.asint cm) (et + 1) ep)) + (Zp.inzmod (Zq.asint h2)));
      
      return Some (m_encode m');
   }
}.

(*
--------------------------------
 Adversary Prototypes
--------------------------------
*)
module type Adv_GMLWR = {
   proc guess(sd : seed, b : Zp_vec) : bool
}.

module type Adv_XMLWR = {
   proc guess(sd : seed, b : Zp_vec, a : Zq_vec, d : Zp) : bool
}.

(*
--------------------------------
 Games
--------------------------------
*)
(* --- General CPA ROM Game --- *)
module CPA_ROM (S : Scheme, A : Adversary) = {
  proc main(b : bool) : bool = {
    var pk : pkey;
    var sk : skey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b' : bool;

    LRO.init();

    (pk, sk) <@ S.kg();
    (m0, m1) <@ A.choose(pk);
    c        <@ S.enc(pk, if b then m1 else m0);
    b'       <@ A.guess(c);

    return b';
  }
}.

(* --- LWR-Related Games --- *)
module GMLWR(A : Adv_GMLWR) = {
   proc main(u : bool) = {
      var u' : bool;
      var sd : seed;
      var _A : Zq_mat;
      var s : Zq_vec;
      var b : Zp_vec;
      
      LRO.init();

      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallZq_vec;
      
      if (u) {
         b <$ dZp_vec;
      } else {
         b <- scale_vec_q_p (_A *^ s + h);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.

module XMLWR(A : Adv_XMLWR) = {
   proc main(u : bool) = {
      var u' : bool;
      var sd : seed;
      var _A : Zq_mat;
      var s : Zq_vec;
      var b : Zp_vec;
      var a : Zq_vec;
      var d : Zp;
      
      LRO.init();

      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallZq_vec;
      
      if (u) {
         b <$ dZp_vec;
      } else {
         b <- scale_vec_q_p ((trmx _A) *^ s + h);
      }
      
      a <$ dZq_vec;

      if (u) {
         d <$ dZp;
      } else {
         d <- scale_q_p ((dotp a s) + h1);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.

(* --- Game Sequence --- *)
(* Game 0 *)
module Game0(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b, b' : Zp_vec;
      var v' : Zp;
      var cmu : Z2t;
      
      LRO.init();

      sd <$ dseed;
      _A <@ LRO.o(sd);
      s <$ dsmallZq_vec;
      b <- scale_vec_q_p (_A *^ s + h);

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p (( trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmu <- scale_p_2t (v' + (Zp.inzmod (scale (Z2.asint (m_decode (if u then m1 else m0))) 1 ep)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return u';
   }
}.

(* Game 1 *)
module Game1(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b, b' : Zp_vec;
      var v' : Zp;
      var cmu : Z2t;
      
      LRO.init();

      sd <$ dseed;
      _A <@ LRO.o(sd);
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZp_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p (( trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmu <- scale_p_2t (v' + (Zp.inzmod (scale (m_decode (if u then m1 else m0)) 1 ep)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return u';
   }
}.

(* Game 2 *)
module Game2(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b, b' : Zp_vec;
      var v' : Zp;
      var cmu : Zppq;
      
      LRO.init();

      sd <$ dseed;
      _A <@ LRO.o(sd);
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZp_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p ((trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmu <- scale_p_ppq (v' + (Zp.inzmod (scale (m_decode (if u then m1 else m0)) 1 ep)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return u';
   }
}.

(* Game 3 *)
module Game3(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b : Zq_vec;
      var b' : Zp_vec;
      var v' : Zp;
      var cmu : Zp;
      
      LRO.init();

      sd <$ dseed;
      _A <@ LRO.o(sd);
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZq_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p (( trmx _A) *^ s' + h);
      v' <- scale_q_p ((dotp b s') + h1);
      cmu <- scale_p_p (v' + (Zp.inzmod (scale (m_decode (if u then m1 else m0)) 1 (2 * ep - eq))));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return u';
   }
}.

(* Game 4 *)
module Game4(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b : Zq_vec;
      var b' : Zp_vec;
      var v' : Zp;
      var cmu : Zp;

      sd <$ dseed;
      _A <@ LRO.o(sd);
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZq_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      (* Skip: s' <$ dsmallZq_vec; *)
      b' <$ dZp_vec;
      v' <$ dZp;
      cmu <- scale_p_p (v' + (Zp.inzmod (scale (m_decode (if u then m1 else m0)) 1 (2 * ep - eq))));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return u';
   }
}.

(* Auxiliary Game with All Random Artifacts *)
module Auxiliary_Game(A : Adversary) = {
   proc main(u : bool) = {
      var u' : bool;
      var m0, m1 : plaintext;
      
      var sd : seed;
      var b : Zq_vec;
      var b' : Zp_vec;
      var cmu : Zp;
      
      sd <$ dseed;
      b <$ dZq_vec;
      
      (m0, m1) <@ A.choose(pk_encode (sd, b));
       
      b' <$ dZp_vec;
      cmu <$ dZp;
         
      u' <@ A.guess(c_encode (cmu, b'));

      return u';
  }
}.

(*
--------------------------------
 Adversaries
--------------------------------
*)
(* --- LWR-Related Adversaries --- *)
(* Adversary B0 against GMLWR constructed from adversary A distinguishing between Game0 and Game1 *)
module B0(A : Adversary) : Adv_GMLWR = {
   proc guess(sd : seed, b : Zp_vec) : bool = {
      var w, w' : bool;
      var m0, m1 : plaintext;
      
      var _A : Zq_mat;
      var s' : Zq_vec;
      var b' : Zp_vec;
      var v' : Zp;
      var cmw : Z2t;
      
      w <$ dbool;
      _A <@ LRO.o(sd);

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p ((trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmw <- scale_p_2t (v' + (Zp.inzmod (scale (m_decode (if w then m1 else m0)) 1 ep)));
      
      w' <@ A.guess(c_encode (cmw, b'));
      
      return (w = w');
   }
}.

(* Adversary B1 against XMLWR constructed from adversary A distinguishing between Game3 and Game4 *)
module B1(A : Adversary) : Adv_XMLWR = {
   proc guess(sd : seed, b : Zp_vec, a : Zq_vec, d : Zp) : bool =  {
      var w, w' : bool;
      var m0, m1 : plaintext;
      
      var cmw : Zp;
      
      w <$ dbool;

      (m0, m1) <@ A.choose(pk_encode (sd, a));

      cmw <- scale_p_p (d + (Zp.inzmod (scale (m_decode (if w then m1 else m0)) 1 (2 * ep - eq))));
      
      w' <@ A.guess(c_encode (cmw, b));
      
      return (w = w');
   }
}.

(* --- Other Adversaries --- *)
(* Adversary A2 against Game2 constructed from adversary A1 against Game1 *)
module A2(A1 : Adversary) : Adversary = {
   proc choose(pk : pkey) : plaintext * plaintext = {
      var m0, m1 : plaintext;
      
      (m0, m1) <@ A1.choose(pk);
      
      return (m0, m1);
   }

   proc guess(c : ciphertext) : bool = {
      var u' : bool;
      var c_dec : Zppq * Zp_vec;

      var cmu : Zppq;
      var b' : Zp_vec;
      var cmu' : Z2t;
      
      c_dec <- c_decode c;
      cmu <- c_dec.`1;
      b' <- c_dec.`2;

      cmu' <- scale_ppq_2t cmu; 
            
      u' <@ A1.guess(c_encode (cmu', b'));

      return u';
   }
}.

(* Adversary A3 against Game3 constructed from adversary A2 against Game2 *)
module A3(A2 : Adversary) : Adversary = {
   proc choose(pk : pkey) : plaintext * plaintext = {
      var pk_dec : seed * Zq_vec;
      var m0, m1 : plaintext;
      
      var sd : seed;
      var b : Zq_vec;
      var bp: Zp_vec;
      
      pk_dec <- pk_decode pk;
      sd <- pk_dec.`1;
      b <- pk_dec.`2;
      bp <- mod_p_Zq_vec b;
      
      (m0, m1) <@ A2.choose(pk_encode (sd, bp));
      
      return (m0, m1);
   }

   proc guess(c : ciphertext) : bool = {
      var u' : bool;
      var c_dec : Zp * Zp_vec;
      
      var cmu : Zp;
      var b' : Zp_vec;
      var cmu' : Zppq;
      
      c_dec <- c_decode c;
      cmu <- c_dec.`1;
      b' <- c_dec.`2;
      cmu' <- Zppq.inzmod (Zp.asint cmu); 
      
      u' <@ A2.guess(c_encode (cmu', b'));

      return u';
   }
}.


(*
--------------------------------
 Game-Based Security Proof 
--------------------------------
*)
(* Saber's INDCPA == Game 0 *)
lemma Equivalence_SaberINDCPA_Game0 &m (A <: Adversary{LRO}) :
      `| Pr[CPA_ROM(Saber_PKE_Scheme_ROM, A).main(true) @ &m : res] - Pr[CPA_ROM(Saber_PKE_Scheme_ROM, A).main(false) @ &m : res] |
      =
      `| Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res] |.
proof.
  have eq_T_T : Pr[CPA_ROM(Saber_PKE_Scheme_ROM, A).main(true) @ &m : res] = Pr[Game0(A).main(true) @ &m : res].
   byequiv => //.
   proc; inline *.
   call (_ : true); auto; call (_: true); auto.
   progress; smt.
  have eq_F_F: Pr[CPA_ROM(Saber_PKE_Scheme_ROM, A).main(false) @ &m : res] = Pr[Game0(A).main(false) @ &m : res].
   byequiv => //.
   proc; inline *.
   call (_ : true); auto; call (_: true); auto.
   progress; smt.
  by rewrite eq_T_T eq_F_F.
qed.

(* Game0 <> Game1 ==> GMLWR *)
lemma Distinguish_Game0_Game1_To_GMLWR &m  (A <: Adversary{LRO}) :
      `| `| Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res] | - 
         `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | | 
      <= 
      2%r * `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] |. 
proof.
  admit.
qed.

(* Game1 ==> Game2 *)
lemma Game1_To_Game2 &m (A <: Adversary{LRO}) :
      `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res]|
      =
      `| Pr[Game2( A2(A) ).main(true) @ &m : res] - Pr[Game2( A2(A) ).main(false) @ &m : res]|.
proof.
  have eq_T_T : Pr[Game1(A).main(true) @ &m : res] = Pr[Game2( A2(A) ).main(true) @ &m : res].
   byequiv => //.
   proc; inline *.
   wp; call (_ : true); auto; call (_ : true); auto.
   progress; smt. 
  have eq_F_F: Pr[Game1(A).main(false) @ &m : res] = Pr[Game2( A2(A) ).main(false) @ &m : res].
   byequiv => //.
   proc; inline *.
   wp; call (_ : true); auto; call (_ : true); auto.
   progress; smt. 
  by rewrite eq_T_T eq_F_F.
qed.

(* Game2 ==> Game3 *)
lemma Game2_To_Game3 &m (A <: Adversary{LRO}) :
      `| Pr[Game2(A).main(true) @ &m : res] - Pr[Game2(A).main(false) @ &m : res]|
      =
      `| Pr[Game3( A3(A) ).main(true) @ &m : res] - Pr[Game3( A3(A) ).main(false) @ &m : res]|.
proof.
  have eq_T_T : Pr[Game2(A).main(true) @ &m : res] = Pr[Game3( A3(A) ).main(true) @ &m : res].
   byequiv =>//.
   proc; inline *.
   wp; call(_ : true); wp; rnd; wp; call(_ : true); wp.
   rnd (fun (x : Zp_vec) => offunv (fun i => Zq.inzmod (Zp.asint x.[i])))
       (fun (x : Zq_vec) => mod_p_Zq_vec x).
  auto.
  progress.
  admit.
  have eq_F_F: Pr[Game2(A).main(false) @ &m : res] = Pr[Game3( A3(A) ).main(false) @ &m : res].
  admit.
  by rewrite eq_T_T eq_F_F.
qed.


(* Game3 <> Game4 ==> XMLWR *)
lemma Distinguish_Game3_Game4_To_XMLWR &m (A <: Adversary{LRO}) :
      `| `| Pr[Game3(A).main(true) @ &m : res] - Pr[Game3(A).main(false) @ &m : res] | - 
         `| Pr[Game4(A).main(true) @ &m : res] - Pr[Game4(A).main(false) @ &m : res] | | 
      <= 
      2%r * `| Pr[XMLWR( B1(A) ).main(true) @ &m : res] - Pr[XMLWR( B1(A) ).main(false) @ &m : res] |. 
proof.
  admit.
qed.


(* Auxiliary_Game Analysis *)
lemma Aux_Advantage_Zero &m  (A <: Adversary{LRO}) :
      `| Pr[Auxiliary_Game(A).main(true) @ &m : res] - Pr[Auxiliary_Game(A).main(false) @ &m : res] | = 0%r. 
proof.
  have eq_T_F:  Pr[Auxiliary_Game(A).main(true) @ &m : res] = Pr[Auxiliary_Game(A).main(false) @ &m : res]. 
   byequiv => //.
   proc.
   by call (_: true); auto; call(_ : true); auto.
  by rewrite eq_T_F. 
qed.

(* Game4 == Aux *)
lemma Equivalence_Game4_Aux &m  (A <: Adversary{LRO}) :
      `| Pr[Game4(A).main(true) @ &m : res] - Pr[Game4(A).main(false) @ &m : res] | 
      =
      `| Pr[Auxiliary_Game(A).main(true) @ &m : res] - Pr[Auxiliary_Game(A).main(false) @ &m : res] |.
proof.
  have xmx_0 : forall (x : Zp), x - x = Zp.zero. 
   by move=> xZp; rewrite -Zp.ZModule.addrC Zp.ZModule.addNr.
 
  have eq_T_T: Pr[Auxiliary_Game(A).main(true) @ &m : res] = Pr[Game4(A).main(true) @ &m : res].
   byequiv => //.
   proc; inline*.
   call (_ : true); wp. 
   rnd (fun (x : Zp) => x - Zp.inzmod(scale (m_decode m1{2}) 1 (2 * ep - eq)))  
       (fun (x : Zp) => x + Zp.inzmod(scale (m_decode m1{2}) 1 (2 * ep - eq))). 
   auto; call (_ : true); auto.
   rnd {2}; auto.
   progress.
    by apply dZq_mat_ll.
    pose x := (inzmod (scale (m_decode result_R.`2) 1 (2 * ep - eq)))%Zp.
    by rewrite -Zp.ZModule.addrA xmx_0 Zp.ZModule.addrC Zp.ZModule.add0r.
    pose x := (inzmod (scale (m_decode result_R.`2) 1 (2 * ep - eq)))%Zp.
    by rewrite -Zp.ZModule.addrA Zp.ZModule.addNr Zp.ZModule.addrC Zp.ZModule.add0r.
    by rewrite {1} H8 scale_p_p_id.
  
  have eq_F_F: Pr[Auxiliary_Game(A).main(false) @ &m : res] = Pr[Game4(A).main(false) @ &m : res].
   byequiv => //.
   proc; inline*.
   call (_ : true); wp. 
   rnd (fun (x : Zp) => x - Zp.inzmod(scale (m_decode m0{2}) 1 (2 * ep - eq)))  
       (fun (x : Zp) => x + Zp.inzmod(scale (m_decode m0{2}) 1 (2 * ep - eq))). 
   auto; call (_ : true); auto.
   rnd {2}; auto.
   progress.
    by apply dZq_mat_ll.
    pose x := (inzmod (scale (m_decode result_R.`2) 1 (2 * ep - eq)))%Zp.
    by rewrite -Zp.ZModule.addrA xmx_0 Zp.ZModule.addrC Zp.ZModule.add0r.
    pose x := (inzmod (scale (m_decode result_R.`2) 1 (2 * ep - eq)))%Zp.
    by rewrite -Zp.ZModule.addrA Zp.ZModule.addNr Zp.ZModule.addrC Zp.ZModule.add0r.
    by rewrite {1} H8 scale_p_p_id.
  
  by rewrite eq_T_T eq_F_F.
qed.


(* Game4 Analysis *)
lemma Game4_Advantage_Zero &m (A <: Adversary{LRO}) :
      `| Pr[Game4(A).main(true) @ &m : res] - Pr[Game4(A).main(false) @ &m : res] | = 0%r. 
proof.
   by rewrite (Equivalence_Game4_Aux &m A); apply (Aux_Advantage_Zero &m A).
qed.


(* Intelligibility Intermediate Result *)
lemma Difference_Advantage_Game1_Game4 &m (A <: Adversary{LRO}):
      `| `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | - 
         `| Pr[Game4( A3(A2(A)) ).main(true) @ &m : res] - Pr[Game4( A3(A2(A)) ).main(false) @ &m : res] | |
      <=
      2%r * `| Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] |.
proof. 
  rewrite (Game4_Advantage_Zero &m (A3(A2(A)))) /= (Game1_To_Game2 &m A) (Game2_To_Game3 &m (A2(A))).
  change (`| `|Pr[Game3( A3(A2(A)) ).main(true) @ &m : res] - Pr[Game3( A3(A2(A)) ).main(false) @ &m : res]| - 0%r| <=
           2%r * `|Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res]|).
  by rewrite -(Game4_Advantage_Zero &m (A3(A2(A)))) (Distinguish_Game3_Game4_To_XMLWR &m (A3(A2(A)))).
qed.


(* Final Result (Security Theorem) *)
lemma Saber_INDCPA_Security_Theorem &m (A <: Adversary{LRO}) :
      `| Pr[CPA_ROM(Saber_PKE_Scheme_ROM, A).main(true) @ &m : res] - Pr[CPA_ROM(Saber_PKE_Scheme_ROM, A).main(false) @ &m : res] |
      <=
      2%r * `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] | 
      +
      2%r * `| Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] |. 
proof.
  rewrite (Equivalence_SaberINDCPA_Game0 &m A).
  have eq_double_abs_min0: forall (x : real), `| x | = `| `| x | - 0%r |.
   by smt.
  rewrite {1} eq_double_abs_min0  -(Game4_Advantage_Zero &m (A3(A2(A)))).

  have apply_triangle_inequality: 
     `| `|Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res]| -
     `|Pr[Game4(A3(A2(A))).main(true) @ &m : res] - Pr[Game4(A3(A2(A))).main(false) @ &m : res]| | 
     <=
     `| `| Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res] | - 
        `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | |
     +
     `| `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | - 
        `| Pr[Game4( A3(A2(A)) ).main(true) @ &m : res] - Pr[Game4( A3(A2(A)) ).main(false) @ &m : res] | |.
   by rewrite (triangle_inequality 
                `| Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res] |
                `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] |
                `| Pr[Game4( A3(A2(A)) ).main(true) @ &m : res] - Pr[Game4( A3(A2(A)) ).main(false) @ &m : res] |).

  have adv01_adv14_lt_2advlwr: 
    `| `| Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res] | - 
       `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | |        
     +
    `| `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | - 
       `| Pr[Game4( A3(A2(A)) ).main(true) @ &m : res] - Pr[Game4( A3(A2(A)) ).main(false) @ &m : res] | |
    <=
    2%r * `|Pr[GMLWR( B0(A) ).main(true) @ &m : res] -  Pr[GMLWR( B0(A) ).main(false) @ &m : res]|
    +
    2%r * `|Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res]|.
   have double_lt: forall (x xg y yg: real), x <= xg => y <= yg => x + y <= xg + yg. 
    by smt.
   rewrite (double_lt
              `| `| Pr[Game0(A).main(true) @ &m : res] - Pr[Game0(A).main(false) @ &m : res] | -
                 `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | |
              (2%r * `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] |)
              `| `| Pr[Game1(A).main(true) @ &m : res] - Pr[Game1(A).main(false) @ &m : res] | -
                 `| Pr[Game4( A3(A2(A)) ).main(true) @ &m : res] - Pr[Game4( A3(A2(A)) ).main(false) @ &m : res] | |
              (2%r * `| Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] |)).
    by rewrite (Distinguish_Game0_Game1_To_GMLWR &m A).
    by rewrite (Difference_Advantage_Game1_Game4 &m A).

  by smt.
qed.
