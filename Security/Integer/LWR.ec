prover ["Alt-Ergo"].

pragma Goals:printall.

(*
----------------------------------- 
 Require/Import EasyCrypt Theories
-----------------------------------
*)
require import AllCore Distr DBool ZModP IntDiv StdOrder.
require (*--*) Poly Matrix PKE ROM.

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
(* -- Assumptions/Properties -- *)
(*axiom exp_relation: 0 < et + 1 < ep < eq.*)
axiom gt0_et1: 0 < et + 1.
axiom gtet_ep: et + 1 < ep.
axiom gtep_eq: ep < eq.
axiom sec_assumption: eq - ep <= ep - et - 1. (* q %/ p <= p %/ 2*t. *)
axiom module_dimension_ge1: 1 <= l.

lemma et_ge0: 0 <= et by smt.
lemma ep_ge2: 2 <= ep by smt.
lemma eq_ge3: 3 <= eq by smt.

lemma t_div_p: t %| p by rewrite dvdzP /t /p; exists (2^(ep - et)); rewrite -exprD_nneg; smt.
lemma p_div_q: p %| q by rewrite dvdzP /p /q; exists (2^(eq - ep)); rewrite -exprD_nneg; smt.
lemma t_div_q: t %| q by apply /(dvdz_trans p t q) /p_div_q /t_div_p.

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

(* (x %/ a) %/ b == x %/ (a * b) *)
lemma scale_split (x ea eab eb : int):
      0 <= eb => eb <= eab => eab <= ea =>
      scale x ea eb = scale (scale x ea eab) eab eb. 
proof. admit. qed.

lemma scale_split_p_ppq_2t (x : Zp):
      scale_p_2t x = scale_ppq_2t (scale_p_ppq x).
proof. admit. qed.

lemma scale_id (x ea eb : int) : ea = eb => scale x ea eb = x.
proof. by move=> eq_eaeb; rewrite /scale /shr eq_eaeb addzN expr0. qed.

lemma scale_p_p_id (x : Zp) : scale_p_p x = x.
proof. by rewrite /scale_p_p scale_id; [trivial | rewrite asintK]. qed.

(* --- PKE --- *)
clone import PKE as Saber_PKE with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

(*
-----------------
 Saber PKE Scheme
-----------------
*)
module Saber_PKE_Scheme : Scheme = {
   proc kg() : pkey * skey = {
      var sd: seed;
      var _A: Zq_mat;
      var s: Zq_vec;
      var b: Zp_vec;
      
      sd <$ dseed;
      _A <- gen sd;
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
      _A <- gen sd;
      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p ((trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cm <- scale_p_2t (v' + (Zp.inzmod (shl (Z2.asint m_dec) (ep - 1))));
      
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
      m' <- scale_p_2 (v - (Zp.inzmod (shl (Z2t.asint cm) (ep - et -1))) + (Zp.inzmod (Zq.asint h2)));
      
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

(* --- LWR-Related Games --- *)
module GMLWR(A : Adv_GMLWR) = {
   proc main(u : bool) = {
      var u' : bool;
      var sd : seed;
      var _A : Zq_mat;
      var s : Zq_vec;
      var b : Zp_vec;

      sd <$ dseed;
      _A <- gen sd;
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

      sd <$ dseed;
      _A <- gen sd;
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
   proc main() = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b, b' : Zp_vec;
      var v' : Zp;
      var cmu : Z2t;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallZq_vec;
      b <- scale_vec_q_p (_A *^ s + h);

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p (( trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmu <- scale_p_2t (v' + (Zp.inzmod (shl (Z2.asint (m_decode (if u then m1 else m0))) (ep - 1))));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 1 *)
module Game1(A : Adversary) = {
   proc main() = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b, b' : Zp_vec;
      var v' : Zp;
      var cmu : Z2t;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZp_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p (( trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmu <- scale_p_2t (v' + (Zp.inzmod (shl (Z2.asint (m_decode (if u then m1 else m0))) (ep - 1))));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 2 *)
module Game2(A : Adversary) = {
   proc main() = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b, b' : Zp_vec;
      var v' : Zp;
      var cmu : Zppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZp_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p ((trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmu <- scale_p_ppq (v' + (Zp.inzmod (shl (Z2.asint (m_decode (if u then m1 else m0))) (ep - 1))));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 3 *)
module Game3(A : Adversary) = {
   proc main() = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b : Zq_vec;
      var b' : Zp_vec;
      var v' : Zp;
      var cmu : Zp;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZq_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p (( trmx _A) *^ s' + h);
      v' <- scale_q_p ((dotp b s') + h1);
      cmu <- scale_p_p (v' + (Zp.inzmod (shl (Z2.asint (m_decode (if u then m1 else m0))) (2 * ep - eq - 1))));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 4 *)
module Game4(A : Adversary) = {
   proc main() = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Zq_mat;
      var s, s' : Zq_vec;
      var b : Zq_vec;
      var b' : Zp_vec;
      var v' : Zp;
      var cmu : Zp;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallZq_vec; *)
      b <$ dZq_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      (* Skip: s' <$ dsmallZq_vec; *)
      b' <$ dZp_vec;
      v' <$ dZp;
      cmu <- scale_p_p (v' + (Zp.inzmod (shl (Z2.asint (m_decode (if u then m1 else m0))) (2 * ep - eq - 1))));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Auxiliary Game with All Random Artifacts *)
module Auxiliary_Game(A : Adversary) = {
   proc main() = {
      var u, u' : bool;
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
      
      u <$ dbool;

      return (u = u');
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

      _A <- gen sd;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallZq_vec;
      b' <- scale_vec_q_p ((trmx _A) *^ s' + h);
      v' <- (dotp b (mod_p_Zq_vec s')) + (Zp.inzmod (Zq.asint h1));
      cmw <- scale_p_2t (v' + (Zp.inzmod (shl (Z2.asint (m_decode (if w then m1 else m0))) (ep - 1))));
      
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

      cmw <- scale_p_p (d + (Zp.inzmod (shl (Z2.asint (m_decode (if w then m1 else m0))) (2 * ep - eq - 1))));
      
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

(* -- Properties -- *)
axiom Adv_CPA_choose_ll (A <: Adversary) : islossless A.choose.
axiom Adv_CPA_guess_ll (A <: Adversary) : islossless A.guess.
axiom Adv_GMLWR_ll (A <: Adv_GMLWR) : islossless A.guess.
axiom Adv_XMLWR_ll (A <: Adv_XMLWR) : islossless A.guess.

(*
--------------------------------
 Game-Based Security Proof 
--------------------------------
*)
(* Saber's INDCPA == Game 0 *)
lemma Equivalence_SaberINDCPA_Game0 &m (A <: Adversary) :
      `| Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game0(A).main() @ &m : res] - 1%r /2%r |.
proof.
  have eq_games: Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] = Pr[Game0(A).main() @ &m : res].
   byequiv => //.
   proc; inline *. 
   swap {1} 7 -6.
   call (_ : true); auto; call (_: true); auto.
   progress; admit.
  by rewrite eq_games.
qed.

(* Game0 <> Game1 ==> GMLWR *)
lemma Distinguish_Game0_Game1_To_GMLWR &m  (A <: Adversary) :
      `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
      = 
      `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] |. 
proof.
  have eq_0_F: Pr[Game0(A).main() @ &m : res] =  Pr[GMLWR( B0(A) ).main(false) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondf {2} 4.
    by move=> &m0; auto.
   swap {2} 7 -6; wp.
   by call (_ : true); auto; call (_: true); auto.
  have eq_1_T: Pr[Game1(A).main() @ &m : res] =  Pr[GMLWR( B0(A) ).main(true) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondt {2} 4.
    by move=> &m0; auto.
   swap {2} 7 -6; wp.
   call (_ : true); auto; call (_: true); auto; rnd {2}; auto.
   by progress; apply dsmallZq_vec_ll.
  by rewrite eq_0_F eq_1_T; apply RealOrder.distrC.
qed.


(* Game1 ==> Game2 *)
lemma Game1_To_Game2 &m (A <: Adversary) :
      `| Pr[Game1(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game2( A2(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
  have eq_games : Pr[Game1(A).main() @ &m : res] = Pr[Game2( A2(A) ).main() @ &m : res].
   byequiv => //.
   proc; inline *.
   wp; call (_ : true); auto; call (_ : true); auto.
   progress; smt. 
  by rewrite eq_games.
qed.

(* Game2 ==> Game3 *)
lemma Game2_To_Game3 &m (A <: Adversary) :
      `| Pr[Game2(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game3( A3(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
  have eq_games : Pr[Game2(A).main() @ &m : res] = Pr[Game3( A3(A) ).main() @ &m : res].
   admit.
  by rewrite eq_games.
qed.


(* Game3 <> Game4 ==> XMLWR *)
lemma Distinguish_Game3_Game4_To_XMLWR &m (A <: Adversary) :
      `| Pr[Game3(A).main() @ &m : res] - Pr[Game4(A).main() @ &m : res] |
      = 
      `| Pr[XMLWR( B1(A) ).main(true) @ &m : res] - Pr[XMLWR( B1(A) ).main(false) @ &m : res] |. 
proof.
  have eq_3_F: Pr[Game3(A).main() @ &m : res] =  Pr[XMLWR( B1(A) ).main(false) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondf {2} 4.
    by move=> &m0; auto.
   rcondf {2} 6.
    by move=> &m0; auto.
   swap {2} 11 -10; swap {1} 5 3; swap {2} 6 -2; wp.
   by sim.
  have eq_4_T: Pr[Game4(A).main() @ &m : res] =  Pr[XMLWR( B1(A) ).main(true) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondt {2} 4.
    by move=> &m0; auto.
   rcondt {2} 6.
    by move=> &m0; auto.
   swap {2} 11 -10; swap {1} 5 2; swap {2} 6 -1; wp.
   sim; rnd {2}; auto.
   by  progress; apply dsmallZq_vec_ll.
  by rewrite eq_3_F eq_4_T; apply RealOrder.distrC.
qed.

(* Auxiliary_Game Analysis *)
lemma Aux_Prob_Half &m  (A <: Adversary) :
      Pr[Auxiliary_Game(A).main() @ &m : res]  = 1%r / 2%r. 
proof.
  byphoare => //.
  proc.
  rnd. 
  call (_: true); [ apply (Adv_CPA_guess_ll A) | auto ].
  call(_ : true); [ apply (Adv_CPA_choose_ll A) | auto ].
  by progress; [ apply dseed_ll | apply dZq_vec_ll | apply dZp_vec_ll | apply DZp.dunifin_ll | apply dbool1E ].
qed.

lemma Equivalence_Game4_Aux &m  (A <: Adversary) :
      `| Pr[Game4(A).main() @ &m : res] - 1%r /2%r | 
      =
      `| Pr[Auxiliary_Game(A).main() @ &m : res] - 1%r / 2%r |.
proof.
  have eq_games: Pr[Game4(A).main() @ &m : res] = Pr[Auxiliary_Game(A).main() @ &m : res].
   byequiv => //. 
   proc; inline *.
   swap {2} 7 -6.
   call (_ : true); wp.
   rnd (fun (x : Zp) => x + Zp.inzmod (shl (Z2.asint (m_decode (if u{1} then m1{1} else m0{1}))) (2 * ep - eq - 1)))  
       (fun (x : Zp) => x - Zp.inzmod (shl (Z2.asint (m_decode (if u{1} then m1{1} else m0{1}))) (2 * ep - eq - 1))).
   auto; call(_ : true); auto.
   progress.
    pose x := (Zp.inzmod (shl (Z2.asint (m_decode (if uL then result_R.`2 else result_R.`1))) (2 * ep - eq - 1))).
    by rewrite -Zp.ZModule.addrA Zp.ZModule.addNr Zp.ZModule.addrC Zp.ZModule.add0r.
    pose x := (Zp.inzmod (shl (Z2.asint (m_decode (if uL then result_R.`2 else result_R.`1))) (2 * ep - eq - 1))).
    have xx_0 : forall (x : Zp), x - x = Zp.zero.
     by move=> x0; rewrite -Zp.ZModule.addrC Zp.ZModule.addNr.
    by rewrite -Zp.ZModule.addrA xx_0 Zp.ZModule.addrC Zp.ZModule.add0r.
    by rewrite scale_p_p_id H7.
  by rewrite eq_games.    
qed.

(* Game4 Analysis *)
lemma Game4_Prob_Half &m (A <: Adversary) :
      Pr[Game4(A).main() @ &m : res] = 1%r / 2%r. 
proof.
  rewrite -(Real.RField.subr_eq0  Pr[Game4(A).main() @ &m : res]  (1%r / 2%r)) -RealOrder.normr0P.
  by rewrite (Equivalence_Game4_Aux &m A) (Aux_Prob_Half &m A).
qed.

(* Intelligibility Intermediate Result *)
lemma Difference_Game1_Game4_To_XMLWR &m (A <: Adversary):
      `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
      =
      `| Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] |.
proof. 
  by rewrite (Game4_Prob_Half &m (A3(A2(A)))) (Game1_To_Game2 &m A) (Game2_To_Game3 &m (A2(A))) 
            -(Game4_Prob_Half &m (A3(A2(A)))) (Distinguish_Game3_Game4_To_XMLWR &m (A3(A2(A)))).
qed.

(* Final Result (Security Theorem) *)
lemma Saber_INDCPA_Security_Theorem &m (A <: Adversary) :
      `| Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] - 1%r / 2%r |
      <=
      `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] | 
      +
      `| Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] |. 
proof.
  rewrite (Equivalence_SaberINDCPA_Game0 &m A) -(Game4_Prob_Half &m (A3(A2(A)))).

  have triangle_inequality: 
       `| Pr[Game0(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |  
       <=
       `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
       +
       `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |.
   by apply RealOrder.ler_dist_add.

  have intermediate_result:
       `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
       +
       `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
       <=
       `|Pr[GMLWR(B0(A)).main(true) @ &m : res] - Pr[GMLWR(B0(A)).main(false) @ &m : res]| 
       +
       `|Pr[XMLWR(B1(A3(A2(A)))).main(true) @ &m : res] - Pr[XMLWR(B1(A3(A2(A)))).main(false) @ &m : res]|.
   by apply /RealOrder.ler_add; [ rewrite (Distinguish_Game0_Game1_To_GMLWR &m A) |
                                  rewrite -(Difference_Game1_Game4_To_XMLWR &m A) ].

  by move: triangle_inequality intermediate_result; apply RealOrder.ler_trans.
qed.
