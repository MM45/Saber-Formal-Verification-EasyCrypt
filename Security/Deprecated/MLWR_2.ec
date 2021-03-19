prover ["Alt-Ergo"].

(*
----------------------------------- 
 Require/Import EasyCrypt Theories
-----------------------------------
*)
require import AllCore Distr DBool.
require (*--*) Matrix PKE ROM.

(*
--------------------------------
 Definitions and Initialization
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

(* --- Types, Operators and Distributions --- *)
(* -- Rq = Zq[X] / (X^n + 1) -- *)
type Rq.

clone import Ring.ComRing as Rq with type t <- Rq.

clone MFinite as DRq with 
    type t <- Rq,
    op Support.card <- q ^ n.

op dRq: Rq distr = DRq.dunifin. (* Uniform Distribution over Rq *)

(* Vectors and Matrices over Rq*)
clone Matrix as Mat_Rq with 
  type R <- Rq,
  op size <- l.

type Rq_vec = Mat_Rq.vector.
type Rq_mat = Mat_Rq.Matrix.matrix.

op dRq_vec = Mat_Rq.Matrix.dvector dRq. (* Uniform Distribution over Vectors of Rq *)
op dRq_mat = Mat_Rq.Matrix.dmatrix dRq. (* Uniform Distribution over Matrices of Rq *)

op [lossless] dsmallRq: Rq distr. (* CBD over Rq *)
op dsmallRq_vec = Mat_Rq.Matrix.dvector dsmallRq. (* CBD over Vectors of Rq *)

(* -- Rp = Zp[X] / (X^n + 1) -- *)
type Rp.

clone import Ring.ComRing as Rp with type t <- Rp.

clone MFinite as DRp with 
  type t <- Rp,
  op Support.card = p ^ n.

op dRp : Rp distr = DRp.dunifin. (* Uniform Distribution over Rp*)

(* Vectors over Rp*)
clone Matrix as Mat_Rp with 
  type R <- Rp,
  op size <- l.
  
type Rp_vec = Mat_Rp.vector.

op dRp_vec = Mat_Rp.Matrix.dvector dRp. (* Uniform Distribution over Vectors of Rp *)
  
(* -- Rppq = Zppq[X] / (X^n + 1) -- *)
type Rppq.

clone import Ring.ComRing as Rppq with type t <- Rppq.

(* -- R2t = Z2t[X] / (X^n + 1) -- *)
type R2t.

clone import Ring.ComRing as R2t with type t <- R2t.

(* -- R2 = Z2[X] / (X^n + 1) -- *)
type R2.

clone import Ring.ComRing as R2 with type t <- R2.

(* - Properties - *)
(* Vector distribution has same properties as the distribution of the vector's elements *)
lemma dRq_vec_ll: is_lossless dRq_vec.
proof. apply Mat_Rq.Matrix.dvector_ll; rewrite /dRq; apply /DRq.dunifin_ll. qed.

lemma dRq_vec_uni: is_uniform dRq_vec.
proof. apply /Mat_Rq.Matrix.dvector_uni; rewrite /dRq; apply /DRq.dunifin_uni. qed.

lemma dRq_vec_fu: is_full dRq_vec.
proof. apply /Mat_Rq.Matrix.dvector_fu; rewrite /dRq; apply /DRq.dunifin_fu. qed.

lemma dRp_vec_ll: is_lossless dRp_vec.
proof. apply /Mat_Rp.Matrix.dvector_ll; rewrite /dRp; apply /DRp.dunifin_ll. qed.

lemma dRp_vec_uni: is_uniform dRp_vec.
proof. apply /Mat_Rp.Matrix.dvector_uni; rewrite /dRp; apply /DRp.dunifin_uni. qed.

lemma dRp_vec_fu: is_full dRp_vec.
proof. apply /Mat_Rp.Matrix.dvector_fu; rewrite /dRp; apply /DRp.dunifin_fu. qed.

lemma dsmallRq_vec_ll: is_lossless dsmallRq_vec.
proof. apply /Mat_Rq.Matrix.dvector_ll /dsmallRq_ll. qed.

(* Matrix Distribution has same properties as the distribution of the matrix's elements *)
lemma dRq_mat_ll: is_lossless dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_ll; rewrite /dRq; apply /DRq.dunifin_ll. qed.

lemma dRq_mat_uni: is_uniform dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_uni; rewrite /dRq; apply /DRq.dunifin_uni. qed.

lemma dRq_mat_fu: is_full dRq_mat.
proof. apply /Mat_Rq.Matrix.dmatrix_fu; rewrite /dRq; apply /DRq.dunifin_fu. qed.

(* - Imports - *)
import Mat_Rq.
import Mat_Rp.

(* -- Cryptographic Types -- *)
type seed.
type pkey.
type skey.
type plaintext.
type ciphertext.

(* -- Operations -- *)

(* --- ROM --- *)
clone import ROM as MLWR_ROM with
   type in_t <- seed,
   type out_t <- Rq_mat,
   op dout <- fun (sd: seed) => dRq_mat,
   type d_in_t <- unit,
   type d_out_t <- bool.

import Lazy.

(* --- PKE --- *)
clone import PKE as General_Saber_PKE with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

module General_Saber_PKE_Scheme : Scheme = {
   proc kg() : pkey * skey = {
      
   }

   proc enc(pk: pkey, m: plaintext) : ciphertext = {
      
   }

   proc dec(sk: skey, c: ciphertext) : plaintext = {
   
   }
}.


