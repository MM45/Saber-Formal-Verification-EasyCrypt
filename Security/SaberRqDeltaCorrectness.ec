(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr ZModP IntDiv StdOrder.

(* --- Local --- *)
require import SaberRqPreliminaries.
(*---*) import Mat_Rp Mat_Rq.
(*---*) import Rp Rq.
(*---*) import Zp Zq.

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

