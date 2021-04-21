(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr DBool ZModP IntDiv StdOrder.
(*---*) import RealOrder.

(* --- Local --- *)
require import SaberRqPreliminaries.
(*---*) import Mat_Rq Mat_Rp.
(*---*) import Rq Rp.
(*---*) import Rq.ComRing Rp.ComRing.
(*---*) import Saber_PKE.

(* ----------------------------------- *)
(*  Adversary Prototypes               *)
(* ----------------------------------- *)

module type Adv_GMLWR = {
   proc guess(sd : seed, b : Rp_vec) : bool
}.

module type Adv_XMLWR = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool
}.

(* ----------------------------------- *)
(*  Games                              *)
(* ----------------------------------- *)

(* --- MLWR-Related Games --- *)
(* GMLWR Game *)
module GMLWR(A : Adv_GMLWR) = {
   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleRqv2Rpv (_A *^ s + h);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.

(* XMLWR Game *)
module XMLWR(A : Adv_XMLWR) = {
   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var a : Rq_vec;
      var d : Rp;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleRqv2Rpv ((trmx _A) *^ s + h);
      }
      
      a <$ dRq_vec;

      if (u) {
         d <$ dRp;
      } else {
         d <- scaleRq2Rp ((dotp a s) + h1);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.

(* --- Game Sequence --- *)
(* Game 0 *)
module Game0(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var cmu : R2t;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      b <- scaleRqv2Rpv (_A *^ s + h);

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2R2t (v' + (shl_enc (m_decode (if u then m1 else m0)) (ep - 1)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 1 *)
module Game1(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var cmu : R2t;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRp_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2R2t (v' + (shl_enc (m_decode (if u then m1 else m0)) (ep - 1)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 2 *)
module Game2(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var cmu : Rppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRp_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2Rppq (v' + (shl_enc (m_decode (if u then m1 else m0)) (ep - 1)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 3 *)
module Game3(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var cmu : Rp;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRq_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- scaleRq2Rp ((dotp b s') + h1);
      cmu <- scaleRp2Rp (v' + (shl_enc (m_decode (if u then m1 else m0)) (2 * ep - eq - 1)));
   
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 4 *)
module Game4(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var cmu : Rp;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRq_vec;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      (* Skip: s' <$ dsmallRq_vec; *)
      b' <$ dRp_vec;
      v' <$ dRp;
      cmu <- scaleRp2Rp (v' + (shl_enc (m_decode (if u then m1 else m0)) (2 * ep - eq - 1)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Auxiliary Game with All Random Artifacts *)
module Auxiliary_Game(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;
      
      var sd : seed;
      var b : Rq_vec;
      var b' : Rp_vec;
      var cmu : Rp;
      
      sd <$ dseed;
      b <$ dRq_vec;
      
      (m0, m1) <@ A.choose(pk_encode (sd, b));
       
      b' <$ dRp_vec;
      cmu <$ dRp;
         
      u' <@ A.guess(c_encode (cmu, b'));
      
      u <$ dbool;

      return (u = u');
  }
}.

(* ----------------------------------- *)
(*  Adversaries                        *)
(* ----------------------------------- *)

(* --- MLWR-Related Adversaries --- *)
(* Adversary B0 Against GMLWR, Constructed from Adversary A Distinguishing Between Game0 and Game1 *)
module B0(A : Adversary) : Adv_GMLWR = {
   proc guess(sd : seed, b : Rp_vec) : bool = {
      var w, w' : bool;
      var m0, m1 : plaintext;
      
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var cmw : R2t;
      
      w <$ dbool;

      _A <- gen sd;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmw <- scaleRp2R2t (v' + (shl_enc (m_decode (if w then m1 else m0)) (ep - 1)));
      
      w' <@ A.guess(c_encode (cmw, b'));
      
      return (w = w');
   }
}.

(* Adversary B1 Against XMLWR, Constructed from Adversary A Distinguishing between Game3 and Game4 *)
module B1(A : Adversary) : Adv_XMLWR = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool =  {
      var w, w' : bool;
      var m0, m1 : plaintext;
      
      var cmw : Rp;
      
      w <$ dbool;

      (m0, m1) <@ A.choose(pk_encode (sd, a));

      cmw <- scaleRp2Rp (d + (shl_enc (m_decode (if w then m1 else m0)) (2 * ep - eq - 1)));
      
      w' <@ A.guess(c_encode (cmw, b));
      
      return (w = w');
   }
}.

(* --- Other Adversaries --- *)
(* Adversary A2 Against Game2, Constructed from Adversary A1 Against Game1 *)
module A2(A1 : Adversary) : Adversary = {
   proc choose(pk : pkey) : plaintext * plaintext = {
      var m0, m1 : plaintext;
      
      (m0, m1) <@ A1.choose(pk);
      
      return (m0, m1);
   }

   proc guess(c : ciphertext) : bool = {
      var u' : bool;
      var c_dec : Rppq * Rp_vec;

      var cmu : Rppq;
      var b' : Rp_vec;
      var cmu' : R2t;
      
      c_dec <- c_decode c;
      cmu <- c_dec.`1;
      b' <- c_dec.`2;

      cmu' <- scaleRppq2R2t cmu; 
            
      u' <@ A1.guess(c_encode (cmu', b'));

      return u';
   }
}.

(* Adversary A3 Against Game3, Constructed from Adversary A2 Against Game2 *)
module A3(A2 : Adversary) : Adversary = {
   proc choose(pk : pkey) : plaintext * plaintext = {
      var pk_dec : seed * Rq_vec;
      var m0, m1 : plaintext;
      
      var sd : seed;
      var b : Rq_vec;
      var bp: Rp_vec;
      
      pk_dec <- pk_decode pk;
      sd <- pk_dec.`1;
      b <- pk_dec.`2;
      bp <- Rqv2Rpv b;
      
      (m0, m1) <@ A2.choose(pk_encode (sd, bp));
      
      return (m0, m1);
   }

   proc guess(c : ciphertext) : bool = {
      var u' : bool;
      var c_dec : Rp * Rp_vec;
      
      var cmu : Rp;
      var b' : Rp_vec;
      var cmu' : Rppq;
      
      c_dec <- c_decode c;
      cmu <- c_dec.`1;
      b' <- c_dec.`2;
      cmu' <- Rp2Rppq cmu; 
      
      u' <@ A2.guess(c_encode (cmu', b'));

      return u';
   }
}.

(* -- Properties -- *)
axiom Adv_CPA_choose_ll (A <: Adversary) : islossless A.choose.
axiom Adv_CPA_guess_ll (A <: Adversary) : islossless A.guess.
axiom Adv_GMLWR_ll (A <: Adv_GMLWR) : islossless A.guess.
axiom Adv_XMLWR_ll (A <: Adv_XMLWR) : islossless A.guess.

(* ----------------------------------- *)
(*  Game-Based Security Proof          *)
(* ----------------------------------- *)

(* Saber's INDCPA == Game 0 *)
lemma Equivalence_SaberINDCPA_Game0 &m (A <: Adversary) :
      `| Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game0(A).main() @ &m : res] - 1%r /2%r |.
proof.
have -> //: Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] = Pr[Game0(A).main() @ &m : res].
+ byequiv => //.
  proc; inline *. 
  swap {1} 7 -6.
  call (_ : true); auto; call (_: true); auto.
  progress; first do! congr; by rewrite pk_enc_dec_inv.
  - by rewrite (eq_sym result_R0 bL).
qed.

(* Game0 <> Game1 ==> GMLWR *)
lemma Distinguish_Game0_Game1_To_GMLWR &m  (A <: Adversary) :
      `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
      = 
      `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] |. 
proof.
have ->: Pr[Game0(A).main() @ &m : res] =  Pr[GMLWR( B0(A) ).main(false) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondf {2} 4.
  - by move=> &m0; auto.
  swap {2} 7 -6; wp.
  by call (_ : true); auto; call (_: true); auto.
have ->: Pr[Game1(A).main() @ &m : res] =  Pr[GMLWR( B0(A) ).main(true) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondt {2} 4.
  - by move=> &m0; auto.
  swap {2} 7 -6; wp.
  call (_ : true); auto; call (_: true); auto; rnd {2}; auto.
  by progress; apply dsmallRq_vec_ll.
by apply distrC.
qed.

(* Game1 ==> Game2 *)
lemma Game1_To_Game2 &m (A <: Adversary) :
      `| Pr[Game1(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game2( A2(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game1(A).main() @ &m : res] = Pr[Game2( A2(A) ).main() @ &m : res].
+ byequiv => //.
  proc; inline *.
  wp; call (_ : true); auto; call (_ : true); auto.
  by progress; do! congr; rewrite c_enc_dec_inv; 1: rewrite scaleRp2Rppq2R2t_comp.  
qed.

(*
===========================================================================
START TEST
===========================================================================
*)

(* Game 2.5 *)
module Game25(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var bq : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var cmu : Rppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      bq <$ dRq_vec;
      b <- Rqv2Rpv bq;

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2Rppq (v' + (shl_enc (m_decode (if u then m1 else m0)) (ep - 1)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

pragma Goals:printall.
lemma Game25_To_Game3 &m (A <: Adversary) :
      `| Pr[Game25(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game3( A3(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game25(A).main() @ &m : res] = Pr[Game3( A3(A) ).main() @ &m : res].
byequiv => //.
proc; inline *.
auto; call(_ : true); auto; call(_ : true); auto.
progress. 
+ by rewrite pk_enc_dec_inv. 
+ rewrite c_enc_dec_inv scaleRp2Rp_id //=. 
  congr.
  rewrite &(pw_eq) // cmu_red23.
  do 2! congr.
  by rewrite eq_sym (Rq2Rp_DM (dotp bqL s'L) h1) Rq2Rp_DotDl.
qed.

require import DMap.

clone import DMapSampling with
   type t1 <- Rq_vec,
   type t2 <- Rp_vec.

(* Game 2.4 *)
module Game24(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var cmu : Rppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <@ S.sample(dRq_vec, Rqv2Rpv);

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2Rppq (v' + (shl_enc (m_decode (if u then m1 else m0)) (ep - 1)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.

(* Game 2.6 *)
module Game26(A : Adversary) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : plaintext;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var bq : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var cmu : Rppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <@ S.map(dRq_vec, Rqv2Rpv);

      (m0, m1) <@ A.choose(pk_encode (sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2Rppq (v' + (shl_enc (m_decode (if u then m1 else m0)) (ep - 1)));
      
      u' <@ A.guess(c_encode (cmu, b'));

      return (u = u');
   }
}.


lemma Game2_To_Game24 &m (A <: Adversary) :
      `| Pr[Game2(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game24(A).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game2(A).main() @ &m : res] = Pr[Game24(A).main() @ &m : res].
byequiv => //.
proc; inline *.
auto; call(_ : true); auto; call(_ : true); auto.
progress.
by rewrite dRqv2dRpv.
rewrite dRqv2dRpv. apply /(is_fullP dRp_vec) /dRp_vec_fu.
qed.

lemma Game24_To_Game26 &m (A <: Adversary) :
      `| Pr[Game24(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game26(A).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game24(A).main() @ &m : res] = Pr[Game26(A).main() @ &m : res].
byequiv => //.
proc. auto; call(_ : true); auto; call(_ : true). call (_ : ={d, f} ==> ={res}). rewrite sample.
auto.
qed.

lemma Game26_To_Game25 &m (A <: Adversary) :
      `| Pr[Game26(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game25(A).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game26(A).main() @ &m : res] = Pr[Game25(A).main() @ &m : res].
byequiv => //.
proc. inline *.
auto; call(_ : true); auto; call(_ : true); auto.
qed.

(* ======================================================================= *)

(* Game2 ==> Game3 *)
lemma Game2_To_Game3 &m (A <: Adversary) :
      `| Pr[Game2(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game3( A3(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game2(A).main() @ &m : res] = Pr[Game3( A3(A) ).main() @ &m : res].
+ byequiv => //.
  proc; inline *.
  wp; call (_ : true); auto; call (_ : true); wp.
  (* What functions to use here ... *)  
  rnd (fun (pv : Rp_vec) => Rpv2Rqv pv)
      (fun (pv : Rq_vec) => Rqv2Rpv pv).
  auto; progress. 
  - admit. 
  - admit.
  - by apply /(is_fullP dRq_vec) /dRq_vec_fu.
  - by rewrite Rpv2Rqv_Rqv2Rpv_inv.
  - by rewrite pk_enc_dec_inv /= Rpv2Rqv_Rqv2Rpv_inv.
  - rewrite c_enc_dec_inv scaleRp2Rp_id //=; congr.
    rewrite &(pw_eq) // cmu_red23 eq_sym; congr. 
    by rewrite (Rq2Rp_DM (dotp (Rpv2Rqv bL) s'L) h1) Rq2Rp_DotDl Rpv2Rqv_Rqv2Rpv_inv.
qed.

(* Game3 <> Game4 ==> XMLWR *)
lemma Distinguish_Game3_Game4_To_XMLWR &m (A <: Adversary) :
      `| Pr[Game3(A).main() @ &m : res] - Pr[Game4(A).main() @ &m : res] |
      = 
      `| Pr[XMLWR( B1(A) ).main(true) @ &m : res] - Pr[XMLWR( B1(A) ).main(false) @ &m : res] |. 
proof.
have ->: Pr[Game3(A).main() @ &m : res] =  Pr[XMLWR( B1(A) ).main(false) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondf {2} 4.
  - by move => &m0; auto.
  rcondf {2} 6.
  - by move => &m0; auto.
  swap {2} 11 -10; swap {1} 5 3; swap {2} 6 -2; wp.
  by sim.
have ->: Pr[Game4(A).main() @ &m : res] =  Pr[XMLWR( B1(A) ).main(true) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondt {2} 4.
  - by move => &m0; auto.
  rcondt {2} 6.
  - by move => &m0; auto.
  swap {2} 11 -10; swap {1} 5 2; swap {2} 6 -1; wp.
  sim; rnd {2}; auto.
  by progress; apply dsmallRq_vec_ll.
by apply distrC.
qed.

(* Auxiliary_Game Analysis *)
lemma Aux_Prob_Half &m  (A <: Adversary) :
      Pr[Auxiliary_Game(A).main() @ &m : res]  = 1%r / 2%r. 
proof.
byphoare => //.
proc.
rnd. 
call (_: true); [apply (Adv_CPA_guess_ll A) | auto].
call(_ : true); [apply (Adv_CPA_choose_ll A) | auto].
by progress; [apply dseed_ll        |
              apply dRq_vec_ll      |
              apply dRp_vec_ll      |
              apply Rp.dpolyXnD1_ll |
              apply dbool1E].
qed.

lemma Equivalence_Game4_Aux &m  (A <: Adversary) :
      `| Pr[Game4(A).main() @ &m : res] - 1%r /2%r | 
      =
      `| Pr[Auxiliary_Game(A).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game4(A).main() @ &m : res] = Pr[Auxiliary_Game(A).main() @ &m : res].
+ byequiv => //. 
  proc; inline *.
  swap {2} 7 -6.
  call (_ : true); wp.
  rnd (fun (x : Rp) => x + (shl_enc (m_decode (if u{1} then m1{1} else m0{1})) (2 * ep - eq - 1)))  
      (fun (x : Rp) => x - (shl_enc (m_decode (if u{1} then m1{1} else m0{1})) (2 * ep - eq - 1))).
  auto; call(_ : true); auto.
  progress.
  - pose x := shl_enc (m_decode (if uL then result_R.`2 else result_R.`1)) (2 * ep - eq - 1).
    by rewrite -addrA addNr addrC add0r. 
  - by apply /rnd_funi /Rp.dpolyXnD1_funi.
  - by apply /is_fullP /Rp.dpolyXnD1_fu.
  - pose x := shl_enc (m_decode (if uL then result_R.`2 else result_R.`1)) (2 * ep - eq - 1).
    have xx_0: forall (x : Rp), x + (- x) = Rp.zeroXnD1.
    * by move => x0; rewrite -(addrN x0).
    by rewrite -addrA (xx_0 x) addrC add0r.
  - by rewrite scaleRp2Rp_id.  
qed.

(* Game4 Analysis *)
lemma Game4_Prob_Half &m (A <: Adversary) :
      Pr[Game4(A).main() @ &m : res] = 1%r / 2%r. 
proof.
  rewrite -(Real.RField.subr_eq0 Pr[Game4(A).main() @ &m : res] (1%r / 2%r)) -RealOrder.normr0P.
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
have:
     `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
     +
     `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
     <=
     `| Pr[GMLWR(B0(A)).main(true) @ &m : res] - Pr[GMLWR(B0(A)).main(false) @ &m : res] | 
     +
     `| Pr[XMLWR(B1(A3(A2(A)))).main(true) @ &m : res] - Pr[XMLWR(B1(A3(A2(A)))).main(false) @ &m : res] |.
+ by apply ler_add; [rewrite (Distinguish_Game0_Game1_To_GMLWR &m A) |
                     rewrite -(Difference_Game1_Game4_To_XMLWR &m A) ].
move: (ler_dist_add (Pr[Game1(A).main() @ &m : res]) 
                    (Pr[Game0(A).main() @ &m : res])
                    (Pr[Game4( A3(A2(A)) ).main() @ &m : res])).
by apply ler_trans.  
qed.
