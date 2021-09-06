pragma Goals:printall.

(*
----------------------------------- 
 Require/Import Theories
-----------------------------------
*)
(* --- Built-in --- *)
require import AllCore Distr DBool ZModP IntDiv StdOrder.
require (*--*) Matrix PKE.

(* --- Local --- *)
require import SaberZqPreliminaries.
(*---*) import Zq Zp Zppq Z2t Z2.
(*---*) import Mat_Zq Mat_Zp.

(*
----------------------------------
 Saber PKE Scheme
----------------------------------
*)
(* --- General --- *)
clone import PKE as Saber_PKE with
  type pkey <- pkey,
  type skey <- skey,
  type plaintext <- plaintext,
  type ciphertext <- ciphertext.

(* --- Actual --- *)
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
      v <- (dotp b' (mod_p_Zq_vec s)) + (Zp.inzmod (Zq.asint h1));
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
  have ->: Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] = Pr[Game0(A).main() @ &m : res].
   byequiv => //.
   proc; inline *. 
   swap {1} 7 -6.
   call (_ : true); auto; call (_: true); auto.
   progress; first do! congr; by rewrite pk_enc_dec_inv. 
    by case (bL); case (result_R0).
  by reflexivity.
qed.

(* Game0 <> Game1 ==> GMLWR *)
lemma Distinguish_Game0_Game1_To_GMLWR &m  (A <: Adversary) :
      `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
      = 
      `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] |. 
proof.
  have ->: Pr[Game0(A).main() @ &m : res] =  Pr[GMLWR( B0(A) ).main(false) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondf {2} 4.
    by move=> &m0; auto.
   swap {2} 7 -6; wp.
   by call (_ : true); auto; call (_: true); auto.
  have ->: Pr[Game1(A).main() @ &m : res] =  Pr[GMLWR( B0(A) ).main(true) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondt {2} 4.
    by move=> &m0; auto.
   swap {2} 7 -6; wp.
   call (_ : true); auto; call (_: true); auto; rnd {2}; auto.
   by progress; apply dsmallZq_vec_ll.
  by apply RealOrder.distrC.
qed.


(* Game1 ==> Game2 *)
lemma Game1_To_Game2 &m (A <: Adversary) :
      `| Pr[Game1(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game2( A2(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
  have ->: Pr[Game1(A).main() @ &m : res] = Pr[Game2( A2(A) ).main() @ &m : res].
   byequiv => //.
   proc; inline *.
   wp; call (_ : true); auto; call (_ : true); auto.
   by progress; do! congr; rewrite c_enc_dec_inv; first rewrite scale_comp_p_ppq_2t.  
  by reflexivity.
qed.

(* Game2 ==> Game3 *)
lemma Game2_To_Game3 &m (A <: Adversary) :
      `| Pr[Game2(A).main() @ &m : res] - 1%r / 2%r |
      =
      `| Pr[Game3( A3(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
  have ->: Pr[Game2(A).main() @ &m : res] = Pr[Game3( A3(A) ).main() @ &m : res].
   byequiv => //.
   proc; inline *.
   wp; call (_ : true); auto; call (_ : true); wp.
   (* What functions to use here... *)
   admit.
  by reflexivity.
qed.


(* Game3 <> Game4 ==> XMLWR *)
lemma Distinguish_Game3_Game4_To_XMLWR &m (A <: Adversary) :
      `| Pr[Game3(A).main() @ &m : res] - Pr[Game4(A).main() @ &m : res] |
      = 
      `| Pr[XMLWR( B1(A) ).main(true) @ &m : res] - Pr[XMLWR( B1(A) ).main(false) @ &m : res] |. 
proof.
  have ->: Pr[Game3(A).main() @ &m : res] =  Pr[XMLWR( B1(A) ).main(false) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondf {2} 4.
    by move=> &m0; auto.
   rcondf {2} 6.
    by move=> &m0; auto.
   swap {2} 11 -10; swap {1} 5 3; swap {2} 6 -2; wp.
   by sim.
  have ->: Pr[Game4(A).main() @ &m : res] =  Pr[XMLWR( B1(A) ).main(true) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondt {2} 4.
    by move=> &m0; auto.
   rcondt {2} 6.
    by move=> &m0; auto.
   swap {2} 11 -10; swap {1} 5 2; swap {2} 6 -1; wp.
   sim; rnd {2}; auto.
   by  progress; apply dsmallZq_vec_ll.
  by apply RealOrder.distrC.
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
  have ->: Pr[Game4(A).main() @ &m : res] = Pr[Auxiliary_Game(A).main() @ &m : res].
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
  by reflexivity.    
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
