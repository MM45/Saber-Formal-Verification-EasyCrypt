(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr DBool ZModP IntDiv StdOrder.
(*---*) import RealOrder.

(* --- Local --- *)
require import SaberPKEPreliminaries.
(*---*) import Mat_Rq Mat_Rp.
(*---*) import Rq Rp.
(*---*) import Rq.ComRing Rp.ComRing.
(*---*) import Saber_PKE.
(*---*) import DMapRqv2Rpv.

(* ----------------------------------- *)
(*  Adversary Classes                  *)
(* ----------------------------------- *)

module type Adv_GMLWR = {
   proc guess(sd : seed, b : Rp_vec) : bool
}.

module type Adv_XMLWR = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool
}.

module type Adv_INDCPA = {
  proc choose(pk : seed * Rp_vec) : R2 * R2  
  proc guess(c : R2t * Rp_vec) : bool
}.

module type Adv_INDCPA_2 = {
  proc choose(pk : seed * Rp_vec) : R2 * R2  
  proc guess(c : Rppq * Rp_vec) : bool
}.

module type Adv_INDCPA_34 = {
  proc choose(pk : seed * Rq_vec) : R2 * R2  
  proc guess(c : Rp * Rp_vec) : bool
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
module Game0(A : Adv_INDCPA) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

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

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2R2t (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((cmu, b'));

      return (u = u');
   }
}.

(* Game 1 *)
module Game1(A : Adv_INDCPA) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

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

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2R2t (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((cmu, b'));

      return (u = u');
   }
}.

(* Game 2 *)
module Game2(A : Adv_INDCPA_2) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

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

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2Rppq (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((cmu, b'));

      return (u = u');
   }
}.

(* Auxiliary Game (Reduction 2-3): Game 2a *)
module Game2a(A : Adv_INDCPA_2) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

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
      b <@ Rqv2RpvSampl.sample(dRq_vec, Rqv2Rpv);

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2Rppq (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((cmu, b'));

      return (u = u');
   }
}.

(* Auxiliary Game (Reduction 2-3): Game 2b *)
module Game2b(A : Adv_INDCPA_2) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

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
      b <@ Rqv2RpvSampl.map(dRq_vec, Rqv2Rpv);

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmu <- scaleRp2Rppq (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((cmu, b'));

      return (u = u');
   }
}.

(* Game 3 *)
module Game3(A : Adv_INDCPA_34) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

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

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- scaleRq2Rp ((dotp b s') + h1);
      cmu <- v' + (scaleR22Rp_var (if u then m1 else m0) (2 * ep - eq - 1));
   
      u' <@ A.guess((cmu, b'));

      return (u = u');
   }
}.

(* Game 4 *)
module Game4(A : Adv_INDCPA_34) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

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

      (m0, m1) <@ A.choose((sd, b));

      (* Skip: s' <$ dsmallRq_vec; *)
      b' <$ dRp_vec;
      v' <$ dRp;
      cmu <- v' + (scaleR22Rp_var (if u then m1 else m0) (2 * ep - eq - 1));
      
      u' <@ A.guess((cmu, b'));

      return (u = u');
   }
}.

(* Auxiliary Game with All Random Artifacts *)
module Auxiliary_Game(A : Adv_INDCPA_34) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;
      
      var sd : seed;
      var b : Rq_vec;
      var b' : Rp_vec;
      var cmu : Rp;
      
      sd <$ dseed;
      b <$ dRq_vec;
      
      (m0, m1) <@ A.choose((sd, b));
       
      b' <$ dRp_vec;
      cmu <$ dRp;
         
      u' <@ A.guess((cmu, b'));
      
      u <$ dbool;

      return (u = u');
  }
}.

(* ----------------------------------- *)
(*  Adversaries                        *)
(* ----------------------------------- *)

(* --- MLWR-Related Adversaries --- *)
(* Adversary B0 Against GMLWR, Constructed from Adversary A Distinguishing Between Game0 and Game1 *)
module B0(A : Adv_INDCPA) : Adv_GMLWR = {
   proc guess(sd : seed, b : Rp_vec) : bool = {
      var w, w' : bool;
      var m0, m1 : R2;
      
      var _A : Rq_mat;
      var s' : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var cmw : R2t;
      
      w <$ dbool;

      _A <- gen sd;

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      cmw <- scaleRp2R2t (v' + (scaleR22Rp (if w then m1 else m0)));
      
      w' <@ A.guess((cmw, b'));
      
      return (w = w');
   }
}.

(* Adversary B1 Against XMLWR, Constructed from Adversary A Distinguishing between Game3 and Game4 *)
module B1(A : Adv_INDCPA_34) : Adv_XMLWR = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool =  {
      var w, w' : bool;
      var m0, m1 : R2;
      
      var cmw : Rp;
      
      w <$ dbool;

      (m0, m1) <@ A.choose((sd, a));

      cmw <- d + (scaleR22Rp_var (if w then m1 else m0) (2 * ep - eq - 1));
      
      w' <@ A.guess((cmw, b));
      
      return (w = w');
   }
}.

(* --- Other Adversaries --- *)
(* Adversary A2 Against Game2, Constructed from Adversary A1 Against Game1 *)
module A2(A1 : Adv_INDCPA) : Adv_INDCPA_2 = {
   proc choose(pk : seed * Rp_vec) : R2 * R2 = {
      var m0, m1 : R2;
      
      (m0, m1) <@ A1.choose(pk);
      
      return (m0, m1);
   }

   proc guess(c : Rppq * Rp_vec) : bool = {
      var u' : bool;
      
      var cmu : Rppq;
      var b' : Rp_vec;
      var cmu' : R2t;
      
      cmu <- c.`1;
      b' <- c.`2;

      cmu' <- scaleRppq2R2t cmu; 
            
      u' <@ A1.guess((cmu', b'));

      return u';
   }
}.

(* Adversary A3 Against Game3, Constructed from Adversary A2 Against Game2 *)
module A3(A2 : Adv_INDCPA_2) : Adv_INDCPA_34 = {
   proc choose(pk : seed * Rq_vec) : R2 * R2 = {
      var m0, m1 : R2;
      
      var sd : seed;
      var b : Rq_vec;
      var bp: Rp_vec;
      
      sd <- pk.`1;
      b <- pk.`2;
      bp <- Rqv2Rpv b;
      
      (m0, m1) <@ A2.choose((sd, bp));
      
      return (m0, m1);
   }

   proc guess(c : Rp * Rp_vec) : bool = {
      var u' : bool;
      
      var cmu : Rp;
      var b' : Rp_vec;
      var cmu' : Rppq;
      
      cmu <- c.`1;
      b' <- c.`2;
      cmu' <- Rp2Rppq cmu; 
      
      u' <@ A2.guess((cmu', b'));

      return u';
   }
}.

(* ----------------------------------- *)
(*  Game-Based Security Proof          *)
(* ----------------------------------- *)

section Game_Hopping.

(* -- Declare Adversary Against Game0 and Game1  -- *)
declare module Adv_01 <: Adv_INDCPA.

(* Saber's INDCPA <==> Game 0 *)
lemma Equivalence_SaberINDCPA_Game0 &m :
  `| Pr[CPA(Saber_PKE_Scheme, Adv_01).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game0(Adv_01).main() @ &m : res] - 1%r /2%r |.
proof.
have -> //: Pr[CPA(Saber_PKE_Scheme, Adv_01).main() @ &m : res] 
            = 
            Pr[Game0(Adv_01).main() @ &m : res].
+ byequiv => //.
  proc; inline *. 
  swap {1} 7 -6.
  call (_ : true); auto; call (_: true); auto => /> u _ sd _ s1 _ s2 _ u'.
  by rewrite (eq_sym u u').
qed.

(* Step 1: Game0 <> Game1 -- GMLWR *)
lemma Step_Distinguish_Game0_Game1_GMLWR &m :
  `| Pr[Game0(Adv_01).main() @ &m : res] - Pr[Game1(Adv_01).main() @ &m : res] |
  = 
  `| Pr[GMLWR( B0(Adv_01) ).main(true) @ &m : res] - Pr[GMLWR( B0(Adv_01) ).main(false) @ &m : res] |. 
proof.
have ->: Pr[Game0(Adv_01).main() @ &m : res] =  Pr[GMLWR( B0(Adv_01) ).main(false) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondf {2} 4.
  - by move=> &m0; auto.
  swap {2} 7 -6; wp.
  by call (_ : true); auto; call (_: true); auto.
have ->: Pr[Game1(Adv_01).main() @ &m : res] =  Pr[GMLWR( B0(Adv_01) ).main(true) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondt {2} 4.
  - by move=> &m0; auto.
  swap {2} 7 -6; wp.
  call (_ : true); auto; call (_: true); auto; rnd {2}; auto => /> *.
  by apply dsmallRq_vec_ll.
by apply distrC.
qed.

(* Step 2: Game1 -- Game2 *)
lemma Step_Game1_Game2 &m :
  `| Pr[Game1(Adv_01).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game2( A2(Adv_01) ).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game1(Adv_01).main() @ &m : res] = Pr[Game2( A2(Adv_01) ).main() @ &m : res].
+ byequiv => //.
  proc; inline *.
  wp; call (_ : true); auto; call (_ : true); auto => /> u _ sd _ b _ r s _.
  by rewrite scaleRp2Rppq2R2t_comp.  
qed.


(* Declare Adversary Against Game2  *)
declare module Adv_2 <: Adv_INDCPA_2.

(* Auxiliary Step (Reduction 2-3): Game2 -- Game2a *)
lemma AuxStep_Game2_Game2a &m :
  `| Pr[Game2(Adv_2).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game2a(Adv_2).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game2(Adv_2).main() @ &m : res] = Pr[Game2a(Adv_2).main() @ &m : res].
+ byequiv => //.
  proc; inline *.
  auto; call(_ : true); auto; call(_ : true); auto => />.
  by rewrite dRqv2dRpv.
qed.

(* Auxiliary Step (Reduction 2-3): Game2a -- Game2b *)
lemma AuxStep_Game2a_Game2b &m :
  `| Pr[Game2a(Adv_2).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game2b(Adv_2).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game2a(Adv_2).main() @ &m : res] = Pr[Game2b(Adv_2).main() @ &m : res].
+ byequiv => //.
  proc.
  by auto; call(_ : true); auto; call(_ : true); call sample; auto.
qed.

(* Auxiliary Step (Reduction 2-3): Game2b -- Game3 *)
lemma AuxStep_Game2b_Game3 &m :
  `| Pr[Game2b(Adv_2).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game3( A3(Adv_2) ).main() @ &m : res] - 1%r / 2%r |.
proof.
have -> //: Pr[Game2b(Adv_2).main() @ &m : res] = Pr[Game3( A3(Adv_2) ).main() @ &m : res].
+ byequiv => //.
  proc; inline *.
  auto; call(_ : true); auto; call(_ : true); auto => /> u _ sd _ x _ r s _.
  by rewrite eq_comp23; do 2! congr; rewrite -Rq2Rp_DG23.
qed.

(* Step 3: Game2 -- Game3 *)
lemma Step_Game2_Game3 &m :
  `| Pr[Game2(Adv_2).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game3( A3(Adv_2) ).main() @ &m : res] - 1%r / 2%r |.
proof.
by rewrite (AuxStep_Game2_Game2a &m) (AuxStep_Game2a_Game2b &m) (AuxStep_Game2b_Game3 &m).
qed.


(* Declare (Terminating) Adversary Against Game3 and Game4 *)
declare module Adv_34 <: Adv_INDCPA_34.
declare axiom Adv_34_choose_ll : islossless Adv_34.choose.
declare axiom Adv_34_guess_ll : islossless Adv_34.guess.

(* Step 4: Game3 <> Game4 -- XMLWR *)
lemma Step_Distinguish_Game3_Game4_XMLWR &m :
  `| Pr[Game3(Adv_34).main() @ &m : res] - Pr[Game4(Adv_34).main() @ &m : res] |
  = 
  `| Pr[XMLWR( B1(Adv_34) ).main(true) @ &m : res] - Pr[XMLWR( B1(Adv_34) ).main(false) @ &m : res] |. 
proof.
have ->: Pr[Game3(Adv_34).main() @ &m : res] = Pr[XMLWR( B1(Adv_34) ).main(false) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondf {2} 4.
  - by move => &m0; auto.
  rcondf {2} 6.
  - by move => &m0; auto.
  swap {2} 11 -10; swap {1} 5 3; swap {2} 6 -2; wp.
  by sim.
have ->: Pr[Game4(Adv_34).main() @ &m : res] = Pr[XMLWR( B1(Adv_34) ).main(true) @ &m : res].
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
lemma Aux_Prob_Half &m :
  Pr[Auxiliary_Game(Adv_34).main() @ &m : res]  = 1%r / 2%r. 
proof.
byphoare => //.
proc.
rnd.
call Adv_34_guess_ll; auto; call Adv_34_choose_ll; auto.
by progress; [apply dseed_ll        |
              apply dRq_vec_ll      |
              apply dRp_vec_ll      |
              apply Rp.dpolyXnD1_ll |
              apply dbool1E].
qed.

(* Game4 <==> Auxiliary_Game *)
lemma Equal_Prob_Game4_Aux &m :
  Pr[Game4(Adv_34).main() @ &m : res] = Pr[Auxiliary_Game(Adv_34).main() @ &m : res].
proof.
byequiv => //. 
proc; inline *.
swap {2} 7 -6.
call (_ : true); wp.
rnd (fun (x : Rp) => x + (scaleR22Rp_var (if u{1} then m1{1} else m0{1}) (2 * ep - eq - 1)))  
    (fun (x : Rp) => x - (scaleR22Rp_var (if u{1} then m1{1} else m0{1}) (2 * ep - eq - 1))).
auto; call(_ : true); auto.
progress; 1, 4: by ring.
- by apply /rnd_funi /Rp.dpolyXnD1_funi.
- by apply /is_fullP /Rp.dpolyXnD1_fu.  
qed.

(* Game4 Analysis *)
lemma Game4_Prob_Half &m :
  Pr[Game4(Adv_34).main() @ &m : res] = 1%r / 2%r. 
proof. by rewrite (Equal_Prob_Game4_Aux &m) (Aux_Prob_Half &m). qed.

end section Game_Hopping.

section Security_Theorem.

(* -- Declare (Terminating) Adversary Against INDCPA Game For Saber_PKE_Scheme -- *)
declare module A <: Adv_INDCPA.
declare axiom A_choose_ll : islossless A.choose.
declare axiom A_guess_ll : islossless A.guess.

(* Intelligibility Intermediate Result *)
lemma Difference_Game1_Game4_XMLWR &m :
  `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
  =
  `| Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] |.
proof.
move: A_choose_ll A_guess_ll => c_ll g_ll.
rewrite (Game4_Prob_Half (A3(A2(A))))
        3: (Step_Game1_Game2 A)
        3: (Step_Game2_Game3 (A2(A)))
        3: -(Game4_Prob_Half (A3(A2(A))) _ _ &m)
        5: &(Step_Distinguish_Game3_Game4_XMLWR (A3(A2(A)))) //;
          by proc; inline *; wp; call (_ : true); auto.
qed.

(* Final Result (Security Theorem) *)
lemma Saber_INDCPA_Security_Theorem &m :
  exists (BG <: Adv_GMLWR) (BX <: Adv_XMLWR),
  `| Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] - 1%r / 2%r |
  <=
  `| Pr[GMLWR(BG).main(true) @ &m : res] - Pr[GMLWR(BG).main(false) @ &m : res] | 
  +
  `| Pr[XMLWR(BX).main(true) @ &m : res] - Pr[XMLWR(BX).main(false) @ &m : res] |. 
proof.
exists (B0(A)) (B1(A3(A2(A)))).
move: A_choose_ll A_guess_ll => c_ll g_ll.
rewrite (Equivalence_SaberINDCPA_Game0 A) -(Game4_Prob_Half (A3(A2(A))) _ _ &m) //;
          first 2 by proc; inline *; wp; call (_ : true); auto.
have:
  `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
  +
  `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
  <=
  `| Pr[GMLWR( B0(A) ).main(true) @ &m : res] - Pr[GMLWR( B0(A) ).main(false) @ &m : res] | 
  +
  `| Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] |.
+ by apply ler_add; 
    [rewrite (Step_Distinguish_Game0_Game1_GMLWR A) | rewrite -(Difference_Game1_Game4_XMLWR &m) ].
move: (ler_dist_add (Pr[Game1(A).main() @ &m : res]) (Pr[Game0(A).main() @ &m : res])
                    (Pr[Game4( A3(A2(A)) ).main() @ &m : res])).
by apply ler_trans.  
qed.

end section Security_Theorem.
