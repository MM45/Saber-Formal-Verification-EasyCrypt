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



(* ----------------------------------- *)
(* MLWR-Related Games                  *)
(* ----------------------------------- *)

(* GMLWR Game *)
module GMLWR(A : Adv_GMLWR) = {
   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b0, b1 : Rp_vec;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      
      b0 <- scaleroundRqv2Rpv (_A *^ s);
      b1 <$ dRp_vec;
      
      u' <@ A.guess(sd, if u then b1 else b0);
      
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
      var b0, b1 : Rp_vec;
      var a : Rq_vec;
      var d0, d1 : Rp;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      
      b0 <- scaleroundRqv2Rpv ((trmx _A) *^ s);
      b1 <$ dRp_vec;
      
      a <$ dRq_vec;

      d0 <- scaleroundRq2Rp (dotp a s);
      d1 <$ dRp;
    
      u' <@ A.guess(sd, if u then b1 else b0, a, if u then d1 else d0);
      
      return u';
   }
}.



(* ----------------------------------- *)
(* Game-Playing Proof                  *)
(* ----------------------------------- *)

section INDCPA_SaberPKE.
(* --- Auxiliary Adversary Classes --- *)
local module type Adv_INDCPA_2 = {
  proc choose(pk : seed * Rp_vec) : R2 * R2  
  proc guess(c : Rppq * Rp_vec) : bool
}.

local module type Adv_INDCPA_34 = {
  proc choose(pk : seed * Rq_vec) : R2 * R2  
  proc guess(c : Rp * Rp_vec) : bool
}.


(* --- Game Sequence --- *)
(* Game 0 *)
local module Game0(A : Adv_INDCPA) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var chat : R2t;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      s <$ dsmallRq_vec;
      b <- scaleRqv2Rpv (_A *^ s + h);

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      chat <- scaleRp2R2t (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((chat, b'));

      return (u = u');
   }
}.

(* Game 1 *)
local module Game1(A : Adv_INDCPA) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var chat : R2t;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRp_vec;

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      chat <- scaleRp2R2t (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((chat, b'));

      return (u = u');
   }
}.

(* Game 2 *)
local module Game2(A : Adv_INDCPA_2) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var chat : Rppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRp_vec;

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      chat <- scaleRp2Rppq (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((chat, b'));

      return (u = u');
   }
}.

(* Auxiliary Game (Reduction 2-3): Game 2a *)
local module Game2a(A : Adv_INDCPA_2) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var chat : Rppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <@ Rqv2RpvSampl.sample(dRq_vec, Rqv2Rpv);

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      chat <- scaleRp2Rppq (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((chat, b'));

      return (u = u');
   }
}.

(* Auxiliary Game (Reduction 2-3): Game 2b *)
local module Game2b(A : Adv_INDCPA_2) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var bq : Rq_vec;
      var b, b' : Rp_vec;
      var v' : Rp;
      var chat : Rppq;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <@ Rqv2RpvSampl.map(dRq_vec, Rqv2Rpv);

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- (dotp b (Rqv2Rpv s')) + (Rq2Rp h1);
      chat <- scaleRp2Rppq (v' + (scaleR22Rp (if u then m1 else m0)));
      
      u' <@ A.guess((chat, b'));

      return (u = u');
   }
}.

(* Game 3 *)
local module Game3(A : Adv_INDCPA_34) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var chat : Rp;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRq_vec;

      (m0, m1) <@ A.choose((sd, b));

      s' <$ dsmallRq_vec;
      b' <- scaleRqv2Rpv ((trmx _A) *^ s' + h);
      v' <- scaleRq2Rp ((dotp b s') + h1);
      chat <- v' + (scaleR22Rp_var (if u then m1 else m0) (2 * ep - eq - 1));
   
      u' <@ A.guess((chat, b'));

      return (u = u');
   }
}.

(* Game 4 *)
local module Game4(A : Adv_INDCPA_34) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;

      var sd : seed;
      var _A : Rq_mat;
      var s, s' : Rq_vec;
      var b : Rq_vec;
      var b' : Rp_vec;
      var v' : Rp;
      var chat : Rp;

      u <$ dbool;

      sd <$ dseed;
      _A <- gen sd;
      (* Skip: s <$ dsmallRq_vec; *)
      b <$ dRq_vec;

      (m0, m1) <@ A.choose((sd, b));

      (* Skip: s' <$ dsmallRq_vec; *)
      b' <$ dRp_vec;
      v' <$ dRp;
      chat <- v' + (scaleR22Rp_var (if u then m1 else m0) (2 * ep - eq - 1));
      
      u' <@ A.guess((chat, b'));

      return (u = u');
   }
}.

(* Auxiliary Game with All Random Artifacts *)
local module Auxiliary_Game(A : Adv_INDCPA_34) = {
   proc main() : bool = {
      var u, u' : bool;
      var m0, m1 : R2;
      
      var sd : seed;
      var b : Rq_vec;
      var b' : Rp_vec;
      var chat : Rp;
      
      sd <$ dseed;
      b <$ dRq_vec;
      
      (m0, m1) <@ A.choose((sd, b));
       
      b' <$ dRp_vec;
      chat <$ dRp;
         
      u' <@ A.guess((chat, b'));
      
      u <$ dbool;

      return (u = u');
  }
}.


(* --- Reduction Adversaries --- *)
(* Adversary B0 Against GMLWR, Constructed from Adversary A Distinguishing Between Game0 and Game1 *)
local module B0(A : Adv_INDCPA) : Adv_GMLWR = {
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
local module B1(A : Adv_INDCPA_34) : Adv_XMLWR = {
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

(* Adversary A2 Against Game2, Constructed from Adversary A1 Against Game1 *)
local module A2(A1 : Adv_INDCPA) : Adv_INDCPA_2 = {
   proc choose(pk : seed * Rp_vec) : R2 * R2 = {
      var m0, m1 : R2;
      
      (m0, m1) <@ A1.choose(pk);
      
      return (m0, m1);
   }

   proc guess(c : Rppq * Rp_vec) : bool = {
      var u' : bool;
      
      var chat : Rppq;
      var b' : Rp_vec;
      var chat' : R2t;
      
      chat <- c.`1;
      b' <- c.`2;

      chat' <- scaleRppq2R2t chat; 
            
      u' <@ A1.guess((chat', b'));

      return u';
   }
}.

(* Adversary A3 Against Game3, Constructed from Adversary A2 Against Game2 *)
local module A3(A2 : Adv_INDCPA_2) : Adv_INDCPA_34 = {
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
      
      var chat : Rp;
      var b' : Rp_vec;
      var chat' : Rppq;
      
      chat <- c.`1;
      b' <- c.`2;
      chat' <- Rp2Rppq chat; 
      
      u' <@ A2.guess((chat', b'));

      return u';
   }
}.


(* --- Declare (Arbitrary Terminating) IND-CPA Adversary --- *)
declare module A <: Adv_INDCPA.
declare axiom A_choose_ll : islossless A.choose.
declare axiom A_guess_ll : islossless A.guess.

(* Saber's INDCPA <==> Game 0 *)
local lemma Equivalence_SaberINDCPA_Game0 &m :
  `| Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game0(A).main() @ &m : res] - 1%r /2%r |.
proof.
do 2! congr.
byequiv => //.
proc; inline *. 
swap {1} 7 -6.
call (_ : true); auto; call (_: true); auto => /> u _ sd _ s1 _ s2 _ u'.
by rewrite (eq_sym u u').
qed.

(* Step 1: Game0 <> Game1 -- GMLWR *)
local lemma Step_Distinguish_Game0_Game1_GMLWR &m :
  `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
  = 
  `| Pr[GMLWR( B0(A) ).main(false) @ &m : res] - Pr[GMLWR( B0(A) ).main(true) @ &m : res] |. 
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc; inline *.
  swap{2} 8 -7; wp.
  call (_ : true); auto; call (_: true); wp; rnd{2}; auto => /> *.
  by rewrite dRp_vec_ll eq_scaleRqv2Rpv_scaleroundRqv2Rpv.
byequiv => //.
proc; inline *.
swap{2} 8 -7; wp.
call (_ : true); auto; call (_: true); auto; rnd{2}; auto => /> *.
by apply dsmallRq_vec_ll.
qed.

(* Step 2: Game1 -- Game2 *)
local lemma Step_Game1_Game2 &m :
  `| Pr[Game1(A).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game2( A2(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
do 2! congr.
byequiv => //.
proc; inline *.
wp; call (_ : true); auto; call (_ : true); auto => /> u _ sd _ b _ r s _.
by rewrite scaleRp2Rppq2R2t_comp.  
qed.

(* Auxiliary Step (Reduction 2-3): Game2 -- Game2a *)
local lemma AuxStep_Game2_Game2a &m :
  `| Pr[Game2( A2(A) ).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game2a( A2(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
do 2! congr.
byequiv => //.
proc; inline *.
auto; call(_ : true); auto; call(_ : true); auto => />.
by rewrite dRqv2dRpv.
qed.

(* Auxiliary Step (Reduction 2-3): Game2a -- Game2b *)
local lemma AuxStep_Game2a_Game2b &m :
  `| Pr[Game2a( A2(A) ).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game2b( A2(A) ).main() @ &m : res] - 1%r / 2%r |.
proof.
do 2! congr.
byequiv => //.
proc; inline A2(A).choose A2(A).guess.
by wp; call(_ : true); auto; call(_ : true); wp; call sample; auto.
qed.

(* Auxiliary Step (Reduction 2-3): Game2b -- Game3 *)
local lemma AuxStep_Game2b_Game3 &m :
  `| Pr[Game2b( A2(A) ).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game3( A3(A2(A)) ).main() @ &m : res] - 1%r / 2%r |.
proof.
do 2! congr.
byequiv => //.
proc; inline *.
auto; call(_ : true); auto; call(_ : true); auto => /> *.
by rewrite eq_comp23; do 2! congr; rewrite -Rq2Rp_DG23.
qed.

(* Step 3: Game2 -- Game3 *)
local lemma Step_Game2_Game3 &m :
  `| Pr[Game2( A2(A) ).main() @ &m : res] - 1%r / 2%r |
  =
  `| Pr[Game3( A3(A2(A)) ).main() @ &m : res] - 1%r / 2%r |.
proof.
by rewrite (AuxStep_Game2_Game2a &m) (AuxStep_Game2a_Game2b &m) (AuxStep_Game2b_Game3 &m).
qed.

(* Step 4: Game3 <> Game4 -- XMLWR *)
local lemma Step_Distinguish_Game3_Game4_XMLWR &m :
  `| Pr[Game3( A3(A2(A)) ).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
  = 
  `| Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] |. 
proof.
do 2! congr; last congr.
+ byequiv => //.
  proc; inline *.
  swap{1} 13 -9; swap {2} 13 -12; swap{2} 6 1.
  wp; call(: true); wp; call (: true). 
  wp; rnd{2}; wp; rnd{2}; auto => /> *.
  rewrite dRp_vec_ll /dRp dpolyXnD1_ll /=.
  by rewrite eq_scaleRq2Rp_scaleroundRq2Rp eq_scaleRqv2Rpv_scaleroundRqv2Rpv.
byequiv => //.
proc; inline *.
swap{1} [13..14] -8; swap{2} 13 -12; swap{2} 8 1; swap{2} 5 3; swap{2} 6 -1.
wp; call(: true); wp; call(: true).
auto; rnd{2}; auto => /> *.
by apply dsmallRq_vec_ll.
qed.

(* Auxiliary_Game Analysis *)
local lemma Aux_Prob_Half &m :
  Pr[Auxiliary_Game( A3(A2(A)) ).main() @ &m : res]  = 1%r / 2%r. 
proof.
byphoare => //.
proc; inline *.
rnd; wp.
call A_guess_ll; auto; call A_choose_ll; auto => />.
split => [| *]; first by apply dseed_ll.
split => [| *]; first by apply dRq_vec_ll.
split => [| *]; first by apply dRp_vec_ll.
by split => [| *]; [apply Rp.dpolyXnD1_ll | apply dbool1E].
qed.

(* Game4 <==> Auxiliary_Game *)
local lemma Equal_Prob_Game4_Aux &m :
  Pr[Game4( A3(A2(A)) ).main() @ &m : res] 
  = 
  Pr[Auxiliary_Game( A3(A2(A)) ).main() @ &m : res].
proof.
byequiv => //. 
proc; inline *.
swap {2} 24 -23.
wp; call (_ : true); wp.
rnd (fun (x : Rp) => x + (scaleR22Rp_var (if u{1} then m1{1} else m0{1}) (2 * ep - eq - 1)))  
    (fun (x : Rp) => x - (scaleR22Rp_var (if u{1} then m1{1} else m0{1}) (2 * ep - eq - 1))).
auto; call(_ : true); auto => /> *.
split => *; first by ring.
split => *; first by apply /rnd_funi /Rp.dpolyXnD1_funi.
by split => *; [apply /is_fullP /Rp.dpolyXnD1_fu | ring].
qed.

(* Game4 Analysis *)
local lemma Game4_Prob_Half &m :
  Pr[Game4( A3(A2(A)) ).main() @ &m : res] = 1%r / 2%r. 
proof. by rewrite (Equal_Prob_Game4_Aux &m) (Aux_Prob_Half &m). qed.

(* Intelligibility Intermediate Result *)
local lemma Difference_Game1_Game4_XMLWR &m :
  `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
  =
  `| Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] |.
proof.
move: A_choose_ll A_guess_ll => c_ll g_ll.
rewrite Game4_Prob_Half Step_Game1_Game2 Step_Game2_Game3.
by rewrite -(Game4_Prob_Half &m) Step_Distinguish_Game3_Game4_XMLWR.
qed.

(* Final Result (Security Theorem) *)
lemma Saber_INDCPA_Security_Theorem &m :
  exists (BG <: Adv_GMLWR) (BX <: Adv_XMLWR),
  `| Pr[CPA(Saber_PKE_Scheme, A).main() @ &m : res] - 1%r / 2%r |
  <=
  `| Pr[GMLWR(BG).main(false) @ &m : res] - Pr[GMLWR(BG).main(true) @ &m : res] | 
  +
  `| Pr[XMLWR(BX).main(false) @ &m : res] - Pr[XMLWR(BX).main(true) @ &m : res] |. 
proof.
exists (B0(A)) (B1(A3(A2(A)))).
move: A_choose_ll A_guess_ll => c_ll g_ll.
rewrite Equivalence_SaberINDCPA_Game0 -(Game4_Prob_Half &m).
have:
  `| Pr[Game0(A).main() @ &m : res] - Pr[Game1(A).main() @ &m : res] |
  +
  `| Pr[Game1(A).main() @ &m : res] - Pr[Game4( A3(A2(A)) ).main() @ &m : res] |
  <=
  `| Pr[GMLWR( B0(A) ).main(false) @ &m : res] - Pr[GMLWR( B0(A) ).main(true) @ &m : res] | 
  +
  `| Pr[XMLWR( B1(A3(A2(A))) ).main(false) @ &m : res] - Pr[XMLWR( B1(A3(A2(A))) ).main(true) @ &m : res] |.
+ apply ler_add; first by rewrite Step_Distinguish_Game0_Game1_GMLWR. 
  by rewrite -(Difference_Game1_Game4_XMLWR &m).
move: (ler_dist_add (Pr[Game1(A).main() @ &m : res]) (Pr[Game0(A).main() @ &m : res])
                    (Pr[Game4( A3(A2(A)) ).main() @ &m : res])).
by apply ler_trans.
qed.

end section INDCPA_SaberPKE.
