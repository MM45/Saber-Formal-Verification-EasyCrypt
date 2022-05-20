(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr DBool PROM.
require (*--*) Matrix.

(* --- Local --- *)
require import SaberPKEPreliminaries.
(*---*) import Mat_Rq Mat_Rp.
(*---*) import Rq Rp.
(*---*) import Rq.ComRing Rp.ComRing.

(* ----------------------------------- *)
(*  ROM                                *)
(* ----------------------------------- *)
clone import FullRO as PRO with
  type in_t  <- seed,
  type out_t <- Rq_mat,
    op dout  <- (fun (sd : seed) => dRq_mat).

(* ----------------------------------- *)
(*  Adversary Classes                  *)
(* ----------------------------------- *)
module type Adv_MLWR = {
  proc guess(_A : Rq_mat, b : Rp_vec) : bool
}.

module type Adv_MLWR1 = {
  proc guess(_A : Rq_mat, a : Rq_vec, b : Rp_vec, d : Rp) : bool
}.

module type Adv_GMLWR_RO(Gen : RO) = {
   proc guess(sd : seed, b : Rp_vec) : bool { Gen.get }
}.

module type Adv_XMLWR_RO(Gen : RO) = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool { Gen.get }
}.

(* ----------------------------------- *)
(*  Games                              *)
(* ----------------------------------- *)

(* Original MLWR Game (l samples) *)
module MLWR(A : Adv_MLWR) = {
    proc main(u : bool) : bool = {
       var u' : bool;
       var _A : Rq_mat;
       var s : Rq_vec;
       var b : Rp_vec;

       _A <$ dRq_mat;
       s <$ dsmallRq_vec;
       
       if (u) {
          b <$ dRp_vec; 
       } else {
          b <- scaleroundRqv2Rpv (_A *^ s);
       }
       
       u' <@ A.guess(_A, b);

       return u';
    }
}.

(* Original MLWR Game (l + 1 samples) *)
module MLWR1(A : Adv_MLWR1) = {
    proc main(u : bool) : bool = {
       var u' : bool;
       var _A : Rq_mat;
       var a : Rq_vec;
       var s : Rq_vec;
       var b : Rp_vec;
       var d : Rp;

       _A <$ dRq_mat; (* l samples *)
       a <$ dRq_vec; (* single sample *)
      
       s <$ dsmallRq_vec;
       
       if (u) {
          b <$ dRp_vec;
          d <$ dRp;
       } else {
          b <- scaleroundRqv2Rpv (_A *^ s);
          d <- scaleroundRq2Rp (dotp a s);
       }
       
       u' <@ A.guess(_A, a, b, d);

       return u';
    }
}.

(* GMLWR in ROM *)
module GMLWR_RO(A : Adv_GMLWR_RO) = {
   module A = A(RO)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;

      RO.init();

      sd <$ dseed;
      _A <@ RO.get(sd);
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv (_A *^ s);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.

(* XMLWR in ROM *)
module XMLWR_RO(A : Adv_XMLWR_RO) = {
   module A = A(RO)

   proc main(u : bool) : bool = {
      var u' : bool;
      var sd : seed;
      var _A : Rq_mat;
      var s : Rq_vec;
      var b : Rp_vec;
      var a : Rq_vec;
      var d : Rp;

      RO.init();

      sd <$ dseed;
      _A <- RO.get(sd);
      s <$ dsmallRq_vec;
      
      if (u) {
         b <$ dRp_vec;
      } else {
         b <- scaleroundRqv2Rpv ((trmx _A) *^ s);
      }
      
      a <$ dRq_vec;

      if (u) {
         d <$ dRp;
      } else {
         d <- scaleroundRq2Rp (dotp a s);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.

(* ----------------------------------- *)
(*  Reduction Adversaries              *)
(* ----------------------------------- *)

(* Adversary Against MLWR (l samples) Game, Constructed From Adversary Against GMLWR_RO Game *)
module AGM(AG : Adv_GMLWR_RO) : Adv_MLWR = {
   module AG = AG(RO)

   proc guess(_A : Rq_mat, b : Rp_vec) : bool = {
      var u' : bool;
      var sd : seed;

      RO.init();

      sd <$ dseed;

      RO.set(sd, _A);

      u' <@ AG.guess(sd, b);

      return u';
   } 
}.

(* Adversary Against MLWR1 (l + 1 samples) Game, Constructed From Adversary Against XMLWR_RO Game *)
module AXM(AX : Adv_XMLWR_RO) : Adv_MLWR1 = {
   module AX = AX(RO)

   proc guess(_A : Rq_mat, a : Rq_vec, b : Rp_vec, d : Rp) : bool = {
      var u' : bool;
      var sd : seed;

      RO.init();

      sd <$ dseed;

      RO.set(sd, trmx _A);

      u' <@ AX.guess(sd, b, a, d);

      return u';
   } 
}.

(* ----------------------------------- *)
(*  Reductions                         *)
(* ----------------------------------- *)

(* Reduction From GMLWR_RO to MLWR *)
lemma Equivalent_GMLWR_RO_MLWR (A <: Adv_GMLWR_RO{-RO}) :
  equiv[GMLWR_RO(A).main ~ MLWR( AGM(A) ).main : ={glob A, u} ==> ={res}].
proof.
proc; inline *.
case (u{1}).
+ conseq (_ : ={glob A} /\ u{1} /\ u{2} ==> _) => //.
  rcondt {1} 8; 2: rcondt {2} 3; first 2 by auto.
  rcondt {1} 5; first by auto; progress; apply SmtMap.mem_empty.
  swap {1} [7..8] -2; swap {1} [4..6] -2.
  by wp; call (_ : ={RO.m}); 1: proc; auto.
+ conseq (_ :  ={glob A} /\ !u{1} /\ !u{2} ==> _) => //. 
  rcondf {1} 8; 2: rcondf {2} 3; first 2 by auto.
  rcondt {1} 5; first by auto; progress; apply SmtMap.mem_empty.
  swap {1} 4 -3; swap {1} 7 -5. 
  wp; call (_ : ={RO.m}); 1: proc; auto; progress.
  by do 2! congr; rewrite SmtMap.get_set_sameE oget_some. 
qed.

lemma Equal_Advantage_GMLWR_RO_MLWR &m (A <: Adv_GMLWR_RO{-RO}) :
  `| Pr[GMLWR_RO(A).main(true) @ &m : res] - Pr[GMLWR_RO(A).main(false) @ &m : res] |
   =
  `| Pr[MLWR( AGM(A) ).main(true) @ &m : res] - Pr[MLWR( AGM(A) ).main(false) @ &m : res] |.
proof.
have ->: Pr[GMLWR_RO(A).main(true) @ &m : res] = Pr[MLWR( AGM(A) ).main(true) @ &m : res].
+ by byequiv (Equivalent_GMLWR_RO_MLWR A).
have -> //: Pr[GMLWR_RO(A).main(false) @ &m : res] = Pr[MLWR( AGM(A) ).main(false) @ &m : res].
+ by byequiv (Equivalent_GMLWR_RO_MLWR A).
qed.


(* Reduction From XMLWR_RO to MLWR1 *)
lemma Equivalent_XMLWR_RO_MLWR1 (A <: Adv_XMLWR_RO{-RO}) :
  equiv[XMLWR_RO(A).main ~ MLWR1( AXM(A) ).main : ={glob A, u} ==> ={res}].
proof.
proc; inline *.
case (u{1}).
+ conseq (_ : ={glob A} /\ u{1} /\ u{2} ==> _) => //.
  rcondt {1} 8; 2: rcondt {1} 10; 3: rcondt {2} 4; first 3 auto.
  rcondt {1} 5; first by auto; progress; apply SmtMap.mem_empty.
  swap {1} [7..10] -2; swap {1} [4..8] - 3; swap {1} 4 -2.
  wp; call (_ : ={RO.m}); first by proc; auto. 
  wp; rnd; wp; do 4! rnd; rnd (fun (m : Rq_mat) => trmx m). 
  skip; progress; 1, 4, 5: by rewrite trmxK.
  - by apply /rnd_funi /is_full_funiform /dRq_mat_uni /dRq_mat_fu.
  - by apply /is_fullP /dRq_mat_fu.
+ conseq (_ :  ={glob A} /\ !u{1} /\ !u{2} ==> _) => //. 
  rcondf {1} 8; 2: rcondf {1} 10; 3: rcondf {2} 4; first 3 by auto.
  rcondt {1} 5; first by auto; progress; apply SmtMap.mem_empty.
  swap {1} 9 -2; swap {1} [7..8] -2; swap {1} [4..6] -2.
  wp; call (_ : ={RO.m}); first by proc; auto.  
  wp; rnd; wp; do 2! rnd; rnd (fun (m : Rq_mat) => trmx m). 
  auto; progress; 1, 4, 6: by rewrite trmxK.
  - by apply /rnd_funi /is_full_funiform /dRq_mat_uni /dRq_mat_fu.
  - by apply /is_fullP /dRq_mat_fu.
  - by do 3! congr; rewrite SmtMap.get_set_sameE oget_some.
qed.


lemma Equal_Advantage_XMLWR_RO_MLWR1 &m (A <: Adv_XMLWR_RO{-RO}) :
  `| Pr[XMLWR_RO(A).main(true) @ &m : res] - Pr[XMLWR_RO(A).main(false) @ &m : res] |
   =
  `| Pr[MLWR1( AXM(A) ).main(true) @ &m : res] - Pr[MLWR1( AXM(A) ).main(false) @ &m : res] |.
proof.
have ->: Pr[XMLWR_RO(A).main(true) @ &m : res] = Pr[MLWR1( AXM(A) ).main(true) @ &m : res].
+ by byequiv (Equivalent_XMLWR_RO_MLWR1 A).
have -> //:  Pr[XMLWR_RO(A).main(false) @ &m : res] = Pr[MLWR1( AXM(A) ).main(false) @ &m : res].
+ by byequiv (Equivalent_XMLWR_RO_MLWR1 A).
qed.
