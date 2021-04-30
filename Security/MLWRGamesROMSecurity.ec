(* ----------------------------------- *)
(*  Require/Import Theories            *)
(* ----------------------------------- *)

(* --- Built-in --- *)
require import AllCore Distr DBool PROM.
require (*--*) Matrix.

(* --- Local --- *)
require import SaberRqPreliminaries.
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
(*  Adversary Prototypes               *)
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
          b <- scaleRqv2Rpv (_A *^ s + h);
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
          b <- scaleRqv2Rpv (_A *^ s + h);
          d <- scaleRq2Rp ((dotp a s) + h1);
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
         b <- scaleRqv2Rpv (_A *^ s + h);
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
lemma GMLWR_RO_to_MLWR &m (A <: Adv_GMLWR_RO{RO}) :
  `| Pr[GMLWR_RO(A).main(true) @ &m : res] - Pr[GMLWR_RO(A).main(false) @ &m : res] |
   =
  `| Pr[MLWR( AGM(A) ).main(true) @ &m : res] - Pr[MLWR( AGM(A) ).main(false) @ &m : res] |.
proof.
have ->: Pr[GMLWR_RO(A).main(true) @ &m : res] =  Pr[MLWR( AGM(A) ).main(true) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondt {1} 8; 2: rcondt {2} 3; first 2 auto.
  rcondt {1} 5; first auto; progress; smt.
  swap {1} [7..8] -2; swap {1} [4..6] -2.
  by wp; call (_ : ={RO.m}); 1: proc; auto.
have -> //: Pr[GMLWR_RO(A).main(false) @ &m : res] =  Pr[MLWR( AGM(A) ).main(false) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondf {1} 8; 2: rcondf {2} 3; first 2 auto.
  rcondt {1} 5; first auto; progress; smt.
  swap {1} 4 -3; swap {1} 7 -5. 
  wp; call (_ : ={RO.m}); 1: proc; auto.
  progress; smt.
qed.  

(* Reduction From XMLWR_RO to MLWR1 *)
lemma XMLWR_RO_to_MLWR1 &m (A <: Adv_XMLWR_RO{RO}) :
  `| Pr[XMLWR_RO(A).main(true) @ &m : res] - Pr[XMLWR_RO(A).main(false) @ &m : res] |
   =
  `| Pr[MLWR1( AXM(A) ).main(true) @ &m : res] - Pr[MLWR1( AXM(A) ).main(false) @ &m : res] |.
proof.
have ->: Pr[XMLWR_RO(A).main(true) @ &m : res] =  Pr[MLWR1( AXM(A) ).main(true) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondt {1} 8; 2: rcondt {1} 10; 3: rcondt {2} 4; first 3 auto.
  rcondt {1} 5; first auto; progress; smt.
  swap {1} [7..10] -2; swap {1} [4..8] - 3; swap {1} 4 -2.
  wp; call (_ : ={RO.m}); first proc; auto. 
  wp; rnd; wp; do 4! rnd; rnd (fun (m : Rq_mat) => trmx m). 
  skip; progress; smt.
have -> //:  Pr[XMLWR_RO(A).main(false) @ &m : res] =  Pr[MLWR1( AXM(A) ).main(false) @ &m : res].
+ byequiv => //.
  proc; inline *.
  rcondf {1} 8; 2: rcondf {1} 10; 3: rcondf {2} 4; first 3 auto.
  rcondt {1} 5; first auto; progress; smt.
  swap {1} 9 -2; swap {1} [7..8] -2; swap {1} [4..6] -2.
  wp; call (_ : ={RO.m}); first proc; auto.  
  wp; rnd; wp; do 2! rnd; rnd (fun (m : Rq_mat) => trmx m). 
  auto; progress; smt.
qed.
