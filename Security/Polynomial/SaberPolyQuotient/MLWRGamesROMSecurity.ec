pragma Goals:printall.

(*
----------------------------------- 
 Require/Import EasyCrypt Theories
-----------------------------------
*)
(* --- Built-in --- *)
require import AllCore Distr DBool ZModP IntDiv StdOrder PROM.
require (*--*) Matrix PKE.

(* --- Local --- *)
require import SaberRqPreliminaries.
(*---*) import Rq Rp Rppq R2t R2.
(*---*) import Mat_Rq Mat_Rp.

(*
----------------------------------- 
 ROM
-----------------------------------
*)

clone import FullRO with
  type in_t <- seed,
  type out_t <- Rq_mat,
  op dout <- (fun (sd : seed) => dRq_mat).

(*
--------------------------------
 Adversary Prototypes
--------------------------------
*)
module type Adv_MLWR = {
  proc guess(_A : Rq_mat, b : Rp_vec) : bool
}.

module type Adv_GMLWR_RO(Gen : RO) = {
   proc guess(sd : seed, b : Rp_vec) : bool { Gen.get }
}.

module type Adv_XMLWR_RO(Gen : RO) = {
   proc guess(sd : seed, b : Rp_vec, a : Rq_vec, d : Rp) : bool { Gen.get }
}.

(*
--------------------------------
 Games
--------------------------------
*)

(* --- Original (transposed) MLWR Game --- *)
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
          b <- scale_vec_Rq_Rp (_A *^ s + h);
       }
       
       u' <@ A.guess(_A, b);

       return u';
    }
}.

(* --- LWR-Related Games in ROM --- *)
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
         b <- scale_vec_Rq_Rp (_A *^ s + h);
      }
      
      u' <@ A.guess(sd, b);
      
      return u';
   }
}.

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
         b <- scale_vec_Rq_Rp ((trmx _A) *^ s + h);
      }
      
      a <$ dRq_vec;

      if (u) {
         d <$ dRp;
      } else {
         d <- scale_Rq_Rp ((dotp a s) + h1);
      }
    
      u' <@ A.guess(sd, b, a, d);
      
      return u';
   }
}.

(*
--------------------------------
 Adversaries
--------------------------------
*)
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



(*
--------------------------------
 Reductions
--------------------------------
*)

lemma GMLWR_RO_to_MLWR &m (A <: Adv_GMLWR_RO{RO}) :
  `| Pr[GMLWR_RO(A).main(true) @ &m : res] - Pr[GMLWR_RO(A).main(false) @ &m : res] |
   =
  `| Pr[MLWR( AGM(A) ).main(true) @ &m : res] - Pr[MLWR( AGM(A) ).main(false) @ &m : res] |.
proof.
  have ->: Pr[GMLWR_RO(A).main(true) @ &m : res] =  Pr[MLWR( AGM(A) ).main(true) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondt {1} 8; 2: rcondt {2} 3; first 2 auto.
   rcondt {1} 5; first auto; progress; smt.
   swap {1} [7..8] -2; swap {1} [4..6] -2.
   by wp; call (_ : ={RO.m}); 1: proc; auto.
  have -> //: Pr[GMLWR_RO(A).main(false) @ &m : res] =  Pr[MLWR( AGM(A) ).main(false) @ &m : res].
   byequiv => //.
   proc; inline *.
   rcondf {1} 8; 2: rcondf {2} 3; first 2 auto.
   rcondt {1} 5; first auto; progress; smt.
   swap {1} 4 -3; swap {1} 7 -5. 
   wp; call (_ : ={RO.m}); 1: proc; auto.
   progress; smt.
qed.  

