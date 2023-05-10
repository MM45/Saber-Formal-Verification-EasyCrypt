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

module Gen = RO.

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
       var b0, b1 : Rp_vec;

       _A <$ dRq_mat;
       s <$ dsmallRq_vec;
       
       b0 <- scaleroundRqv2Rpv (_A *^ s);
       b1 <$ dRp_vec;
       
       u' <@ A.guess(_A, if u then b1 else b0);

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
       var b0, b1 : Rp_vec;
       var d0, d1 : Rp;

       _A <$ dRq_mat; (* l samples *)
       a <$ dRq_vec; (* single sample *)
      
       s <$ dsmallRq_vec;
       
       b0 <- scaleroundRqv2Rpv (_A *^ s);
       b1 <$ dRp_vec;
       
       d0 <- scaleroundRq2Rp (dotp a s);
       d1 <$ dRp;
       
       u' <@ A.guess(_A, a, if u then b1 else b0, if u then d1 else d0);

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
      var b0, b1 : Rp_vec;

      RO.init();

      sd <$ dseed;
      _A <@ Gen.get(sd);
      s <$ dsmallRq_vec;
      
      b0 <- scaleroundRqv2Rpv (_A *^ s);
      b1 <$ dRp_vec;
      
      u' <@ A.guess(sd, if u then b1 else b0);
      
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
      var b0, b1 : Rp_vec;
      var a : Rq_vec;
      var d0, d1 : Rp;

      RO.init();

      sd <$ dseed;
      _A <@ Gen.get(sd);
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
rcondt{1} 5; first by auto => /> *; rewrite SmtMap.mem_empty.
wp; call(: ={RO.m}); first by proc; auto. 
swap{2} 8 -7; auto => /> &2 *.
by case (u{2}) => // _; rewrite SmtMap.get_set_sameE oget_some. 
qed.

lemma Equal_Advantage_GMLWR_RO_MLWR &m (A <: Adv_GMLWR_RO{-RO}) :
  `| Pr[GMLWR_RO(A).main(false) @ &m : res] - Pr[GMLWR_RO(A).main(true) @ &m : res] |
   =
  `| Pr[MLWR( AGM(A) ).main(false) @ &m : res] - Pr[MLWR( AGM(A) ).main(true) @ &m : res] |.
proof.
by do 2! congr; 2: congr; byequiv (Equivalent_GMLWR_RO_MLWR A).
qed.


(* Reduction From XMLWR_RO to MLWR1 *)
lemma Equivalent_XMLWR_RO_MLWR1 (A <: Adv_XMLWR_RO{-RO}) :
  equiv[XMLWR_RO(A).main ~ MLWR1( AXM(A) ).main : ={glob A, u} ==> ={res}].
proof.
proc; inline *.
rcondt{1} 5; first by auto => /> *; rewrite SmtMap.mem_empty.
swap{1} 1 3; swap{1} 2 2; swap{2} 2 3; swap{2} 13 -12.
wp; call(: ={RO.m}); first by proc; auto.
conseq />. 
seq 2 2 : (#pre /\ ={sd} /\ r{1} = trmx _A{2}). 
+ rnd (fun (m : Rq_mat) => trmx m); auto => /> *. 
  split => *; first by rewrite trmxK.
  split => *; first by apply /rnd_funi /is_full_funiform /dRq_mat_uni /dRq_mat_fu.
  by split => *; [apply /is_fullP /dRq_mat_fu | rewrite trmxK].
auto => /> &2 *.
by case (u{2}) => // _; rewrite SmtMap.get_set_sameE oget_some trmxK.
qed.


lemma Equal_Advantage_XMLWR_RO_MLWR1 &m (A <: Adv_XMLWR_RO{-RO}) :
  `| Pr[XMLWR_RO(A).main(false) @ &m : res] - Pr[XMLWR_RO(A).main(true) @ &m : res] |
   =
  `| Pr[MLWR1( AXM(A) ).main(false) @ &m : res] - Pr[MLWR1( AXM(A) ).main(true) @ &m : res] |.
proof.
by do 2! congr; 2: congr; byequiv (Equivalent_XMLWR_RO_MLWR1 A).
qed.
