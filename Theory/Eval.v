From ExtensibleCompiler.Theory Require Import
     Algebra
     Environment
     Functor
     ProgramAlgebra
     SubFunctor
     Sum1
     UniversalProperty
.

Local Open Scope SubFunctor.
Local Open Scope Sum1.

(** [ValueFix] is just an alias for [WellFormedValue], but it makes it so that
    code that depends on wrapping values can use this, in case we ever need to
    change what type of fixed point to use.  *)
Definition ValueFix
           V `{Functor V}
  := WellFormedValue V.

Definition EvalResult
           V `{Functor V}
  := Environment (ValueFix V) -> ValueFix V.

Variant ForEval := .

Definition eval
           {L V}
           `{Functor L} `{Functor V}
           `{Eval__L : forall {T}, ProgramAlgebra ForEval L T (EvalResult V)}
  : Fix L -> EvalResult V
  := mendlerFold (fun _ => programAlgebra).

(* Class MendlerEval F R `{Functor F} `{Functor R} := *)
(*   { *)
(*     evalMendlerAlgebra : MendlerAlgebra F (Fix R); *)
(*   }. *)

(* Global *)
(*   Instance *)
(*   MendlerEvalSum1 *)
(*   F G R *)
(*   `{Functor F} `{Functor G} `{Functor R} *)
(*   `{MFR : MendlerEval F R} `{MGR : MendlerEval G R} *)
(*   : MendlerEval (F + G) R *)
(*   | 2 := *)
(*   {| *)
(*     evalMendlerAlgebra := *)
(*       fun A rec v => *)
(*         match v with *)
(*         | inl1 fa => evalMendlerAlgebra A rec fa *)
(*         | inr1 ga => evalMendlerAlgebra A rec ga *)
(*         end; *)
(*   |}. *)

(* Global *)
(*   Instance *)
(*   MendlerEvalSum1OutputL *)
(*   F G *)
(*   `{Functor F} `{Functor G} *)
(*   : MendlerEval F (F + G) *)
(*   | 3 := *)
(*   {| *)
(*     evalMendlerAlgebra := fun A rec v => wrapF (inl1 (fmap rec v)); *)
(*   |}. *)

(* Global *)
(*   Instance *)
(*   MendlerEvalSum1OutputR *)
(*   F G *)
(*   `{Functor F} `{Functor G} *)
(*   : MendlerEval G (F + G) *)
(*   | 4 := *)
(*   {| *)
(*     evalMendlerAlgebra := fun A rec v => wrapF (inr1 (fmap rec v)); *)
(*   |}. *)

(* Global Instance MendlerEvalRefl F `{Functor F} : MendlerEval F F *)
(*   | 1 := *)
(*   {| *)
(*     evalMendlerAlgebra := fun A rec v => wrapF (fmap rec v); *)
(*   |}. *)

(* (** *)
(* [T] stands for the recursive occurence. *)
(* [F] stands for the input functor. *)
(* [A] stands for the output functor. *)
(*  *) *)
(* Class MixinEval *)
(*       T F A *)
(*       `{Functor T} `{Functor F} `{Functor A} *)
(*   := { evalMixinAlgebra : MixinAlgebra F (Fix T) (Fix A) }. *)

(* Global *)
(*   Instance *)
(*   MixinEvalSum1 *)
(*   T F G R *)
(*   `(MFR : MixinEval T F R) `(MGR : MixinEval T G R) *)
(*   : MixinEval T (F + G) R *)
(*   | 2 := *)
(*   {| *)
(*     evalMixinAlgebra := *)
(*       fun rec v S alg => *)
(*         match v with *)
(*         | inl1 l => evalMixinAlgebra rec l S alg *)
(*         | inr1 r => evalMixinAlgebra rec r S alg *)
(*         end; *)
(*   |}. *)

(* Global *)
(*   Instance *)
(*   MixinEvalSum1OutputL *)
(*   T F G *)
(*   `{Functor T} `{Functor F} `{Functor G} *)
(*   : MixinEval T F (F + G) *)
(*   | 3 := *)
(*   {| *)
(*     evalMixinAlgebra := fun rec v S alg => mendlerFold alg (wrapF (inl1 (fmap rec v))); *)
(*   |}. *)

(* Global *)
(*   Instance *)
(*   MixinEvalSum1OutputR *)
(*   T F G *)
(*   `{Functor T} `{Functor F} `{Functor G} *)
(*   : MixinEval T G (F + G) *)
(*   | 3 := *)
(*   {| *)
(*     evalMixinAlgebra := fun rec v S alg => mendlerFold alg (wrapF (inr1 (fmap rec v))); *)
(*   |}. *)

(* Fixpoint boundedFix *)
(*          {A} {F} `{Functor F} *)
(*          (n : nat) *)
(*          (fM : MixinAlgebra F (Fix F) A) *)
(*          (default : A) *)
(*          (e : Fix F) *)
(*   : A *)
(*   := *)
(*   match n with *)
(*   | 0   => default *)
(*   | S n => fM (boundedFix n fM default) (unwrapF e) *)
(*   end. *)

(* Class WellFormedMendlerEval *)
(*       F G A *)
(*       `{MFA : MendlerEval F A} `{MGA : MendlerEval G A} *)
(*       `{S : SubFunctor F G} *)
(*   := *)
(*     { *)
(*       wellFormedMendlerEval : forall (R : Set) (rec : R -> Fix A) (e : F R), *)
(*         evalMendlerAlgebra R rec (inj e) = evalMendlerAlgebra R rec e; *)
(*     }. *)

(* Global Instance WellFormedMendlerEvalLeft *)
(*        F G H A *)
(*        `{Functor F} `{Functor G} `{Functor A} *)
(*        `{MFA : ! MendlerEval F A} *)
(*        `{MGA : ! MendlerEval G A} *)
(*        `{S : ! SubFunctor F G} *)
(*        `(WF : ! WellFormedMendlerEval F G A) *)
(*        `{Functor H} *)
(*        `(HA : ! MendlerEval H A) *)
(*   : WellFormedMendlerEval F (G + H) A. *)
(* Proof. *)
(*   constructor. *)
(*   intros R rec e. *)
(*   unfold evalMendlerAlgebra. *)
(*   unfold MendlerEvalSum1. *)
(*   apply wellFormedMendlerEval. *)
(* Defined. *)

(* Global Instance WellFormedMendlerEvalRight *)
(*        F H A *)
(*        `{Functor F} `{Functor H} `{Functor A} *)
(*        `{MFA : ! MendlerEval F A} *)
(*        `{MHA : ! MendlerEval H A} *)
(*        `{S : ! SubFunctor F H} *)
(*        `(WF : ! WellFormedMendlerEval F H A) *)
(*        G `{Functor G} *)
(*        `(GA : ! MendlerEval G A) *)
(*   : WellFormedMendlerEval F (G + H) A. *)
(* Proof. *)
(*   constructor. *)
(*   intros R rec e. *)
(*   unfold evalMendlerAlgebra. *)
(*   unfold MendlerEvalSum1. *)
(*   apply wellFormedMendlerEval. *)
(* Defined. *)

(* Class WellFormedMixinEval *)
(*       T F G A *)
(*       `{Functor T} `{Functor F} `{Functor G} `{Functor A} *)
(*       `{TFA : ! MixinEval T F A} `{TGA : ! MixinEval T G A} *)
(*       `{S : ! SubFunctor F G} *)
(*   := *)
(*     { *)
(*       wellFormedMixinEval : forall (rec : Fix T -> Fix A) (e : F (Fix T)), *)
(*         evalMixinAlgebra rec (inj e) = evalMixinAlgebra rec e *)
(*       ; *)
(*     }. *)

(* Global Instance WellFormedMixinEvalLeft *)
(*        T F G H A *)
(*        `{Functor T} `{Functor F} `{Functor G} `{Functor H} `{Functor A} *)
(*        `{MFA : ! MixinEval T F A} *)
(*        `{MGA : ! MixinEval T G A} *)
(*        `{S : ! SubFunctor F G} *)
(*        `(WF : WellFormedMixinEval T F G A) *)
(*        `(HA : ! MixinEval T H A) *)
(*   : WellFormedMixinEval T F (G + H) A. *)
(* Proof. *)
(*   constructor. *)
(*   intros rec e. *)
(*   unfold evalMixinAlgebra. *)
(*   unfold MixinEvalSum1. *)
(*   apply wellFormedMixinEval. *)
(* Defined. *)

(* Global Instance WellFormedMixinEvalRight *)
(*        T F G H A *)
(*        `{Functor T} `{Functor F} `{Functor G} `{Functor H} `{Functor A} *)
(*        `{MFA : ! MixinEval T F A} *)
(*        `{MHA : ! MixinEval T H A} *)
(*        `{S : ! SubFunctor F H} *)
(*        `(WF : WellFormedMixinEval T F H A) *)
(*        `(GA : ! MixinEval T G A) *)
(*   : WellFormedMixinEval T F (G + H) A. *)
(* Proof. *)
(*   constructor. *)
(*   intros rec e. *)
(*   unfold evalMixinAlgebra. *)
(*   unfold MixinEvalSum1. *)
(*   apply wellFormedMixinEval. *)
(* Defined. *)
