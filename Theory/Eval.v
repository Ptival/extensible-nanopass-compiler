From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

(** [ValueFix] is just an alias for [UniversalPropertyF], but it makes it so that
    code that depends on wrapping values can use this, in case we ever need to
    change what type of fixed point to use.  *)
Definition ValueFix
           V `{FunctorLaws V}
  := UniversalPropertyF V.

Definition EvalResult
           V `{FunctorLaws V}
  := ValueFix V.

Definition eval
           {L V}
           `{FunctorLaws L} `{FunctorLaws V}
           {evalL : forall T, ProgramAlgebra L T (EvalResult V)}
  := mendlerFold (fun _ => @programAlgebra _ _ _ _ _ (evalL _)).

Class MendlerEval F R `{FunctorLaws F} `{FunctorLaws R} :=
  {
    evalMendlerAlgebra : MendlerAlgebra F (Fix R)
  }.

Global
  Instance
  MendlerEvalSum1
  F G R
  `{Functor F} `{Functor G} `{Functor R}
  `{MFR : MendlerEval F R} `{MGR : MendlerEval G R}
  : MendlerEval (F + G) R
  | 2 :=
  {|
    evalMendlerAlgebra :=
      fun A rec v =>
        match v with
        | inl1 fa => evalMendlerAlgebra A rec fa
        | inr1 ga => evalMendlerAlgebra A rec ga
        end;
  |}.

Global
  Instance
  MendlerEvalSum1OutputL
  F G
  `{FunctorLaws F} `{FunctorLaws G}
  : MendlerEval F (F + G)
  | 3 :=
  {|
    evalMendlerAlgebra := fun A rec v => wrapFix (inl1 (fmap rec v));
  |}.

Global
  Instance
  MendlerEvalSum1OutputR
  F G
  `{FunctorLaws F} `{FunctorLaws G}
  : MendlerEval G (F + G)
  | 4 :=
  {|
    evalMendlerAlgebra := fun A rec v => wrapFix (inr1 (fmap rec v));
  |}.

Global Instance MendlerEvalRefl F `{FunctorLaws F} : MendlerEval F F
  | 1 :=
  {|
    evalMendlerAlgebra := fun A rec v => wrapFix (fmap rec v);
  |}.

(**
[T] stands for the recursive occurence.
[F] stands for the input functor.
[A] stands for the output functor.
 *)
Class MixinEval
      T F A
      `{FunctorLaws T} `{FunctorLaws F} `{FunctorLaws A}
  := { evalMixinAlgebra : MixinAlgebra F (Fix T) (Fix A) }.

Global
  Instance
  MixinEvalSum1
  T F G R
  `(MFR : MixinEval T F R) `(MGR : MixinEval T G R)
  : MixinEval T (F + G) R
  | 2 :=
  {|
    evalMixinAlgebra :=
      fun rec v S alg =>
        match v with
        | inl1 l => evalMixinAlgebra rec l S alg
        | inr1 r => evalMixinAlgebra rec r S alg
        end;
  |}.

Global
  Instance
  MixinEvalSum1OutputL
  T F G
  `{FunctorLaws T} `{FunctorLaws F} `{FunctorLaws G}
  : MixinEval T F (F + G)
  | 3 :=
  {|
    evalMixinAlgebra := fun rec v S alg => mendlerFold alg (wrapFix (inl1 (fmap rec v)));
  |}.

Global
  Instance
  MixinEvalSum1OutputR
  T F G
  `{FunctorLaws T} `{FunctorLaws F} `{FunctorLaws G}
  : MixinEval T G (F + G)
  | 3 :=
  {|
    evalMixinAlgebra := fun rec v S alg => mendlerFold alg (wrapFix (inr1 (fmap rec v)));
  |}.

Fixpoint boundedFix
         {A} {F} `{Functor F}
         (n : nat)
         (fM : MixinAlgebra F (Fix F) A)
         (default : A)
         (e : Fix F)
  : A
  :=
  match n with
  | 0   => default
  | S n => fM (boundedFix n fM default) (unwrapFix e)
  end.

Class WellFormedMendlerEval
      F G A
      `{MFA : MendlerEval F A} `{MGA : MendlerEval G A}
      `{S : SubFunctor F G}
  :=
    {
      wellFormedMendlerEval : forall (R : Set) (rec : R -> Fix A) (e : F R),
        evalMendlerAlgebra R rec (inj e) = evalMendlerAlgebra R rec e;
    }.

Global Instance WellFormedMendlerEvalLeft
       F G A
       `{FunctorLaws F} `{FunctorLaws G} `{FunctorLaws A}
       `{MFA : ! MendlerEval F A}
       `{MGA : ! MendlerEval G A}
       `{S : ! SubFunctor F G}
       `(WF : ! WellFormedMendlerEval F G A)
       H `{FunctorLaws H}
       `(HA : ! MendlerEval H A)
  : WellFormedMendlerEval F (G + H) A.
Proof.
  constructor.
  intros R rec e.
  unfold evalMendlerAlgebra.
  unfold MendlerEvalSum1.
  apply wellFormedMendlerEval.
Defined.

Global Instance WellFormedMendlerEvalRight
       F H A
       `{FunctorLaws F} `{FunctorLaws H} `{FunctorLaws A}
       `{MFA : ! MendlerEval F A}
       `{MHA : ! MendlerEval H A}
       `{S : ! SubFunctor F H}
       `(WF : ! WellFormedMendlerEval F H A)
       G `{FunctorLaws G}
       `(GA : ! MendlerEval G A)
  : WellFormedMendlerEval F (G + H) A.
Proof.
  constructor.
  intros R rec e.
  unfold evalMendlerAlgebra.
  unfold MendlerEvalSum1.
  apply wellFormedMendlerEval.
Defined.

Class WellFormedMixinEval
      T F G A
      `{FunctorLaws T} `{FunctorLaws F} `{FunctorLaws G} `{FunctorLaws A}
      `{TFA : ! MixinEval T F A} `{TGA : ! MixinEval T G A}
      `{S : ! SubFunctor F G}
  :=
    {
      wellFormedMixinEval : forall (rec : Fix T -> Fix A) (e : F (Fix T)),
        evalMixinAlgebra rec (inj e) = evalMixinAlgebra rec e
      ;
    }.

Global Instance WellFormedMixinEvalLeft
       T F G H A
       `{FunctorLaws T} `{FunctorLaws F} `{FunctorLaws G} `{FunctorLaws H} `{FunctorLaws A}
       `{MFA : ! MixinEval T F A}
       `{MGA : ! MixinEval T G A}
       `{S : ! SubFunctor F G}
       `(WF : WellFormedMixinEval T F G A)
       `(HA : ! MixinEval T H A)
  : WellFormedMixinEval T F (G + H) A.
Proof.
  constructor.
  intros rec e.
  unfold evalMixinAlgebra.
  unfold MixinEvalSum1.
  apply wellFormedMixinEval.
Defined.

Global Instance WellFormedMixinEvalRight
       T F G H A
       `{FunctorLaws T} `{FunctorLaws F} `{FunctorLaws G} `{FunctorLaws H} `{FunctorLaws A}
       `{MFA : ! MixinEval T F A}
       `{MHA : ! MixinEval T H A}
       `{S : ! SubFunctor F H}
       `(WF : WellFormedMixinEval T F H A)
       `(GA : ! MixinEval T G A)
  : WellFormedMixinEval T F (G + H) A.
Proof.
  constructor.
  intros rec e.
  unfold evalMixinAlgebra.
  unfold MixinEvalSum1.
  apply wellFormedMixinEval.
Defined.
