From Coq Require Import ssreflect.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition eval__Bool
           {V} `{FunctorLaws V}
           `{! V supports Bool}
  : forall {T}, MixinAlgebra Bool T (EvalResult V)
  := fun _ rec '(MkBool b) env => boolean b.

Global Instance EvalAlgebra__Bool
       {V} `{FunctorLaws V}
       `{! V supports Bool}
  : forall {T}, ProgramAlgebra Eval Bool T (EvalResult V)
  := fun _ => {| programAlgebra := eval__Bool; |}.

Inductive Eval__Bool {L V}
          `{FunctorLaws L} `{FunctorLaws V}
          `{! L supports Bool}
          `{! V supports Bool}
          (Eval_E : (WellFormedValue L * WellFormedValue V) -> Prop)
  : (WellFormedValue L * WellFormedValue V) -> Prop
  :=
  | BoolValue : forall b, Eval__Bool Eval_E (boolean b, boolean b)
.

Definition SoundnessStatement__Bool
           {L LT V}
           `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
           `{! L supports Bool}
           (WT : (TypedValue V LT -> Prop) -> TypedValue V LT -> Prop)
           `{Eval_L   : forall {T}, ProgramAlgebra Eval   L T (EvalResult   V)}
           `{TypeOf_L : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
           (recEval   : UniversalPropertyF L -> EvalResult   V)
           (recTypeOf : UniversalPropertyF L -> TypeOfResult LT)
  :=
    (SoundnessStatement__EvalAlgebra WT
                                   (evalL   := fun _ => programAlgebra' Eval_L)
                                   (typeOfL := fun _ => programAlgebra' TypeOf_L)
                                   recEval recTypeOf
    ).

Global Instance EvalSoundness__Bool
       {L LT V}
       `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
       `{! L supports Bool}
       (WT : (TypedValue V LT -> Prop) -> TypedValue V LT -> Prop)
       `{Eval_L   : forall {T}, ProgramAlgebra Eval   L T (EvalResult   V)}
       `{TypeOf_L : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
       (recEval   : UniversalPropertyF L -> EvalResult   V)
       (recTypeOf : UniversalPropertyF L -> TypeOfResult LT)
  : ProofAlgebra Bool (sig (UniversalPropertyP2 (SoundnessStatement__Bool WT recEval recTypeOf))).
Proof.
  constructor.
  apply Induction2Algebra_Bool => b.
  rewrite / SoundnessStatement__Bool / SoundnessStatement__EvalAlgebra / UniversalPropertyP2 /=.
  constructor.
  {
    apply conj; apply (proj2_sig (boolean b)).
  }
  {
    move => Gamma IH T TY.
    rewrite / boolean__F / boolean / inject /=.

    admit.
  }
Admitted.
