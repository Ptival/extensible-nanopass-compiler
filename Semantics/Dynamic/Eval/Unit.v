From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Semantics.Static Require Import Unit.

From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Syntax.Types Require Import UnitType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSubFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section Unit.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Unit}
    `{! WellFormedSubFunctor Unit V}
  .

  Definition eval__Unit
    : forall {R}, MixinAlgebra Unit R (EvalResult V)
    := fun _ rec '(MkUnit) env => unit.

  Global Instance Eval__Unit
    : forall {R}, ProgramAlgebra ForEval Unit R (EvalResult V)
    := fun _ => {| programAlgebra := eval__Unit; |}.

  Definition Eval__Unit'
    : forall R, ProgramAlgebra ForEval Unit R (EvalResult V)
    := fun _ => Eval__Unit.

  Global Instance WF_Eval__Bool
    : WellFormedMendlerAlgebra Eval__Unit'.
  Proof.
    constructor.
    move => T T' f rec [] //.
  Qed.

End Unit.
