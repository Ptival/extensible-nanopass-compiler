From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Stuck
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     SubFunctor
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedSubFunctor
     ProofAlgebra
     ProgramAlgebra
     Types
     TypeSoundness
     UniversalProperty
.

Local Open Scope SubFunctor.

Section Stuck.

  Context

    {T}
    `{FunctorLaws T}

    {E}
    `{FunctorLaws E}
    `{! E supports Stuck}
    `{!WellFormedSubFunctor Stuck E}

    {V}
    `{FunctorLaws V}
    `{! V supports Stuck}
    `{! WellFormedSubFunctor Stuck V}

  .

  Inductive WellTyped__Stuck
            (WT : (TypedExpr T V)-indexedProp)
    : (TypedExpr T V)-indexedProp
    :=
    | WellTyped__stuck : forall t e reason,
        proj1_sig e = stuckF reason ->
        WellTyped__Stuck WT {| type := t; expr := e |}
  .

  Global Instance IndexedFunctor_WellTyped__Stuck
    : IndexedFunctor (TypedExpr T V) WellTyped__Stuck.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] /= => r Eq__t.
    move : Eq__t UP__e => -> => UP__e.
    econstructor => //.
  Qed.

End Stuck.
