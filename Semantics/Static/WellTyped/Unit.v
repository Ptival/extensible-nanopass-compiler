From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Unit
.

From ExtensibleCompiler.Syntax.Types Require Import
     UnitType
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

Section Unit.

  Context

    {T}
    `{FunctorLaws T}
    `{! T supports UnitType}
    `{! WellFormedSubFunctor UnitType T}

    {E}
    `{FunctorLaws E}
    `{! E supports Unit}
    `{!WellFormedSubFunctor Unit E}

    {V}
    `{FunctorLaws V}
    `{! V supports Unit}
    `{! WellFormedSubFunctor Unit V}

  .

  Inductive WellTyped__Unit
            (WT : (TypedExpr T V)-indexedProp)
    : (TypedExpr T V)-indexedProp
    :=
    | WellTyped__unit : forall t e,
        proj1_sig e = unitF ->
        proj1_sig t = unitType ->
        WellTyped__Unit WT {| type := t; expr := e |}
  .

  Global Instance IndexedFunctor_WellTyped__Unit
    : IndexedFunctor (TypedExpr T V) WellTyped__Unit.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] /= => Eq__e Eq__t.
    move : Eq__t Eq__e UP__t UP__e => -> -> => UP__t UP__e.
    econstructor => //.
  Qed.

End Unit.
