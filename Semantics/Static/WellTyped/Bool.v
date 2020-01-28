From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
.

From ExtensibleCompiler.Syntax.Types Require Import
     BoolType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     IndexedFunctor
     IndexedSubFunctor
     ProgramAlgebra
     SubFunctor
     TypeSoundness
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

Section Bool.

  Context

    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}

    {E}
    `{FunctorLaws E}
    `{! E supports Bool}
    `{! WellFormedSubFunctor Bool E}

    {V}
    `{FunctorLaws V}
    `{! V supports Bool}

  .

  Inductive WellTyped__Bool
            (WT : (TypedExpr T V)-indexedProp)
    : (TypedExpr T V)-indexedProp
    :=
    | WellTyped__boolean : forall t e b,
        proj1_sig e = booleanF b ->
        proj1_sig t = boolType ->
        WellTyped__Bool WT {| type := t; expr := e; |}
  .

  Global Instance IndexedFunctor_WellTyped__Bool
    : IndexedFunctor (TypedExpr T V) WellTyped__Bool.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] b /= => Eq__e Eq__t.
    move : Eq__t Eq__e UP__t UP__e => -> -> => UP__t UP__e.
    econstructor => //.
  Qed.

End Bool.
