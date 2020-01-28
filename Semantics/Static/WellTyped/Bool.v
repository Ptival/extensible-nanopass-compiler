From Coq Require Import ssreflect.

From ExtensibleCompiler.Semantics.Dynamic.Eval Require Import Bool.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSubFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section Bool.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Bool}

    {E}
    `{FunctorLaws E}
    `{! E supports Bool}
    `{! WellFormedSubFunctor Bool E}

    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
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
