From Coq Require Import ssreflect.

From ExtensibleCompiler.Syntax.Terms Require Import If2.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section If2.

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
    `{! WellFormedSubFunctor BoolType T}

    {E}
    `{FunctorLaws E}
    `{E supports If2}
  .

  Inductive WellTyped__If2
            (WT : (TypedExpr T E)-indexedProp)
    : (TypedExpr T E)-indexedProp
    :=
    | WellTyped__if2 : forall t e condition thenBranch elseBranch,
        proj1_sig e = if2F condition thenBranch elseBranch ->
        WT {| type := boolType';  expr := condition; |} ->
        WT {| type := t;          expr := thenBranch; |} ->
        WT {| type := t;          expr := elseBranch; |} ->
        WellTyped__If2 WT {| type := t; expr := e; |}
  .

  Global Instance IndexedFunctor_WellTyped__If2
    : IndexedFunctor (TypedExpr T E) WellTyped__If2.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] /= => cond thenB elseB Eq__e.
    move : Eq__e UP__e => -> => UP__e H__c H__t H__e.
    econstructor => //; apply IH => //.
  Qed.

End If2.
