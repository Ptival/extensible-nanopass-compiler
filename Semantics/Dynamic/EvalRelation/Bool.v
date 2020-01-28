From Coq Require Import ssreflect.

From ExtensibleCompiler.Semantics.Static Require Import Bool.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
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
  .

  Inductive EvalRelation__Bool
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | BoolValue : forall b, EvalRelation__Bool EvalRelation__E (boolean b, boolean b)
  .

End Bool.
