From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If1.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section If1.

  (*
We now define an extensible big-step semantics relation [EvalRelation] that
captures how [If1] evaluates in a larger language [E].
   *)

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports If1}

    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
    `{! V supports Unit}
  .

  Inductive EvalRelation__If1
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | If1True : forall c t t',
        EvalRelation__E (c, boolean true) ->
        EvalRelation__E (t, t') ->
        EvalRelation__If1 EvalRelation__E (if1 c t, t')
    | If1alse : forall c t,
        EvalRelation__E (c, boolean false) ->
        EvalRelation__If1 EvalRelation__E (if1 c t, unit)
  .

End If1.
