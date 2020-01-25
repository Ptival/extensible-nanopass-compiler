From Coq Require Import String.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If2.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition eval__If2
           {V} `{FunctorLaws V}
           `{! V supports Bool}
           `{! V supports Stuck}
  : forall {T}, MixinAlgebra If2 T (EvalResult V)
  := fun _ rec '(MkIf2 condition thenBranch elseBranch) env =>
       match project__F (rec condition env) with
       | Some (MkBool b) =>
         if b
         then rec thenBranch env
         else rec elseBranch env
       | None => stuck "The condition of a binary branch was not a boolean"
       end.

Global Instance Eval__If2
       {V} `{FunctorLaws V}
       `{! V supports Bool}
       `{! V supports Stuck}
  : forall {T}, ProgramAlgebra Eval If2 T (EvalResult V)
  := fun _ => {| programAlgebra := eval__If2; |}.

Inductive EvalP__If2
          {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! E supports If2}
          `{! V supports Bool}
          (EvalP__E : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | If2True : forall c t e t',
      EvalP__E (c, boolean true) ->
      EvalP__E (t, t') ->
      EvalP__If2 EvalP__E (if2 c t e, t')
  | If2False : forall c t e e',
      EvalP__E (c, boolean false) ->
      EvalP__E (e, e') ->
      EvalP__If2 EvalP__E (if2 c t e, e')
.
