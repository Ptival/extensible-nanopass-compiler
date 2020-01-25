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

Definition eval__If1
           {V} `{FunctorLaws V}
           `{! V supports Bool}
           `{! V supports Unit}
           `{! V supports Stuck}
  : forall {T}, MixinAlgebra If1 T (EvalResult V)
  := fun _ rec '(MkIf1 condition thenBranch) env =>
       match project__F (rec condition env) with
       | Some (MkBool b) =>
         if b
         then rec thenBranch env
         else unit
       | None => stuck "The condition of a unary branch did not evaluate to a boolean value"
       end.

Global Instance Eval__If1
       {V} `{FunctorLaws V}
       `{! V supports Bool}
       `{! V supports Unit}
       `{! V supports Stuck}
  : forall {T}, ProgramAlgebra Eval If1 T (EvalResult V)
  := fun T => {| programAlgebra := eval__If1; |}.

Inductive EvalP__If1 {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! E supports If1}
          `{! V supports Bool}
          `{! V supports Unit}
          (EvalP__E : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | If1True : forall c t t',
      EvalP__E (c, boolean true) ->
      EvalP__E (t, t') ->
      EvalP__If1 EvalP__E (if1 c t, t')
  | If1alse : forall c t,
      EvalP__E (c, boolean false) ->
      EvalP__If1 EvalP__E (if1 c t, unit)
.
