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

Global Instance EvalIf1
       {O} `{FunctorLaws O}
       `{! SubFunctor Bool  O}
       `{! SubFunctor Unit  O}
       `{! SubFunctor Stuck O}
       T
  : ProgramAlgebra If1 T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(MkIf1 condition thenBranch) =>
        match project (rec condition) with
        | Some (MkBool b) =>
          if b
          then rec thenBranch
          else proj1_sig unit'
        | None => proj1_sig (stuck "The condition of a unary branch did not evaluate to a boolean value")
        end
    ;
  |}.

Inductive EvalIf1__WF {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! SubFunctor If1  E}
          `{! SubFunctor Bool V}
          `{! SubFunctor Unit V}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | If1True : forall c t t',
      Eval (c, boolean' true) ->
      Eval (t, t') ->
      EvalIf1__WF Eval (if1 c t, t')
  | If1alse : forall c t,
      Eval (c, boolean' false) ->
      EvalIf1__WF Eval (if1 c t, unit')
.
