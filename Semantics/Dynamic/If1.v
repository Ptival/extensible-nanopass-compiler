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
  : forall {T}, MixinAlgebra If1 T (WellFormedValue V)
  := fun _ rec '(MkIf1 condition thenBranch) =>
       match projectFix (rec condition) with
       | Some (MkBool b) =>
         if b
         then rec thenBranch
         else unit
       | None => stuck "The condition of a unary branch did not evaluate to a boolean value"
       end.

Global Instance EvalAlgebra__If1
       {V} `{FunctorLaws V}
       `{! V supports Bool}
       `{! V supports Unit}
       `{! V supports Stuck}
  : forall {T}, ProgramAlgebra Eval If1 T (WellFormedValue V)
  := fun T => {| programAlgebra := eval__If1; |}.

Inductive Eval__If1 {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! E supports If1}
          `{! V supports Bool}
          `{! V supports Unit}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | If1True : forall c t t',
      Eval (c, boolean true) ->
      Eval (t, t') ->
      Eval__If1 Eval (if1 c t, t')
  | If1alse : forall c t,
      Eval (c, boolean false) ->
      Eval__If1 Eval (if1 c t, unit)
.
