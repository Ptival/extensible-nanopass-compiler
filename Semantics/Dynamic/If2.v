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
  : forall {T}, MixinAlgebra If2 T (WellFormedValue V)
  := fun _ rec '(MkIf2 condition thenBranch elseBranch) =>
       match projectFix (rec condition) with
       | Some (MkBool b) =>
         if b
         then rec thenBranch
         else rec elseBranch
       | None => stuck "The condition of a binary branch was not a boolean"
       end.

Global Instance EvalAlgebra__If2
       {V} `{FunctorLaws V}
       `{! V supports Bool}
       `{! V supports Stuck}
  : forall {T}, ProgramAlgebra If2 T (WellFormedValue V)
  := fun _ => {| programAlgebra := eval__If2; |}.

Inductive Eval__If2 {L V}
          `{FunctorLaws L} `{FunctorLaws V}
          `{! L supports If2}
          `{! V supports Bool}
          (Eval : (WellFormedValue L * WellFormedValue V) -> Prop)
  : (WellFormedValue L * WellFormedValue V) -> Prop
  :=
  | If2True : forall c t e t',
      Eval (c, boolean true) ->
      Eval (t, t') ->
      Eval__If2 Eval (if2 c t e, t')
  | If2alse : forall c t e e',
      Eval (c, boolean false) ->
      Eval (e, e') ->
      Eval__If2 Eval (if2 c t e, e')
.
