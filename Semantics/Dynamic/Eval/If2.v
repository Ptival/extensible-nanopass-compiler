From Coq Require Import ssreflect.
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

Section If2.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
    `{! V supports Stuck}
  .

  Definition eval__If2
    : forall {T}, MixinAlgebra If2 T (EvalResult V)
    := fun _ rec '(MkIf2 condition thenBranch elseBranch) env =>
         match projectF (rec condition env) with
         | Some (MkBool b) =>
           if b
           then rec thenBranch env
           else rec elseBranch env
         | None => stuck "The condition of a binary branch was not a boolean"
         end.

  Global Instance Eval__If2
    : forall {T}, ProgramAlgebra ForEval If2 T (EvalResult V)
    := fun _ => {| programAlgebra := eval__If2; |}.

  Definition Eval__If2'
    : forall T, ProgramAlgebra ForEval If2 T (EvalResult V)
    := fun _ => Eval__If2.

  Global Instance WellFormedMendlerAlgebra_Eval__If2
    : WellFormedMendlerAlgebra Eval__If2'.
  Proof.
    constructor.
    move => T T' f rec [] //.
  Qed.

End If2.
