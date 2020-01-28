From Coq Require Import ssreflect.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section Bool.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
  .

  Definition eval__Bool
    : forall {T}, MixinAlgebra Bool T (EvalResult V)
    := fun _ rec '(MkBool b) env => boolean b.

  Global Instance Eval__Bool
    : forall {T}, ProgramAlgebra ForEval Bool T (EvalResult V)
    := fun _ => {| programAlgebra := eval__Bool; |}.

  Global Instance WF_Eval__Bool
    : WellFormedMendlerAlgebra (fun _ => Eval__Bool).
  Proof.
    constructor.
    move => T T' f rec [] b //.
  Qed.

End Bool.
