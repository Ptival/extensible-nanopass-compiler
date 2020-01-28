From Coq Require Import
     ssreflect
     String
.

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
To evaluate an [If1], the language must have [Bool] values, which is what we
would expect the condition to evaluate down to.  It must also have a [Unit]
value, which should be the type of the branch.  Finally, it must have a [Stuck]
placeholder, for when the condition does not evaluate to a boolean value.
   *)
  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
    `{! V supports Unit}
    `{! V supports Stuck}
  .

  Definition eval__If1
    : forall {T}, MixinAlgebra If1 T (EvalResult V)
    := fun _ rec '(MkIf1 condition thenBranch) env =>
         match projectF (rec condition env) with
         | Some (MkBool b) =>
           if b
           then rec thenBranch env
           else unit
         | None => stuck "The condition of a unary branch did not evaluate to a boolean value"
         end.

  Global Instance Eval__If1
    : forall {T}, ProgramAlgebra ForEval If1 T (EvalResult V)
    := fun T => {| programAlgebra := eval__If1; |}.

  (* Copy of [Eval__If1] for when you need to pass [T] explicitly *)
  Definition Eval__If1'
    : forall T, ProgramAlgebra ForEval If1 T (EvalResult V)
    := fun _ => Eval__If1.

  Global Instance WF_Eval__If1
    : WellFormedMendlerAlgebra Eval__If1'.
  Proof.
    constructor.
    move => ???? [] //.
  Qed.

End If1.
