From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
     If2
     Stuck
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProgramAlgebra
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor.

Section If2.

  Context
    {V}
    `{Functor V}
    `{! V supports Bool}
    `{! V supports Stuck}
  .

  Definition eval__If2
    : forall R, MixinAlgebra If2 R (EvalResult V)
    := fun _ rec '(MkIf2 condition thenBranch elseBranch) env =>
         match isBoolean (proj1_sig (rec condition env)) with
         | Some b =>
           if b
           then rec thenBranch env
           else rec elseBranch env
         | None => stuck "The condition of a binary branch was not a boolean"
         end.

  Global Instance Eval__If2
    : forall R, ProgramAlgebra ForEval If2 R (EvalResult V)
    := fun _ => {| programAlgebra := eval__If2 _ |}.

  Global Instance WellFormedProgramAlgebra__Eval__If2
    : WellFormedMendlerProgramAlgebra Eval__If2.
  Proof.
    constructor.
    move => ???? [] //.
  Qed.

End If2.
