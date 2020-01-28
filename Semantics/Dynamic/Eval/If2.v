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
    move => ???? [] //.
  Qed.

End If2.
