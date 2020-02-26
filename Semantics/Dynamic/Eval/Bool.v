From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
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

Section Bool.

  Context
    {V}
    `{Functor V}
    `{! V supports Bool}
  .

  Definition eval__Bool
    : forall T, MixinAlgebra Bool T (EvalResult V)
    := fun _ rec '(MkBool b) env => boolean b.

  Global Instance Eval__Bool
    : forall {T}, ProgramAlgebra ForEval Bool T (EvalResult V)
    := fun _ => {| programAlgebra := eval__Bool _ |}.

  Global Instance WellFormedProgramAlgebra__Eval__Bool
    : WellFormedProgramAlgebra ForEval Bool (EvalResult V).
  Proof.
    constructor.
    move => ???? [] //.
  Qed.

End Bool.
