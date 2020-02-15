From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Unit
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

Section Unit.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Unit}
    `{! WellFormedSubFunctor Unit V}
  .

  Definition eval__Unit
    : forall {R}, MixinAlgebra Unit R (EvalResult V)
    := fun _ rec '(MkUnit) env => unit.

  Global Instance Eval__Unit
    : forall {R}, ProgramAlgebra ForEval Unit R (EvalResult V)
    := fun _ => {| programAlgebra := eval__Unit |}.

  Definition Eval__Unit'
    : forall R, ProgramAlgebra ForEval Unit R (EvalResult V)
    := fun _ => Eval__Unit.

  Global Instance WF_Eval__Bool
    : WellFormedMendlerAlgebra Eval__Unit'.
  Proof.
    constructor.
    move => ???? [] //.
  Qed.

End Unit.
