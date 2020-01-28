From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
.

From ExtensibleCompiler.Syntax.Types Require Import
     BoolType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     SubFunctor
     Types
.

Local Open Scope SubFunctor_scope.

Section Bool.

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
    `{! WellFormedSubFunctor BoolType T}
  .

  Definition typeOf__Bool
    : forall {R}, MixinAlgebra Bool R (TypeOfResult T)
    := fun _ rec '(MkBool _) => Some boolType'.

  Global Instance TypeOf__Bool
    : forall {R}, ProgramAlgebra ForTypeOf Bool R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__Bool; |}.

  Global Instance TypeOf__Bool'
    : forall R, ProgramAlgebra ForTypeOf Bool R (TypeOfResult T)
    := fun _ => TypeOf__Bool.

  Global Instance WellFormedMendlerAlgebra_TypeOf__Bool
    : WellFormedMendlerAlgebra TypeOf__Bool'.
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

End Bool.
