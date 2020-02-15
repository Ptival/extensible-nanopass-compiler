From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Unit
.

From ExtensibleCompiler.Syntax.Types Require Import
     UnitType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     ProgramAlgebra
     SubFunctor
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.

Section UnitType.

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports UnitType}
    `{! WellFormedSubFunctor UnitType T}
  .

  Definition typeOf__UnitType
  : forall R, MixinAlgebra Unit R (TypeOfResult T)
    := fun _ rec '(Unit) => Some unitType'.

  Global Instance TypeOf__Unit
    : forall {R}, ProgramAlgebra ForTypeOf Unit R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__UnitType _ |}.

  Definition TypeOf__Unit'
    : forall R, ProgramAlgebra ForTypeOf Unit R (TypeOfResult T)
    := fun _ => TypeOf__Unit.

  Global Instance WellFormedMendlerAlgebra_TypeOf__Unit
    : WellFormedMendlerAlgebra TypeOf__Unit'.
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

End UnitType.
