From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import
     Semantics.Static.TypeOf
     Syntax.Terms.Unit
     Syntax.Types.UnitType
     Theory.Algebra
     Theory.Functor
     Theory.ProgramAlgebra
     Theory.SubFunctor
     Theory.Types
     Theory.UniversalProperty
.

Local Open Scope SubFunctor.

Section UnitType.

  Context
    {T}
    `{Functor T}
    `{! T supports UnitType}
  .

  Definition typeOf__UnitType
  : forall R, MixinAlgebra Unit R (TypeOfResult T)
    := fun _ rec '(Unit) => Some unitType'.

  Global Instance TypeOf__Unit
    : forall {R}, ProgramAlgebra ForTypeOf Unit R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__UnitType _ |}.

  Global Instance WellFormedProgramAlgebra__TypeOf__Unit
    : WellFormedProgramAlgebra ForTypeOf Unit (TypeOfResult T).
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

End UnitType.
