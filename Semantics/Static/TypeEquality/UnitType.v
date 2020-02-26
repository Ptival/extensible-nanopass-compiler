From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import

     Semantics.Static.TypeEquality

     Syntax.Types.UnitType

     Theory.Algebra
     Theory.Functor
     Theory.ProgramAlgebra
     Theory.SubFunctor

.

Local Open Scope SubFunctor.

Section UnitType.

  Context
    {T}
    `{Functor T}
    `{T supports UnitType}
  .

  Global Instance TypeEquality__UnitType
         T `{Functor T} `{T supports UnitType}
    : forall {R}, ProgramAlgebra ForTypeEquality UnitType R (TypeEqualityResult T)
    := fun _ =>
         {|
           programAlgebra :=
             fun _ '(MkUnitType) => fun t => isUnitType (proj1_sig t)
           ;
         |}.

End UnitType.
