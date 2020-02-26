From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import

     Semantics.Static.TypeEquality

     Syntax.Types.BoolType

     Theory.Algebra
     Theory.Functor
     Theory.ProgramAlgebra
     Theory.SubFunctor

.

Local Open Scope SubFunctor.

Section BoolType.

  Context
    {T}
    `{Functor T}
    `{T supports BoolType}
  .

  Definition typeEquality__BoolType
    : forall R, MixinAlgebra BoolType R (TypeEqualityResult T)
    := fun _ rec '(MkBoolType) => fun t => isBoolType (proj1_sig t).

  Global Instance TypeEquality__BoolType
    : forall {R}, ProgramAlgebra ForTypeEquality BoolType R (TypeEqualityResult T)
    := fun _ => {| programAlgebra := typeEquality__BoolType _ |}.

End BoolType.
