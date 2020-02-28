From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import

     Semantics.Static.TypeOf

     Syntax.Terms.If1
     Syntax.Types.BoolType
     Syntax.Types.UnitType

     Theory.Algebra
     Theory.Functor
     Theory.SubFunctor
     Theory.ProgramAlgebra
     Theory.Types

.

Local Open Scope SubFunctor.

Section If1.

  Context
    {T}
    `{Functor T}
    `{T supports BoolType}
    `{T supports UnitType}
  .

  Definition typeOf__If1
    : forall R, MixinAlgebra If1 R (TypeOfResult T)
    := fun _ rec '(MkIf1 c t) =>
         match rec c with
         | Some cType =>
           if isBoolType (proj1_sig cType)
           then
             match rec t with
             | Some tType =>
               if isUnitType (proj1_sig tType)
               then Some unitType'
               else None
             | None => None
             end
           else None
         | None => None
         end.

  Global Instance TypeOf__If1
    : forall R, ProgramAlgebra ForTypeOf If1 R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__If1 _ |}.

  Global Instance WellFormedProgramAlgebra__TypeOf__If1
    : WellFormedMendlerProgramAlgebra TypeOf__If1.
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

End If1.
