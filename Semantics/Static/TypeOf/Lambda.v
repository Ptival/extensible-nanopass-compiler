From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import
     Semantics.Static.TypeEquality
     Semantics.Static.TypeOf
     Syntax.Terms.Lambda
     Syntax.Types.ArrowType
     Theory.Algebra
     Theory.Functor
     Theory.SubFunctor
     Theory.ProgramAlgebra
     Theory.Types
     Theory.UniversalProperty
.

Local Open Scope SubFunctor.

Section Lambda.

  Context
    {T}
    `{Functor T}
    `{T supports ArrowType}
    `{TypeEqualityForT : forall R, ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
  .

  Definition typeOf__Lambda
    : forall R, MixinAlgebra (Lambda T (TypeOfResult T)) R (TypeOfResult T)
    := fun _ rec v =>
         match v with
         | App f a =>
           match (rec f, rec a) with
           | (Some tf, Some ta) =>
             match isArrowType (proj1_sig tf) with
             | Some (td, tc) =>
               if typeEquality (proj1_sig td) ta
               then Some tc
               else None
             | _ => None
             end
           | _ => None
           end
         | Lam td b =>
           match rec (b (Some td)) with
           | Some tc => Some (arrowType' td tc)
           | None => None
           end
         | Var v => v
         end.

  Global Instance TypeOf__Lambda
    : forall R, ProgramAlgebra ForTypeOf
                          (Lambda T (TypeOfResult T)) R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__Lambda _ |}.

  Global Instance WellFormedMendlerProgramAlgebra__TypeOf__Lambda
    : WellFormedMendlerProgramAlgebra TypeOf__Lambda.
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

End Lambda.
