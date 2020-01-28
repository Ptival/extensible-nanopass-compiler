From Coq Require Import ssreflect.

From ExtensibleCompiler.Syntax.Terms Require Import If2.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section If2.

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
    `{! WellFormedSubFunctor BoolType T}

    {typeEqualityForT : forall R, ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
  .

  Definition typeOf__If2
    : forall {R}, MixinAlgebra If2 R (TypeOfResult T)
    := fun _ rec '(MkIf2 c t e) =>
         match rec c with
         | Some cType =>
           if isBoolType (proj1_sig cType)
           then
             match (rec t, rec e) with
             | (Some tType, Some eType) =>
               if typeEquality (proj1_sig tType) eType
               then Some tType
               else None
             | _ => None
             end
           else None
         | None => None
         end.

  Global Instance TypeOf__If2
    : forall {R}, ProgramAlgebra ForTypeOf If2 R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__If2; |}.

  Definition TypeOf__If2'
    : forall R, ProgramAlgebra ForTypeOf If2 R (TypeOfResult T)
    := fun _ => TypeOf__If2.

  Global Instance WellFormedMendlerAlgebra_TypeOf__If2
    : WellFormedMendlerAlgebra TypeOf__If2'.
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

End If2.
