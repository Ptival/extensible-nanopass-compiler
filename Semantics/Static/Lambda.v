From ExtensibleCompiler.Syntax.Terms Require Import Lambda.

From ExtensibleCompiler.Syntax.Types Require Import ArrowType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition typeOf__Lambda
           {LT} `{FunctorLaws LT}
           `{LT supports ArrowType}
           `{typeEqualityForLT : forall {T}, ProgramAlgebra ForTypeEquality LT T (TypeEqualityResult LT)}
  : forall {T}, MixinAlgebra (Lambda LT (TypeOfResult LT)) T (TypeOfResult LT)
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
       {T} `{FunctorLaws T}
       `{T supports ArrowType}
       `{typeEqualityForT : forall {R}, ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
  : forall {R}, ProgramAlgebra ForTypeOf (Lambda T (TypeOfResult T)) R (TypeOfResult T)
  := fun _ => {| programAlgebra := typeOf__Lambda; |}.
