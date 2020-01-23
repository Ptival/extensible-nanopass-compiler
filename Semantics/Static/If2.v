From ExtensibleCompiler.Syntax.Terms Require Import If2.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.

Local Open Scope SubFunctor_scope.

Definition typeOf__If2
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
           {typeEqualityForLT : forall T, ProgramAlgebra TypeEquality LT T (TypeEqualityResult LT)}
  : forall {T}, MixinAlgebra If2 T (TypeOfResult LT)
  := fun _ rec '(MkIf2 c t e) =>
       match rec c with
       | Some cType =>
         if isBoolType (proj1_sig cType)
         then
           match (rec t, rec e) with
           | (Some tType, Some eType) =>
             if typeEquality LT (proj1_sig tType) eType
             then Some tType
             else None
           | _ => None
           end
         else None
       | None => None
       end.

Global Instance TypeOf__If2
       {LT} `{FunctorLaws LT} `{LT supports BoolType}
       {typeEqualityForLT : forall T, ProgramAlgebra TypeEquality LT T (TypeEqualityResult LT)}
  : forall {T}, ProgramAlgebra TypeOf If2 T (TypeOfResult LT)
  := fun _ => {| programAlgebra := typeOf__If2; |}.
