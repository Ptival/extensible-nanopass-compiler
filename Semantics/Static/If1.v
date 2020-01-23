From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If1.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.
From ExtensibleCompiler.Syntax.Types Require Import UnitType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import Types.

Local Open Scope SubFunctor_scope.

Definition typeOf__If1
           {LT} `{FunctorLaws LT}
           `{LT supports BoolType}
           `{LT supports UnitType}
  : forall {T}, MixinAlgebra If1 T (TypeOfResult LT)
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
       {LT} `{FunctorLaws LT}
       `{LT supports BoolType}
       `{LT supports UnitType}
  : forall {T}, ProgramAlgebra TypeOf If1 T (TypeOfResult LT)
  := fun _ => {| programAlgebra := typeOf__If1; |}.
