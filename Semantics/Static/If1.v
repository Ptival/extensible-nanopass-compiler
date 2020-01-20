From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If1.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.
From ExtensibleCompiler.Syntax.Types Require Import UnitType.

From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import Types.

Local Open Scope SubFunctor_scope.

Definition typeOf_If1
           {LT} `{FunctorLaws LT} `{BoolType <= LT} `{UnitType <= LT}
           (R : Set) (rec : R -> TypeOfResult LT)
           (e : If1 R)
  : TypeOfResult LT
  :=
    match e with
    | MkIf1 c t =>
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
      end
    end.

Global Instance TypeOf_If1
       {LT} `{FunctorLaws LT} `{BoolType <= LT} `{UnitType <= LT}
  : forall T, ProgramAlgebra If1 T (TypeOfResult LT)
  := fun T => {| programAlgebra := typeOf_If1 T |}.
