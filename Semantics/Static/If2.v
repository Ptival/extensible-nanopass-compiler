From ExtensibleCompiler.Syntax.Terms Require Import If2.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.

Local Open Scope SubFunctor_scope.

Definition typeOf_If2
           {LT} `{FunctorLaws LT} `{BoolType <= LT}
           {typeEqualityForLT : forall T, ProgramAlgebra LT T (TypeEqualityResult LT)}
           (R : Set) (rec : R -> TypeOfResult LT)
           (exp : If2 R)
  : TypeOfResult LT
  :=
    match exp with
    | MkIf2 c t e =>
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
      end
    end.

Global Instance TypeOf_If2
       {LT} `{FunctorLaws LT} `{BoolType <= LT}
       {typeEqualityForLT : forall T, ProgramAlgebra LT T (TypeEqualityResult LT)}
  : forall T, ProgramAlgebra If2 T (TypeOfResult LT)
  := fun T => {| programAlgebra := typeOf_If2 T |}.
