From ExtensibleCompiler.Features Require Import Bool.
From ExtensibleCompiler.Features Require Import Types.

From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.

From ExtensibleCompiler.Types Require Import BoolType.

Local Open Scope SubFunctor_scope.

Definition typeOf_Bool
           {LT} `{FunctorLaws LT} `{BoolType <= LT}
           (R : Set) (rec : R -> TypeOfResult LT)
           (e : Bool R)
  : TypeOfResult LT
  :=
    match e with
    | MkBool _ => Some boolType'
    end.

Global Instance TypeOf_Bool
       {LT} `{FunctorLaws LT} `{BoolType <= LT}
  : forall T, ProgramAlgebra Bool T (TypeOfResult LT)
  := fun T => {| programAlgebra := typeOf_Bool T |}.
