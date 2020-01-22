From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.

Local Open Scope SubFunctor_scope.

Definition typeOf_Bool
           {LT} `{FunctorLaws LT} `{SubFunctor BoolType LT}
           (R : Set) (rec : R -> TypeOfResult LT)
           (e : Bool R)
  : TypeOfResult LT
  :=
    match e with
    | MkBool _ => Some boolType'
    end.

Global Instance TypeOf_Bool
       {LT} `{FunctorLaws LT} `{SubFunctor BoolType LT}
  : forall T, ProgramAlgebra Bool T (TypeOfResult LT)
  := fun T => {| programAlgebra := typeOf_Bool T |}.
