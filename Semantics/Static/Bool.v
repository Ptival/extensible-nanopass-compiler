From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.

Local Open Scope SubFunctor_scope.

Definition typeOf__Bool
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : forall {T}, MixinAlgebra Bool T (TypeOfResult LT)
  := fun _ rec '(MkBool _) => Some boolType'.

Global Instance TypeOf__Bool
       {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : forall {T}, ProgramAlgebra Bool T (TypeOfResult LT)
  := fun _ => {| programAlgebra := typeOf__Bool; |}.
