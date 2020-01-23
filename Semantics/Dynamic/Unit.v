From Coq Require Import String.

From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition eval__Unit
           {V} `{FunctorLaws V}
           `{! V supports Unit}
  : forall {T}, MixinAlgebra Unit T (WellFormedValue V)
  := fun T rec '(MkUnit) => unit.

Global Instance EvalAlgebra__Unit
       {V} `{FunctorLaws V}
       `{! V supports Unit}
  : forall {T}, ProgramAlgebra Eval Unit T (WellFormedValue V)
  := fun T => {| programAlgebra := eval__Unit; |}.

Inductive Eval__Unit
          {L V}
          `{FunctorLaws L} `{FunctorLaws V}
          `{! L supports Unit}
          `{! V supports Unit}
          (Eval : (WellFormedValue L * WellFormedValue V) -> Prop)
  : (WellFormedValue L * WellFormedValue V) -> Prop
  :=
  | UnitValue : Eval__Unit Eval (unit, unit)
.
