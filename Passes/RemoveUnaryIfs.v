From ExtensibleCompiler.Syntax.Terms Require Import If1.
From ExtensibleCompiler.Syntax.Terms Require Import If2.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition
  removeUnaryIfs
  {O} `{FunctorLaws O}
  `{! O supports If2}
  `{! O supports Unit}
  : forall {T}, MixinAlgebra If1 T (WellFormedValue O)
  := fun _ rec '(MkIf1 condition thenBranch) =>
       if2 (rec condition) (rec thenBranch) unit.

Global Instance Algebra__RemoveUnaryIfs
  {O} `{FunctorLaws O}
  `{! O supports Unit}
  `{! O supports If2}
  : forall {T}, ProgramAlgebra If1 T (WellFormedValue O)
  := fun T => {| programAlgebra := removeUnaryIfs; |}.
