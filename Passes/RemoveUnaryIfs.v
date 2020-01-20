(* From Coq Require Import Logic.FunctionalExtensionality. *)

From ExtensibleCompiler Require Import Algebra.
From ExtensibleCompiler Require Import Eval.
From ExtensibleCompiler Require Import Functor.
From ExtensibleCompiler Require Import ProgramAlgebra.
From ExtensibleCompiler Require Import ProofAlgebra.
From ExtensibleCompiler Require Import SubFunctor.
From ExtensibleCompiler Require Import Sum1.
From ExtensibleCompiler Require Import UniversalProperty.

From ExtensibleCompiler.Features Require Import Bool.
From ExtensibleCompiler.Features Require Import If1.
From ExtensibleCompiler.Features Require Import If2.
From ExtensibleCompiler.Features Require Import Stuck.
From ExtensibleCompiler.Features Require Import Unit.

Local Open Scope Sum1_scope.
Local Open Scope SubFunctor_scope.

(* Definition *)
(*   wrongRemoveUnaryIfsAlgebra *)
(*   {O} `{Functor O} `{FunctorLaws O} *)
(*   `{O supports UnitF} *)
(*   `{O supports If2F} *)
(*   T *)
(*   : ProgramAlgebra If1F T (Fix O) *)
(*   := *)
(*     {| *)
(*       programAlgebra := *)
(*         fun rec '(If1 c t) => *)
(*           proj1_sig unit; *)
(*     |}. *)

(* Definition *)
(*   removeUnaryIfsAlgebra' *)
(*   {O} `{Functor O} `{FunctorLaws O} *)
(*   `{O supports UnitF} *)
(*   `{O supports If2F} *)
(*   (T : Set) *)
(*   (rec : T -> Fix O) *)
(*   '(If1 condition thenBranch) *)
(*   : Fix O *)
(*   := *)
(*     if2 *)
(*       (rec condition) *)
(*       (rec thenBranch) *)
(*       unit. *)

(* Global *)
(*   Instance *)
(*   removeUnaryIfsAlgebra *)
(*   {O} `{Functor O} `{FunctorLaws O} *)
(*   `{O supports UnitF} *)
(*   `{O supports If2F} *)
(*   T *)
(*   : ProgramAlgebra If1F T (Fix O) *)
(*   := *)
(*     {| *)
(*       programAlgebra := removeUnaryIfsAlgebra' T; *)
(*     |}. *)

Definition
  removeUnaryIfsAlgebra'
  {O} `{Functor O} `{FunctorLaws O}
  `{O supports Unit}
  `{O supports If2}
  (T : Set)
  (rec : T -> WellFormedValue O)
  '(MkIf1 condition thenBranch)
  : WellFormedValue O
  :=
    if2__WF
      (rec condition)
      (rec thenBranch)
      unit__WF.

Global
  Instance
  removeUnaryIfsAlgebra
  {O} `{Functor O} `{FunctorLaws O}
  `{O supports Unit}
  `{O supports If2}
  : forall {T}, ProgramAlgebra If1 T (WellFormedValue O)
  := fun T =>
    {|
      programAlgebra := removeUnaryIfsAlgebra' T;
    |}.
