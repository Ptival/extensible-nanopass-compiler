(* From Coq Require Import Logic.FunctionalExtensionality. *)

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If1.
From ExtensibleCompiler.Syntax.Terms Require Import If2.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

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
  removeUnaryIfs
  {O} `{FunctorLaws O}
  `{! SubFunctor If2  O}
  `{! SubFunctor Unit O}
  : forall {T}, MixinAlgebra If1 T (WellFormedValue O)
  := fun _ rec '(MkIf1 condition thenBranch) =>
       if2 (rec condition) (rec thenBranch) unit.

Global Instance Algebra__RemoveUnaryIfs
  {O} `{FunctorLaws O}
  `{! O supports Unit}
  `{! O supports If2}
  : forall {T}, ProgramAlgebra If1 T (WellFormedValue O)
  := fun T => {| programAlgebra := removeUnaryIfs; |}.
