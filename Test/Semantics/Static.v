From ExtensibleCompiler.Semantics.Static.All Require Import Bool.
From ExtensibleCompiler.Semantics.Static.All Require Import If2.
From ExtensibleCompiler.Semantics.Static.All Require Import Unit.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If1.
From ExtensibleCompiler.Syntax.Terms Require Import If2.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.
From ExtensibleCompiler.Syntax.Types Require Import UnitType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

(* Create an expression language that supports [Bool], [If2], and [Unit] *)
Definition E := (Bool + If2 + Unit).

(* Create a type language that supports [Bool] and [Unit] *)
Definition T := (BoolType + UnitType).

(* Create a concrete representation for the result of type-checking, so
   that it is easy to inspect manually *)
Inductive Result :=
| WellTypedBool
| WellTypedUnit
| IllTyped
.

Variant ForComputeResult := .

(* Algebra to turn the extensible results into concrete results *)
Global Instance computeResult
  : forall {R}, ProgramAlgebra ForComputeResult T R Result
  := fun _ =>
       {|
         programAlgebra :=
           fun rec =>
             (fun   'MkBoolType => WellTypedBool)
             || (fun 'MkUnitType => WellTypedUnit)
         ;
       |}.

Definition typeCheck
           (e : WellFormedValue E)
  : Result
  :=
    match typeOf (E := E) (T := T) (proj1_sig e) with
    | Some t => foldProgramAlgebra (Alg := @computeResult) (proj1_sig t)
    | None   => IllTyped
    end.

Theorem regression__unit : typeCheck unit = WellTypedUnit.
Proof. reflexivity. Qed.

Theorem regression__true : typeCheck (boolean true) = WellTypedBool.
Proof. reflexivity. Qed.

Theorem regression__false : typeCheck (boolean false) = WellTypedBool.
Proof. reflexivity. Qed.

Theorem regression__if2Unit
  : typeCheck (if2 (boolean true) unit unit) = WellTypedUnit.
Proof. reflexivity. Qed.

Theorem regression__if2Bool
  : typeCheck (if2 (boolean true) (boolean true) (boolean false)) = WellTypedBool.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedCondition
  : typeCheck (if2 unit (boolean true) (boolean false)) = IllTyped.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedBranchMismatch
  : typeCheck (if2 (boolean true) (boolean true) unit) = IllTyped.
Proof. reflexivity. Qed.
