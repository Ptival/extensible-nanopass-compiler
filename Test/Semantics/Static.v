From ExtensibleCompiler.Semantics.Static Require Import Bool.
From ExtensibleCompiler.Semantics.Static Require Import If2.
From ExtensibleCompiler.Semantics.Static Require Import Unit.

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

(* Create a language [L] that supports [Bool], [If2], and [Unit] *)
Definition L := (Bool + If2 + Unit).

(* Creates a type language [LT] that supports [Bool] and [Unit] *)
Definition LT := (BoolType + UnitType).

(* Create a concrete representation for the result of type-checking, so
   that it is easy to inspect manually *)
Inductive Result :=
| WellTypedBool
| WellTypedUnit
| IllTyped
.

(* Algebra to turn the extensible results into concrete results *)
Global Instance computeResult
  : forall T, ProgramAlgebra LT T Result
  := fun T =>
       {|
         programAlgebra :=
           fun rec lt =>
             match lt with
             | inl1 MkBoolType => WellTypedBool
             | inr1 MkUnitType => WellTypedUnit
             end;
       |}.

Definition typeCheck
           (b : WellFormedValue L)
  : Result
  :=
    match typeOf (proj1_sig b) with
    | Some e => foldProgramAlgebra (Alg := computeResult) (proj1_sig e)
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
