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
Notation "'L'" := (Bool + If2 + Unit).

(* Creates a type language [LT] that supports [Bool] and [Unit] *)
Notation "'LT'" := (BoolType + UnitType).

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

Definition typeCheck (b : Fix L)
  : Result
  :=
  match typeOf L LT b with
  | Some e => mendlerFold (fun _ => programAlgebra) (proj1_sig e)
  | None   => IllTyped
  end.

Compute typeCheck (if2 (boolean true) (boolean true) (boolean false)).
Compute typeCheck (if2 unit (boolean true) (boolean false)).
Compute typeCheck (if2 (boolean true) unit (boolean false)).
Compute typeCheck (if2 (boolean true) unit unit).
