From Coq Require Import
     ssreflect
.

From ExtensibleCompiler Require Import

     Semantics.Static.All.Bool
     Semantics.Static.All.BoolType
     Semantics.Static.All.If2
     Semantics.Static.All.Unit
     Semantics.Static.All.UnitType
     Semantics.Static.TypeOf

     Syntax.Terms.Bool
     Syntax.Terms.If1
     Syntax.Terms.If2
     Syntax.Terms.Unit
     Syntax.Types.BoolType
     Syntax.Types.UnitType

     Theory.Algebra
     Theory.Eval
     Theory.Functor
     Theory.ProgramAlgebra
     Theory.SubFunctor
     Theory.Sum1
     Theory.Types
     Theory.UniversalProperty

.

Local Open Scope SubFunctor.

(* Create an expression language that supports [Bool], [If2], and [Unit] *)
Definition E := (Bool + If2 + Unit)%Sum1.

(* Create a type language that supports [Bool] and [Unit] *)
Definition T := (BoolType + UnitType)%Sum1.

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
  : forall R, ProgramAlgebra ForComputeResult T R Result
  := fun _ =>
       {|
         programAlgebra :=
           fun rec =>
             (fun   'MkBoolType => WellTypedBool)
             || (fun 'MkUnitType => WellTypedUnit)
         ;
       |}%Sum1.

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
