From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Passes Require Import RemoveUnaryIfs.

From ExtensibleCompiler.Semantics.Dynamic Require Import Bool.
From ExtensibleCompiler.Semantics.Dynamic Require Import If1.
From ExtensibleCompiler.Semantics.Dynamic Require Import If2.
From ExtensibleCompiler.Semantics.Dynamic Require Import Unit.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import If1.
From ExtensibleCompiler.Syntax.Terms Require Import If2.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSum1.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope Sum1_scope.
Local Open Scope SubFunctor_scope.

(* Create a language [L] that supports [Bool], [If2], and [Unit] *)
Definition L := (Bool + If2 + Unit).

(* Creates a type language [LT] that supports [Bool] and [Unit] *)
Definition V := (Bool + Stuck + Unit).

(* Create a concrete representation for the result of type-checking, so
   that it is easy to inspect manually *)
Inductive Result :=
| BoolValue (b : bool)
| UnitValue
| EvalFailed
.

Variant ComputeResult := .

(* Algebra to turn the extensible results into concrete results *)
Global Instance computeResult
  : forall T, ProgramAlgebra ComputeResult V T Result
  := fun _ =>
       {|
         programAlgebra :=
           fun rec =>
             (fun   '(MkBool b) => BoolValue b)
             || (fun 'Stuck      => EvalFailed)
             || (fun 'Unit       => UnitValue)
         ;
       |}.

Definition eval
           (b : WellFormedValue L)
  : Result
  := foldProgramAlgebra (Alg := computeResult) (proj1_sig (eval (proj1_sig b))).

Theorem regression__unit : eval unit = UnitValue.
Proof. reflexivity. Qed.

Theorem regression__true : eval (boolean true) = BoolValue true.
Proof. reflexivity. Qed.

Theorem regression__false : eval (boolean false) = BoolValue false.
Proof. reflexivity. Qed.

Theorem regression__if2True
  : eval (if2 (boolean true) (boolean true) (boolean false)) = BoolValue true.
Proof. reflexivity. Qed.

Theorem regression__if2False
  : eval (if2 (boolean false) (boolean true) (boolean false)) = BoolValue false.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedCondition
  : eval (if2 unit (boolean true) (boolean false)) = EvalFailed.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedBranchStillWorksLeft
  : eval (if2 (boolean true) (boolean true) unit) = BoolValue true.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedBranchStillWorksRight
  : eval (if2 (boolean false) unit (boolean false)) = BoolValue false.
Proof. reflexivity. Qed.

Definition SourceExpr := Bool + If1 + Unit.
Definition TargetExpr := Bool + If2 + Unit.
Definition Value := Bool + Stuck + Unit.

Definition Eval__Source
  : (WellFormedValue SourceExpr * WellFormedValue Value)-indexedProp
  := (Eval__Bool + Eval__If1)%IndexedSum1.

Definition Eval__Target
  : (WellFormedValue TargetExpr * WellFormedValue Value)-indexedProp
  := (Eval__Bool + Eval__If2 + Eval__Unit)%IndexedSum1.

Definition removeUnaryIfs
           (e : WellFormedValue SourceExpr)
  : WellFormedValue TargetExpr
  := removeUnaryIfs (L := SourceExpr) (V := TargetExpr) (proj1_sig e).

Theorem test
  : removeUnaryIfs (if1 (boolean true) unit) = if2 (boolean true) unit unit.
Proof. reflexivity. Qed.

Theorem removeUnaryIfsCorrectness
  : forall e v,
    IndexedFix Eval__Source (e, v) ->
    IndexedFix Eval__Target (removeUnaryIfs e, v).
Proof.
  move => e v S.
  pose proof (@iUnwrapFix) as U.
  specialize (U _ Eval__Source).

  (* TODO: IndexedFunctor instances *)

  admit.
Admitted.
