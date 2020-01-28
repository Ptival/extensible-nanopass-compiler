From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler Require Import

     Passes.RemoveUnaryIfs

     Semantics.All.Bool
     Semantics.All.If1
     Semantics.All.If2
     Semantics.All.Lambda
     Semantics.All.Unit

     Syntax.Terms.Bool
     Syntax.Terms.If1
     Syntax.Terms.If2
     Syntax.Terms.Stuck
     Syntax.Terms.Unit

     Syntax.Types.BoolType
     Syntax.Types.UnitType

     Theory.Algebra
     Theory.Environment
     Theory.Eval
     Theory.Functor
     Theory.IndexedAlgebra
     Theory.IndexedFunctor
     Theory.IndexedSum1
     Theory.ProgramAlgebra
     Theory.ProofAlgebra
     Theory.SubFunctor
     Theory.Sum1
     Theory.Types
     Theory.TypeSoundness
     Theory.UniversalProperty

.

Local Open Scope Sum1_scope.
Local Open Scope SubFunctor_scope.

(* Create a type language [T] *)
Definition T := (BoolType + UnitType).

(* Create an expression language [E] *)
Definition E := (Bool + If2 + Unit).

(* Create a value language [V] *)
Definition V := (Bool + Stuck + Unit).

(*
Create a concrete representation for the result of type-checking, so that it is
easy to inspect manually
 *)
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

Definition eval'
           (e : WellFormedValue E)
  : Result
  := foldProgramAlgebra
       (Alg := computeResult)
       (proj1_sig (eval (L := E) (V := V) (proj1_sig e) (empty _))).

Theorem regression__unit : eval' unit = UnitValue.
Proof. reflexivity. Qed.

Theorem regression__true : eval' (boolean true) = BoolValue true.
Proof. reflexivity. Qed.

Theorem regression__false : eval' (boolean false) = BoolValue false.
Proof. reflexivity. Qed.

Theorem regression__if2True
  : eval' (if2 (boolean true) (boolean true) (boolean false)) = BoolValue true.
Proof. reflexivity. Qed.

Theorem regression__if2False
  : eval' (if2 (boolean false) (boolean true) (boolean false)) = BoolValue false.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedCondition
  : eval' (if2 unit (boolean true) (boolean false)) = EvalFailed.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedBranchStillWorksLeft
  : eval' (if2 (boolean true) (boolean true) unit) = BoolValue true.
Proof. reflexivity. Qed.

Theorem regression__if2IllTypedBranchStillWorksRight
  : eval' (if2 (boolean false) unit (boolean false)) = BoolValue false.
Proof. reflexivity. Qed.

(*
Let's make sure that we can instantiate the statement of type soundness through
evaluation.
 *)

Definition WellTyped__E
  : (TypedExpr T V)-indexedPropFunctor
  := (WellTyped__Bool).

(* Algebra to turn the extensible results into concrete results *)

Theorem Soundness__EvalE
  : forall (e : WellFormedValue E) Gamma (tau : TypeFix T),
    typeOf (proj1_sig e) = Some tau ->
    WellTyped WellTyped__E tau (eval (proj1_sig e) Gamma).
Proof.
  eapply Soundness => //.
  typeclasses eauto.
  typeclasses eauto.
Admitted.








Definition SourceExpr := Bool + If1 + Unit.
Definition TargetExpr := Bool + If2 + Unit.
Definition Value := Bool + Stuck + Unit.

Definition EvalRelation__Source
  : (WellFormedValue SourceExpr * WellFormedValue Value)-indexedPropFunctor
  := (EvalRelation__Bool + EvalRelation__If1 + EvalRelation__Unit)%IndexedSum1.

Definition EvalRelation__Target
  : (WellFormedValue TargetExpr * WellFormedValue Value)-indexedPropFunctor
  := (EvalRelation__Bool + EvalRelation__If2 + EvalRelation__Unit)%IndexedSum1.

Definition removeUnaryIfs
           (e : WellFormedValue SourceExpr)
  : WellFormedValue TargetExpr
  := removeUnaryIfs (L := SourceExpr) (V := TargetExpr) (proj1_sig e).

Theorem test
  : removeUnaryIfs (if1 (boolean true) unit) = if2 (boolean true) unit unit.
Proof. reflexivity. Qed.

Theorem removeUnaryIfsCorrectness
  : forall e v,
    IndexedFix EvalRelation__Source (e, v) ->
    IndexedFix EvalRelation__Target (removeUnaryIfs e, v).
Proof.
  move => e v S.
  pose proof (@iUnwrapFix) as U.
  specialize (U _ EvalRelation__Source).

  (* TODO: IndexedFunctor instances *)

  admit.
Admitted.
