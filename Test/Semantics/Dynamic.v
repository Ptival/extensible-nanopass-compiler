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

Definition p
  : MixinAlgebra If1 (WellFormedValue (If2 + Unit)) (WellFormedValue (If2 + Unit))
  := programAlgebra.

Definition q := p id.

Definition e1
  : WellFormedValue (Bool + If1 + Unit)
  := if1 (boolean true) unit.

Definition v1
  : Fix (Bool + If1 + Unit)
  := proj1_sig e1.

(* Definition check1 := evalAlgebra (F := Unit) (R := Unit). *)
(* Definition check2 := evalAlgebra (F := Bool) (R := Unit + Bool). *)
(* Definition check3 := evalAlgebra (F := Bool) (R := Bool + Unit). *)
(* Definition check4 := evalAlgebra (F := Unit + Bool) (R := Bool + Unit). *)

Definition MixinAlgebra' I O := MixinAlgebra I O O.

(* From now on, code writes itself, for instance: *)

Definition test1
  : Fix Bool -> WellFormedValue (Bool + If2 + Unit)
  := fold (programAlgebra id).

Definition V := WellFormedValue (Bool + If2 + Unit).

(* Definition removeUnaryIfsMixin *)
(*   : MixinAlgebra' (Bool + If1) V *)
(*   := programAlgebra. *)

Definition removeUnaryIfsFromFix
  : Fix (Bool + If1) -> WellFormedValue (Bool + If2 + Unit)
  := fold (programAlgebra id).

Definition evalWellFormed I O `{FunctorLaws I} `{FunctorLaws O}
           `{ProgramAlgebra I (WellFormedValue O) (WellFormedValue O)}
  : WellFormedValue I -> WellFormedValue O
  := fun v => fold (programAlgebra id) (proj1_sig v).

Definition removeUnaryIfs
  : WellFormedValue (Bool + If1) -> WellFormedValue (Bool + If2 + Unit)
  := evalWellFormed _ _.

Definition exprIf1
  : WellFormedValue (Bool + If1)
  := if1 (boolean true) (boolean false).

Definition exprIf2
  : WellFormedValue (Bool + If2 + Unit)
  := if2 (boolean true) (boolean false) unit.

Theorem removeUnaryIfsExprIf1
  : removeUnaryIfs exprIf1 = exprIf2.
Proof.
  reflexivity.
Qed.

Theorem removeUnaryIfsSyntacticCorrectness :
  forall c t,
    removeUnaryIfs (if1 c t) = if2 (removeUnaryIfs c) (removeUnaryIfs t) unit.
Proof.
  reflexivity.
Qed.

Delimit Scope IndexedSum1_scope with IndexedSum1.

Definition SourceExpr := Bool + If1.
Definition TargetExpr := Bool + If2 + Unit.
Definition Value := Bool + Stuck + Unit.

Definition Eval__Source
  : (WellFormedValue SourceExpr * WellFormedValue Value)-indexedProp
  := (Eval__Bool + Eval__If1)%IndexedSum1.

Definition Eval__Target
  : (WellFormedValue TargetExpr * WellFormedValue Value)-indexedProp
  := (Eval__Bool + Eval__If2 + Eval__Unit)%IndexedSum1.

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
