From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Passes Require Import
     RemoveUnaryIfs
.

From ExtensibleCompiler.Semantics.All Require Import
     Bool
     If1
     If2
     Lambda
     Unit
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
     If1
     If2
     Stuck
     Unit
.

From ExtensibleCompiler.Syntax.Types Require Import
     BoolType
     UnitType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Environment
     Eval
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedSum1
     ProgramAlgebra
     ProofAlgebra
     SubFunctor
     Sum1
     Types
     TypeSoundness
     UniversalProperty
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

Variant ForComputeResult := .

(* Algebra to turn the extensible results into concrete results *)
Global Instance computeResult
  : forall R, ProgramAlgebra ForComputeResult V R Result
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

Definition SourceExpr := Bool + If1 + Unit.
Definition TargetExpr := Bool + If2 + Unit.
Definition Value := Bool + Stuck + Unit.

Definition EvalRelation__Source
  : (WellFormedValue SourceExpr * WellFormedValue Value)-indexedPropFunctor
  := (EvalRelation__Bool + EvalRelation__If1 + EvalRelation__Unit)%IndexedSum1.

Definition EvalRelation__Target
  : (WellFormedValue TargetExpr * WellFormedValue Value)-indexedPropFunctor
  := (EvalRelation__Bool + EvalRelation__If2 + EvalRelation__Unit)%IndexedSum1.

Definition removeUnaryIfs'
           (e : WellFormedValue SourceExpr)
  : WellFormedValue TargetExpr
  := removeUnaryIfs (L := SourceExpr) (V := TargetExpr) (proj1_sig e).

Theorem test
  : removeUnaryIfs' (if1 (boolean true) unit) = if2 (boolean true) unit unit.
Proof.
  reflexivity.
Qed.

Variant ForRemoveUnaryIfsCorrectness := .

Definition AbstractCorrectnessStatement
           {S T V}
           `{FunctorLaws S} `{FunctorLaws T} `{FunctorLaws V}
           (EvalRelation__Source : (WellFormedValue S * WellFormedValue V)-indexedPropFunctor)
           (EvalRelation__Target : (WellFormedValue T * WellFormedValue V)-indexedPropFunctor)
           `{removeUnaryIfs__S : forall {R}, MixinAlgebra S R (WellFormedValue T)}
           (recRemoveUnaryIfs : WellFormedValue S -> WellFormedValue T)
           (ev : Fix S * Fix V)
           (UP'__ev : FoldUP' (fst ev) /\ FoldUP' (snd ev))
  : Prop
  := IndexedFix EvalRelation__Source
                ( exist _ (fst ev) (proj1 UP'__ev),
                  exist _ (snd ev) (proj2 UP'__ev)
                ) ->
     IndexedFix EvalRelation__Target
                ( removeUnaryIfs__S recRemoveUnaryIfs (unwrapUP' (fst ev)),
                  wrapUP' (unwrapUP' (snd ev))
                ).

Definition Correctness__ProofAlgebra
           {S T V}
           `{FunctorLaws S} `{FunctorLaws T} `{FunctorLaws V}
           (EvalRelation__Source : (WellFormedValue S * WellFormedValue V)-indexedPropFunctor)
           (EvalRelation__Target : (WellFormedValue T * WellFormedValue V)-indexedPropFunctor)
           `{RemoveUnaryIfs__S : forall {R}, ProgramAlgebra ForRemoveUnaryIfs S R (WellFormedValue T)}
  := forall recRemoveUnaryIfs,
    ProofAlgebra ForRemoveUnaryIfsCorrectness
                 SourceExpr
                 (sig (UniversalPropertyP2
                         (AbstractCorrectnessStatement
                            (removeUnaryIfs__S := fun _ => programAlgebra' RemoveUnaryIfs__S)
                            EvalRelation__Source
                            EvalRelation__Target
                            recRemoveUnaryIfs
                         )
                      )).

Lemma Correctness
      {S T V}
      `{FunctorLaws S} `{FunctorLaws T} `{FunctorLaws V}
      (EvalRelation__Source : (WellFormedValue S * WellFormedValue V)-indexedPropFunctor)
      (EvalRelation__Target : (WellFormedValue T * WellFormedValue V)-indexedPropFunctor)
      `{RemoveUnaryIfs__S : forall {R}, ProgramAlgebra ForRemoveUnaryIfs S R (WellFormedValue T)}
      (correctness__ProofAlgebra : Correctness__ProofAlgebra EvalRelation__Source EvalRelation__Target)
      (WF_eval_Soundness_alg_F :
         forall recRemoveUnaryIfs,
           WellFormedProofAlgebra2 (correctness__ProofAlgebra recRemoveUnaryIfs)
      )
  : forall (ev : WellFormedValue SourceExpr * WellFormedValue Value),
    IndexedFix EvalRelation__Source
               ( _, _
               ) ->
    IndexedFix EvalRelation__Target
               ( removeUnaryIfs _, _
               ).

Theorem removeUnaryIfsCorrectness
  : forall e v,
    IndexedFix EvalRelation__Source (e, v) ->
    IndexedFix EvalRelation__Target (removeUnaryIfs e, v).
Proof.
  move => e v S.


  pose proof @Induction2.


  apply (Induction2 ().

  apply iWrapFix.
  case : (iUnwrapFix (e, v) S) => [ [ | ] |  ].

  {
    (* for some reason we need the @ to help type class resolution... *)
    elim / @EvalInversionClear__Bool => b [] <- <- .
    left.
    left.
    apply Bool.BoolValue.
  }

  {
    elim / @EvalInversionClear__If1.

    {
      move => c t t' E__c E__t [] <- <- .
      left.
      right.
      apply If2True.

      {
        apply iWrapFix.
        case : (iUnwrapFix (c, boolean true) E__c) => [ [ | ] | ].

        {
          elim / @EvalInversionClear__Bool => b.
          rewrite [@boolean]lock.
          move => [].
          unlock.
          move => <- [] EQ.

          (* can't find a nicer way of making this inversion happen *)
          pose proof (wrapF_inversion' (E := Value) (boolean b) (boolean true) EQ) as EQ'.
          move : EQ EQ' => _ [] ->.

          left.
          left.
          apply Bool.BoolValue.
        }

        {
          elim / @EvalInversionClear__If1.

          {
            move =>
          }

          admit.
        }
        {
          admit.
        }
      }
      {
        admit.
      }
    }
    {
      case : (iUnwrapFix (c, boolean false) H) => [ [E | E] | E ].
      {
        inversion E.
        left.
        right.
        constructor.
        {
          apply iWrapFix.

        }
      }
      admit.
    }
  }
  {
    inversion_clear E.
    right.
    constructor.
  }
Qed.
