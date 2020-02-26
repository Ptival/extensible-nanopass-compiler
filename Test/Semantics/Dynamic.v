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

Local Open Scope Sum1.
Local Open Scope SubFunctor.

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
  := (WellTypedValue__Bool).

(* Definition SourceExpr := Bool + If1 + Unit. *)
(* Definition TargetExpr := Bool + If2 + Unit. *)
(* Definition Value := Bool + Stuck + Unit. *)

(* Definition EvalRelation__Source *)
(*   : (WellFormedValue SourceExpr * WellFormedValue Value)-indexedPropFunctor *)
(*   := (EvalRelation__Bool + EvalRelation__If1 + EvalRelation__Unit)%IndexedSum1. *)

(* Definition EvalRelation__Target *)
(*   : (WellFormedValue TargetExpr * WellFormedValue Value)-indexedPropFunctor *)
(*   := (EvalRelation__Bool + EvalRelation__If2 + EvalRelation__Unit)%IndexedSum1. *)

(* Definition removeUnaryIfs' *)
(*            (e : WellFormedValue SourceExpr) *)
(*   : WellFormedValue TargetExpr *)
(*   := removeUnaryIfs (L := SourceExpr) (V := TargetExpr) (proj1_sig e). *)

(* Theorem test *)
(*   : removeUnaryIfs' (if1 (boolean true) unit) = if2 (boolean true) unit unit. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

Variant ForRemoveUnaryIfsCorrectness := .

Declare Scope Prod1.
Delimit Scope Prod1 with Prod1.
Open Scope Prod1.

Variant Prod1 (F G : Set -> Set) (A : Set) : Set :=
| prod1 : F A -> G A -> (F * G)%Sum1 A
where
"F * G" := (Prod1 F G) : Prod1.

Arguments prod1 {F G A}.

Global Instance Functor__Prod1
       {F G} `{Functor F} `{Functor G}
  : Functor (F * G).
Proof.
  refine
    {|
      fmap := fun A B f '(prod1 fa ga) => prod1 (fmap f fa) (fmap f ga);
    |}.
  {
    move => A [] f g /=.
    do 2 rewrite fmapId //.
  }
  {
    move => A B C f g [] fa ga /=.
    do 2 rewrite fmapFusion //.
  }
Defined.

(*
NOTE:

I was trying to do a [WellFormedProofAlgebra2], that took a (Source * Value)
pair and rebuilt it, but you end up wanting a product functor, and then you'd
end up with [A <= A * B] constraints, which might not be true or not be worth it.

It seems like it might be better to do a [WellFormedProofAlgebra] where you only
change one of the two elements ofthe pair at the time, kind of like if you do
induction one variable at a time rather than induction on the pair.

Probably want to do induction on the source term, with the value universally
quantified in the output.
 *)

Definition AbstractCorrectnessStatement
           {S T V}
           `{Functor S} `{Functor T} `{Functor V}
           (EvalRelation__Source : (Fix S * Fix V)-indexedPropFunctor)
           (EvalRelation__Target : (Fix T * Fix V)-indexedPropFunctor)
           `{removeUnaryIfs__S : forall {R}, MixinAlgebra S R (WellFormedValue T)}
           (recRemoveUnaryIfs : WellFormedValue S -> WellFormedValue T)
           (s : Fix S)
           (UP'__s : FoldUP' s)
  : Prop
  := forall (v : Fix V),
    IndexedFix EvalRelation__Source (s, v) ->
    IndexedFix EvalRelation__Target
               ( proj1_sig (removeUnaryIfs__S recRemoveUnaryIfs (unwrapUP' s)),
                 v
               ).

Definition Correctness__ProofAlgebra
           {S T V}
           `{Functor S} `{Functor T} `{Functor V}
           (EvalRelation__Source : (Fix S * Fix V)-indexedPropFunctor)
           (EvalRelation__Target : (Fix T * Fix V)-indexedPropFunctor)
           `{RemoveUnaryIfs__S : forall {R}, ProgramAlgebra ForRemoveUnaryIfs S R (WellFormedValue T)}
  := forall recRemoveUnaryIfs,
    ProofAlgebra ForRemoveUnaryIfsCorrectness
                 S
                 (sig (UniversalPropertyP
                         (AbstractCorrectnessStatement
                            (removeUnaryIfs__S := fun _ => programAlgebra' RemoveUnaryIfs__S)
                            EvalRelation__Source
                            EvalRelation__Target
                            recRemoveUnaryIfs
                         )
                      )).

Lemma Correctness
      {S T V}
      `{Functor S} `{Functor T} `{Functor V}
      (EvalRelation__Source : (Fix S * Fix V)-indexedPropFunctor)
      (EvalRelation__Target : (Fix T * Fix V)-indexedPropFunctor)
      `{RemoveUnaryIfs__S : forall {R}, ProgramAlgebra ForRemoveUnaryIfs S R (WellFormedValue T)}
      `{! forall {R}, WellFormedCompoundProgramAlgebra ForRemoveUnaryIfs S S R (WellFormedValue T)}
      `{! WellFormedProgramAlgebra ForRemoveUnaryIfs S (WellFormedValue T)}
      (PA : Correctness__ProofAlgebra EvalRelation__Source EvalRelation__Target)
      `{! forall rec, WellFormedProofAlgebra (PA rec)}
  : forall (s : Fix S)
      (v : Fix V),
    FoldUP' s ->
    IndexedFix EvalRelation__Source (s, v) ->
    IndexedFix EvalRelation__Target (proj1_sig (removeUnaryIfs s), v).
Proof.
  move => s v UP'__s E__S.
  rewrite <- (wrapUP'_unwrapUP' s) => //.
  rewrite /= / removeUnaryIfs / mendlerFold / wrapF.
  rewrite wellFormedProgramAlgebra.
  case (Induction
          (PA := PA (fun s => removeUnaryIfs (proj1_sig s))) s _
       ) => [? C].
  apply C => //.
Qed.

(* Let's instantiate it *)

Definition SourceExpr := Bool + If1   + Unit.
Definition TargetExpr := Bool + If2   + Unit.
Definition Value      := Bool + Stuck + Unit.

Definition EvalRelation__Source
  : (Fix SourceExpr * Fix Value)-indexedPropFunctor
  := (EvalRelation__Bool + EvalRelation__If1 + EvalRelation__Unit)%IndexedSum1.

Definition EvalRelation__Target
  : (Fix TargetExpr * Fix Value)-indexedPropFunctor
  := (EvalRelation__Bool + EvalRelation__If2 + EvalRelation__Unit)%IndexedSum1.

Definition S' := If1.
Definition T' := BoolType.
Definition V' := If2.

(* Definition CorrectnessInstantiation *)
(*   := Correctness *)
