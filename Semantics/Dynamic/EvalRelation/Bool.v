From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedProofAlgebra
     IndexedSubFunctor
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

(* Class MyClass (T : Set) := {}. *)

(* Class OtherClass (T : Set) `{MyClass T} := {}. *)

(* Definition Pack (T : Set) := {t : T | True}. *)

(* Axiom boolean : forall {T} `{OtherClass T}, bool -> Pack T. *)

(* Section Bool. *)

(*   Context {T} `{OtherClass T}. *)

(*   Inductive EvalRelation__Bool *)
(*             (EvalRelation__E : Pack T -> Prop) *)
(*     : Pack T -> Prop *)
(*     := *)
(*     | BoolValue : forall b, EvalRelation__Bool EvalRelation__E (boolean b) *)
(*   . *)

(* End Bool. *)

(* Derive Inversion inversion__Bool with *)
(*     ( *)
(*       forall {T} {CT : MyClass T} {OT : OtherClass T} *)
(*         EvalRelation__E *)
(*         e, *)
(*         @EvalRelation__Bool T CT OT EvalRelation__E e *)
(*     ). *)

Section Bool.

  Context

    {E}
    `{FunctorLaws E}
    `{! E supports Bool}
    `{! WellFormedSubFunctor Bool E}

    {V}
    `{FunctorLaws V}
    `{! V supports Bool}

  .

  Inductive EvalRelation__Bool
            (EvalRelation__E : (Fix E * Fix V) -> Prop)
    : (Fix E * Fix V) -> Prop
    :=
    | BoolValue : forall (b : bool), EvalRelation__Bool EvalRelation__E (booleanF b, booleanF b)
  .

  Global Instance IndexedFunctor_EvalRelation__Bool
    : IndexedFunctor (Fix E * Fix V) EvalRelation__Bool.
  Proof.
    constructor.
    move => A B i IH [] b.
    econstructor 1; apply IH => //.
  Qed.

  Variant ForEvalRelation := .

  (**
Sadly I can't find the incantation to make Coq generate this via [Derive
Inversion], so manually written...
   *)
  Definition EvalInversion__Bool
             (EvalRelation__E : Fix E * Fix V -> Prop)
             (ev : Fix E * Fix V)
             (P : (Fix E * Fix V)-indexedPropFunctor)
             (IH : forall b : bool,
                 P EvalRelation__E (booleanF b, booleanF b)
             )
             (ER : EvalRelation__Bool EvalRelation__E ev)
    : P EvalRelation__E ev
    :=
      match ER in (EvalRelation__Bool _ p) return (p = ev -> P EvalRelation__E ev) with
      | BoolValue _ b =>
        fun EQ =>
          eq_ind (booleanF b, booleanF b) (fun p => P EvalRelation__E p) (IH b) ev EQ
      end eq_refl.

  Definition EvalInversionClear__Bool
             (EvalRelation__E : Fix E * Fix V -> Prop)
             (ev : Fix E * Fix V)
             (P : (Fix E * Fix V)-indexedPropFunctor)
             (IH : forall b : bool,
                 (booleanF b, booleanF b) = ev ->
                 P EvalRelation__E (booleanF b, booleanF b))
             (ER : EvalRelation__Bool EvalRelation__E ev)
    : P EvalRelation__E ev
    :=
      match ER in (EvalRelation__Bool _ p) return (p = ev -> P EvalRelation__E ev) with
      | BoolValue _ b =>
        fun EQ =>
          eq_ind (booleanF b, booleanF b) (fun p => P EvalRelation__E p) (IH b EQ) ev EQ
      end eq_refl.

  (* not sure if this is useful *)
  Global Instance EvalRelationAlg__Bool
         {A} `{FunctorLaws A}
         `{SA : ! SubFunctor Bool A}
         {EvalRelation__A : (Fix E * Fix V)-indexedPropFunctor}
         `{! IndexedFunctor _ EvalRelation__A}
         `{SE : ! IndexedSubFunctor EvalRelation__Bool EvalRelation__A}
    : IndexedProofAlgebra ForEvalRelation EvalRelation__Bool (IndexedFix EvalRelation__A).
  Proof.
    constructor.
    move => ev.
    elim / @EvalInversionClear__Bool => b _.
    apply (iInject (H1 := SE)).
    apply BoolValue.
  Qed.

End Bool.
