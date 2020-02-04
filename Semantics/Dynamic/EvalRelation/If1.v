From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
     If1
     Unit
.

From ExtensibleCompiler.Theory Require Import
     Functor
     IndexedFunctor
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor_scope.

Section If1.

  (*
We now define an extensible big-step semantics relation [EvalRelation] that
captures how [If1] evaluates in a larger language [E].
   *)

  Context

    {E}
    `{FunctorLaws E}
    `{! E supports If1}

    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
    `{! V supports Unit}

  .

  Inductive EvalRelation__If1
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | If1True : forall c t t',
        EvalRelation__E (c, boolean true) ->
        EvalRelation__E (t, t') ->
        EvalRelation__If1 EvalRelation__E (if1 c t, t')
    | If1False : forall c t,
        EvalRelation__E (c, boolean false) ->
        EvalRelation__If1 EvalRelation__E (if1 c t, unit)
  .

  Global Instance IndexedFunctor_EvalRelation__If1
    : IndexedFunctor (WellFormedValue E * WellFormedValue V) EvalRelation__If1.
  Proof.
    constructor.
    move => A B i IH [].
    - econstructor 1; apply IH => //.
    - econstructor 2; apply IH => //.
  Qed.

  Definition EvalInversionClear__If1
             (EvalRelation__E : WellFormedValue E * WellFormedValue V -> Prop)
             (ev : WellFormedValue E * WellFormedValue V)
             (P : (WellFormedValue E * WellFormedValue V)-indexedPropFunctor)
             (IH__True : forall c t t',
                 EvalRelation__E (c, boolean true) ->
                 EvalRelation__E (t, t') ->
                 (if1 c t, t') = ev ->
                 P EvalRelation__E (if1 c t, t')
             )
             (IH__False : forall c t,
                 EvalRelation__E (c, boolean false) ->
                 (if1 c t, unit) = ev ->
                 P EvalRelation__E (if1 c t, unit)
             )
             (ER : EvalRelation__If1 EvalRelation__E ev)
    : P EvalRelation__E ev
    :=
      match ER in (EvalRelation__If1 _ p) return (p = ev -> P EvalRelation__E ev) with
      | If1True _ c t t' E__c E__t =>
        fun EQ => eq_ind (if1 c t, t') (P EvalRelation__E) (IH__True c t t' E__c E__t EQ) ev EQ
      | If1False _ c t E__c =>
        fun EQ => eq_ind (if1 c t, unit) (P EvalRelation__E) (IH__False c t E__c EQ) ev EQ
      end eq_refl.

End If1.
