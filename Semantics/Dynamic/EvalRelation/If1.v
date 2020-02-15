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
     Algebra
     Functor
     IndexedFunctor
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor.

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
            (EvalRelation__E : (Fix E * Fix V) -> Prop)
    : (Fix E * Fix V) -> Prop
    :=
    | If1True : forall c t t',
        EvalRelation__E (c, booleanF true) ->
        EvalRelation__E (t, t') ->
        EvalRelation__If1 EvalRelation__E (if1F c t, t')
    | If1False : forall c t,
        EvalRelation__E (c, booleanF false) ->
        EvalRelation__If1 EvalRelation__E (if1F c t, unitF)
  .

  Global Instance IndexedFunctor_EvalRelation__If1
    : IndexedFunctor (Fix E * Fix V) EvalRelation__If1.
  Proof.
    constructor.
    move => A B i IH [].
    - econstructor 1; apply IH => //.
    - econstructor 2; apply IH => //.
  Qed.

  Definition EvalInversionClear__If1
             (EvalRelation__E : Fix E * Fix V -> Prop)
             (ev : Fix E * Fix V)
             (P : (Fix E * Fix V)-indexedPropFunctor)
             (IH__True : forall c t t',
                 EvalRelation__E (c, booleanF true) ->
                 EvalRelation__E (t, t') ->
                 (if1F c t, t') = ev ->
                 P EvalRelation__E (if1F c t, t')
             )
             (IH__False : forall c t,
                 EvalRelation__E (c, booleanF false) ->
                 (if1F c t, unitF) = ev ->
                 P EvalRelation__E (if1F c t, unitF)
             )
             (ER : EvalRelation__If1 EvalRelation__E ev)
    : P EvalRelation__E ev
    :=
      match ER in (EvalRelation__If1 _ p) return (p = ev -> P EvalRelation__E ev) with
      | If1True _ c t t' E__c E__t =>
        fun EQ => eq_ind (if1F c t, t') (P EvalRelation__E) (IH__True c t t' E__c E__t EQ) ev EQ
      | If1False _ c t E__c =>
        fun EQ => eq_ind (if1F c t, unitF) (P EvalRelation__E) (IH__False c t E__c EQ) ev EQ
      end eq_refl.

End If1.
