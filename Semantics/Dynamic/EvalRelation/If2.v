From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
     If2
     Stuck
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     IndexedFunctor
     SubFunctor
     UniversalProperty
.

Local Open Scope SubFunctor.

Section If2.

  Context

    {E}
    `{Functor E}
    `{! E supports If2}

    {V}
    `{Functor V}
    `{! V supports Bool}

  .

  Inductive EvalRelation__If2
            (EvalRelation__E : (Fix E * Fix V) -> Prop)
    : (Fix E * Fix V) -> Prop
    :=
    | If2True : forall c t e t',
        EvalRelation__E (c, booleanF true) ->
        EvalRelation__E (t, t') ->
        EvalRelation__If2 EvalRelation__E (if2F c t e, t')
    | If2False : forall c t e e',
        EvalRelation__E (c, booleanF false) ->
        EvalRelation__E (e, e') ->
        EvalRelation__If2 EvalRelation__E (if2F c t e, e')
  .

  Global Instance IndexedFunctor_EvalRelation__If2
    : IndexedFunctor (Fix E * Fix V) EvalRelation__If2.
  Proof.
    constructor.
    move => A B i IH [].
    - econstructor 1; apply IH => //.
    - econstructor 2; apply IH => //.
  Qed.

  Definition EvalInversionClear__If2
             (EvalRelation__E : Fix E * Fix V -> Prop)
             (ev : Fix E * Fix V)
             (P : (Fix E * Fix V)-indexedPropFunctor)
             (IH__True : forall c t e t',
                 EvalRelation__E (c, booleanF true) ->
                 EvalRelation__E (t, t') ->
                 (if2F c t e, t') = ev ->
                 P EvalRelation__E (if2F c t e, t')
             )
             (IH__False : forall c t e e',
                 EvalRelation__E (c, booleanF false) ->
                 EvalRelation__E (e, e') ->
                 (if2F c t e, e') = ev ->
                 P EvalRelation__E (if2F c t e, e')
             )
             (ER : EvalRelation__If2 EvalRelation__E ev)
    : P EvalRelation__E ev
    :=
      match ER in (EvalRelation__If2 _ p) return (p = ev -> P EvalRelation__E ev) with
      | If2True _ c t e t' E__c E__t =>
        fun EQ => eq_ind (if2F c t e, t') (P EvalRelation__E) (IH__True c t e t' E__c E__t EQ) ev EQ
      | If2False _ c t e e' E__c E__e =>
        fun EQ => eq_ind (if2F c t e, e') (P EvalRelation__E) (IH__False c t e e' E__c E__e EQ) ev EQ
      end eq_refl.

End If2.
