From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax.Terms Require Import
     If2
.

From ExtensibleCompiler.Syntax.Types Require Import
     BoolType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     IndexedAlgebra
     IndexedFunctor
     IndexedProofAlgebra
     IndexedSubFunctor
     ProgramAlgebra
     SubFunctor
     TypeSoundness
     UniversalProperty
.

Local Open Scope SubFunctor.

Section If2.

  Context

    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
    `{! WellFormedSubFunctor BoolType T}

    {E}
    `{FunctorLaws E}
    `{E supports If2}

    {V}
    `{FunctorLaws V}

  .

  Inductive WellTypedValue__If2
            (WTV : (TypedExpr T V)-indexedProp)
    : (TypedExpr T V)-indexedProp
    :=
    | WellTypedValue__if2 : forall t v,
        WTV {| type := t; expr := v |} ->
        WellTypedValue__If2 WTV {| type := t; expr := v |}
  .

  Global Instance IndexedFunctor_WellTypedValue__If2
    : IndexedFunctor (TypedExpr T V) WellTypedValue__If2.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [v UP__v] /= => WTV__V.
    econstructor => //; apply IH => //.
  Qed.

  Definition WellTypedValueInversionClear__If2
             (WellTypedValue__V : (TypedExpr T V)-indexedProp)
             (tv : TypedExpr T V)
             (P : (TypedExpr T V)-indexedPropFunctor)
             (IH : forall tau v,
                 {| type := tau; expr := v |} = tv ->
                 WellTypedValue__V {| type := tau; expr := v |} ->
                 P WellTypedValue__V {| type := tau; expr := v |})
             (WT : WellTypedValue__If2 WellTypedValue__V tv)
    : P WellTypedValue__V tv
    :=
      match WT in (WellTypedValue__If2 _ p) return (p = tv -> P WellTypedValue__V tv) with
      | WellTypedValue__if2 _ tau e wtv =>
        fun EQ =>
          eq_ind _ (fun p => P WellTypedValue__V p) (IH _ _ EQ wtv) tv EQ
      end eq_refl.

  (* Definition WellTypedValueInversionStatement__If2 *)
  (*            (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor) *)
  (*            (te : TypedExpr T V) *)
  (*   := proj1_sig (type te) = boolType -> *)
  (*      WellTypedValue__If2 (IndexedFix WellTypedValue__V) te. *)

  (* Variant ForWellTypedValueInversion__If2 := . *)

  (* Global Instance WellTypedValueInversion__If2 *)
  (*        (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor) *)
  (*        `{IndexedFunctor (TypedExpr T V) WellTypedValue__V} *)
  (*        `{S : ! IndexedSubFunctor WellTypedValue__If2 WellTypedValue__V} *)
  (*   : IndexedProofAlgebra ForWellTypedValueInversion__If2 *)
  (*                         WellTypedValue__If2 *)
  (*                         (WellTypedValueInversionStatement__If2 WellTypedValue__V). *)
  (* Proof. *)
  (*   constructor. *)
  (*   move => tv [] t v //. *)
  (* Qed. *)

  (* Definition wellTypedValueInversion__If2 *)
  (*            (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor) *)
  (*            `{IndexedFunctor (TypedExpr T V) WellTypedValue__V} *)
  (*            `{S : ! IndexedSubFunctor WellTypedValue__If2 WellTypedValue__V} *)
  (*            `{A : ! IndexedProofAlgebra ForWellTypedValueInversion__If2 WellTypedValue__V *)
  (*                    (WellTypedValueInversionStatement__If2 WellTypedValue__V)} *)
  (*   :=  ifold (indexedProofAlgebra' A). *)

  Inductive WellTypedExpr__If2
            (WT : (TypedExpr T E)-indexedProp)
    : (TypedExpr T E)-indexedProp
    :=
    | WellTypedExpr__if2 : forall t e condition thenBranch elseBranch,
        proj1_sig e = if2F' condition thenBranch elseBranch ->
        WT {| type := boolType';  expr := condition;  |} ->
        WT {| type := t;          expr := thenBranch |} ->
        WT {| type := t;          expr := elseBranch |} ->
        WellTypedExpr__If2 WT {| type := t; expr := e |}
  .

  Global Instance IndexedFunctor_WellTypedExpr__If2
    : IndexedFunctor (TypedExpr T E) WellTypedExpr__If2.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] /= => cond thenB elseB Eq__e.
    move : Eq__e UP__e => -> => UP__e H__c H__t H__e.
    econstructor => //; apply IH => //.
  Qed.

  Definition WellTypedExprInversionClear__If2
             (WellTypedExpr__E : (TypedExpr T E)-indexedProp)
             (te : TypedExpr T E)
             (P : (TypedExpr T E)-indexedPropFunctor)
             (IH : forall tau e cond thenB elseB,
                 {| type := tau; expr := e |} = te ->
                 proj1_sig e = if2F' cond thenB elseB ->
                 P WellTypedExpr__E {| type := tau; expr := e |})
             (WT : WellTypedExpr__If2 WellTypedExpr__E te)
    : P WellTypedExpr__E te
    :=
      match WT in (WellTypedExpr__If2 _ p) return (p = te -> P WellTypedExpr__E te) with
      | WellTypedExpr__if2 _ tau e cond thenB elseB E WT__c WT__t WT__e =>
        fun EQ =>
          eq_ind _ (fun p => P WellTypedExpr__E p) (IH _ _ _ _ _ EQ E) te EQ
      end eq_refl.

  Definition WellTypedExprInversionStatement__If2
             (WellTypedExpr__E : (TypedExpr T E)-indexedPropFunctor)
             (te : TypedExpr T E)
    := proj1_sig (type te) = boolType ->
       WellTypedExpr__If2 (IndexedFix WellTypedExpr__E) te.

  Variant ForWellTypedExprInversion__If2 := .

  Global Instance WellTypedExprInversion__If2
         (WellTypedExpr__E : (TypedExpr T E)-indexedPropFunctor)
         `{IndexedFunctor (TypedExpr T E) WellTypedExpr__E}
         `{S : ! IndexedSubFunctor WellTypedExpr__If2 WellTypedExpr__E}
    : IndexedProofAlgebra ForWellTypedExprInversion__If2
                          WellTypedExpr__If2
                          (WellTypedExprInversionStatement__If2 WellTypedExpr__E).
  Proof.
    constructor.
    move => te [] t e cond thenB elseB P IH__c IH__t IH__e Q.
    apply : (WellTypedExpr__if2 _ _ _ _ _ _ P).
    apply (iInject (IH__c eq_refl)).
    apply (iInject (IH__t Q)).
    apply (iInject (IH__e Q)).
  Qed.

End If2.
