From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax.Terms Require Import
     Bool
.

From ExtensibleCompiler.Syntax.Types Require Import
     BoolType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
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

Section Bool.

  Context

    {T}
    `{Functor T}
    `{! T supports BoolType}

    {E}
    `{Functor E}
    `{! E supports Bool}

    {V}
    `{Functor V}
    `{! V supports Bool}

  .

  Inductive WellTypedValue__Bool
            (WT : (TypedExpr T V)-indexedProp)
    : (TypedExpr T V)-indexedProp
    :=
    | WellTypedValue__boolean : forall t e b,
        proj1_sig e = booleanF b ->
        proj1_sig t = boolType ->
        WellTypedValue__Bool WT {| type := t; expr := e |}
  .

  Global Instance IndexedFunctor_WellTypedValue__Bool
    : IndexedFunctor (TypedExpr T V) WellTypedValue__Bool.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] b /= => Eq__e Eq__t.
    move : Eq__t Eq__e UP__t UP__e => -> -> => UP__t UP__e.
    econstructor => //.
  Qed.

  Definition WellTypedValueInversionClear__Bool
             (WellTypedValue__V : (TypedExpr T V)-indexedProp)
             (tv : TypedExpr T V)
             (P : (TypedExpr T V)-indexedPropFunctor)
             (IH : forall tau v b,
                 {| type := tau; expr := v |} = tv ->
                 proj1_sig v = booleanF b ->
                 proj1_sig tau = boolType ->
                 P WellTypedValue__V {| type := tau; expr := v |})
             (WT : WellTypedValue__Bool WellTypedValue__V tv)
    : P WellTypedValue__V tv
    :=
      match WT in (WellTypedValue__Bool _ p) return (p = tv -> P WellTypedValue__V tv) with
      | WellTypedValue__boolean _ tau e b P__e P__tau =>
        fun EQ =>
          eq_ind _ (fun p => P WellTypedValue__V p) (IH _ _ _ EQ P__e P__tau) tv EQ
      end eq_refl.

  Definition WellTypedValueProjectionStatement__Bool
             (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
             (tv : TypedExpr T V)
    := proj1_sig (type tv) = boolType ->
       WellTypedValue__Bool (IndexedFix WellTypedValue__V) tv.

  Variant ForWellTypedValueProjection__Bool := .

  Global Instance WellTypedValueProjection__Bool
         (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
         `{IndexedFunctor (TypedExpr T V) WellTypedValue__V}
         `{S : ! IndexedSubFunctor WellTypedValue__Bool WellTypedValue__V}
    : IndexedProofAlgebra
        ForWellTypedValueProjection__Bool
        WellTypedValue__Bool
        (WellTypedValueProjectionStatement__Bool WellTypedValue__V).
  Proof.
    constructor.
    move => tv [] t v b ? ? ?.
    apply : (WellTypedValue__boolean _ _ _ b) => //.
  Qed.

  Global Instance WellTypedValueProj1Type__Bool
         (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
         `{IndexedFunctor (TypedExpr T V) WellTypedValue__V}
         `{S : ! IndexedSubFunctor WellTypedValue__Bool WellTypedValue__V}
    : IndexedProofAlgebra
        ForWellTypedProj1Type
        WellTypedValue__Bool
        (PropertyStatement__WellTypedProj1Type WellTypedValue__V).
  Proof.
    constructor.
    move => tv [] [] /= ? + ? b P__e X.
    move : X => -> ??? /= ?.
    apply (iInject (F := WellTypedValue__Bool)).
    eapply WellTypedValue__boolean => //=.
    apply P__e.
  Qed.

  (* Ltac wellTypedValueProject__Other := *)
  (*   constructor; rewrite / IndexedAlgebra. *)
  (*   unfold iAlgebra; intros i H; unfold WF_invertVB_P; *)
  (*   inversion H; simpl; *)
  (*   match goal with *)
  (*   | eq_H0 : proj1_sig ?T = _ |- proj1_sig ?T = _ -> _ => *)
  (*     intro eq_H; rewrite eq_H in eq_H0; *)
  (*     discriminate_inject eq_H0 *)
  (*   end. *)

  (* Hint Extern 5 ( *)
  (*        IndexedProofAlgebra *)
  (*          ForWellTypedValueProjection__Bool *)
  (*          _ *)
  (*          (WellTypedValueProjectionStatement__Bool _) *)
  (*      ) => wellTypedValueProjection__Other *)
  (* : typeclass_instances. *)

  Definition wellTypedValueProjection__Bool
             (WellTypedValue__V : (TypedExpr T V)-indexedPropFunctor)
             `{IndexedFunctor (TypedExpr T V) WellTypedValue__V}
             `{S : ! IndexedSubFunctor WellTypedValue__Bool WellTypedValue__V}
             `{A : ! IndexedProofAlgebra
                     ForWellTypedValueProjection__Bool
                     WellTypedValue__V
                     (WellTypedValueProjectionStatement__Bool WellTypedValue__V)}
    :=  ifold (indexedProofAlgebra' A).

End Bool.

(**
The default behavior of [apply] in typeclass resolution is too dumb.  Using
ssreflect's [apply :] helps.
 *)
Hint Extern 5
     (IndexedProofAlgebra ForWellTypedProj1Type _ _)
=> apply : WellTypedValueProj1Type__Bool
  : typeclass_instances.
