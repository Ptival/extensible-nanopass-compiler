From Coq Require Import ssreflect.

From ExtensibleCompiler.Semantics.Static Require Import Bool.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSubFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section Bool.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Bool}
  .

  Definition eval__Bool
    : forall {T}, MixinAlgebra Bool T (EvalResult V)
    := fun _ rec '(MkBool b) env => boolean b.

  Global Instance Eval__Bool
    : forall {T}, ProgramAlgebra ForEval Bool T (EvalResult V)
    := fun _ => {| programAlgebra := eval__Bool; |}.

  Global Instance WF_Eval__Bool
    : WellFormedMendlerAlgebra (fun _ => Eval__Bool).
  Proof.
    constructor.
    move => T T' f rec [] b //.
  Qed.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports Bool}
    `{! WellFormedSubFunctor Bool E}
  .

  Inductive EvalRelation__Bool
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | BoolValue : forall b, EvalRelation__Bool EvalRelation__E (boolean b, boolean b)
  .

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
  .

  (* TODO: move this elsewhere *)
  Inductive WellTyped__Bool
            (WT : (TypedExpr T V)-indexedProp)
    : (TypedExpr T V)-indexedProp
    :=
    | WellTyped__boolean : forall t e b,
        proj1_sig e = boolean__F b ->
        proj1_sig t = boolType ->
        WellTyped__Bool WT {| type := t; expr := e; |}
  .

  Global Instance IndexedFunctor_WellTyped__Bool
    : IndexedFunctor (TypedExpr T V) WellTyped__Bool.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] b /= => Eq__e Eq__t.
    move : Eq__t Eq__e UP__t UP__e => -> -> => UP__t UP__e.
    econstructor => //.
  Qed.

  Global Instance Soundness__Bool

         (WT : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WT)
         `((WellTyped__Bool <= WT)%IndexedSubFunctor)

         `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
         `{! forall {R}, WellFormedProgramAlgebra Eval__Bool Eval__E (T := R)}
         (recEval   : UniversalPropertyF E -> EvalResult   V)

         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__Bool TypeOf__E (T := R)}
         (recTypeOf : UniversalPropertyF E -> TypeOfResult T)

    : ProofAlgebra
        ForSoundness Bool
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WT recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2Algebra_Bool => b.
    rewrite / AbstractSoundnessStatement' / AbstractSoundnessStatement.
    rewrite / UniversalPropertyP2 /=.
    constructor.
    {
      apply conj; apply (proj2_sig (boolean b)).
    }
    {
      move => Gamma.
      rewrite / boolean__F / boolean / inject /=.
      rewrite unwrap__UP'_wrap__F /=.
      rewrite fmapFusion / Extras.compose /=.
      rewrite wellFormedSubFunctor => //=.
      rewrite / programAlgebra'.
      rewrite wellFormedProgramAlgebra.
      rewrite wellFormedProgramAlgebra.
      move => IH tau TY.
      apply (iInject (F := WellTyped__Bool)) => /=.
      econstructor => //.
      move : TY => /=.
      move => [] <- //.
    }
  Qed.

End Bool.

(* small sanity check *)
Definition Soundness__Bool'
           {V}
           `{FunctorLaws V}
           `{! V supports Bool}
           {T}
           `{FunctorLaws T}
           `{! T supports BoolType}
  : Soundness__ProofAlgebra (T := T) (E := Bool) (V := V) WellTyped__Bool.
Proof.
  move => recEval recTypeOf.
  apply : Soundness__Bool.
Qed.
