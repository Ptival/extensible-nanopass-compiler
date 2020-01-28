From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Semantics.Static Require Import Unit.

From ExtensibleCompiler.Syntax.Terms Require Import Unit.

From ExtensibleCompiler.Syntax.Types Require Import UnitType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSubFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section AbstractLemma.

  Context
    {T}
    `{FunctorLaws T}
    {C}
    `{FunctorLaws C}
    {E}
    `{FunctorLaws E}
    `{! E supports C}
    `{! WellFormedSubFunctor C E}
    {V}
    `{FunctorLaws V}
  .

  Theorem EvenMoreAbstractSoundness
         (WT__C : (TypedExpr T V)-indexedPropFunctor)
         (WT__E : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WT__C)
         `(IndexedFunctor (TypedExpr T V) WT__E)
         `(! IndexedSubFunctor WT__C WT__E)

         `{Eval__C   : forall {R}, ProgramAlgebra ForEval   C R (EvalResult   V)}
         `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
         `{! forall {R}, WellFormedProgramAlgebra Eval__C Eval__E (T := R)}
         (recEval   : UniversalPropertyF E -> EvalResult   V)

         `{TypeOf__C : forall {R}, ProgramAlgebra ForTypeOf C R (TypeOfResult T)}
         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__C TypeOf__E (T := R)}
         (recTypeOf : UniversalPropertyF E -> TypeOfResult T)

         Gamma (ctor : C (WellFormedValue E))

    :
      (forall
          (Gamma' : Environment.Environment (ValueFix V))
          (a : UniversalPropertyF E * UniversalPropertyF E),
          (forall tau : TypeFix T,
              programAlgebra' TypeOf__E recTypeOf (unwrap__UP' (proj1_sig (snd a))) =
              Some tau ->
              WellTyped WT__E tau
                        (programAlgebra' Eval__E recEval (unwrap__UP' (proj1_sig (fst a)))
                                         Gamma')) ->
          forall tau : TypeFix T,
            recTypeOf (snd a) = Some tau ->
            WellTyped WT__E tau (recEval (wrap__UP' (unwrap__UP' (proj1_sig (fst a)))) Gamma')) ->
      forall tau : TypeFix T,
        programAlgebra' TypeOf__E recTypeOf (unwrap__UP' (proj1_sig (inject ctor))) = Some tau ->

        (WT__C (IndexedFix WT__E) ({|
             type := tau;
             expr := programAlgebra' Eval__E recEval (unwrap__UP' (proj1_sig (inject ctor))) Gamma;
           |})) ->


        WellTyped WT__E tau
                  (programAlgebra' Eval__E recEval (unwrap__UP' (proj1_sig (inject ctor))) Gamma).
  Proof.
    rewrite / inject /=.
    rewrite unwrap__UP'_wrap__F /=.
    rewrite fmapFusion / Extras.compose /=.
    rewrite wellFormedSubFunctor => //=.
    rewrite / programAlgebra'.
    rewrite wellFormedProgramAlgebra.
    rewrite wellFormedProgramAlgebra.
    move => IH tau TY.
    apply (iInject (F := WT__C)) => /=.
  Qed.

End AbstractLemma.

Section Unit.

  Context
    {V}
    `{FunctorLaws V}
    `{! V supports Unit}
    `{! WellFormedSubFunctor Unit V}
  .

  Definition eval__Unit
    : forall {R}, MixinAlgebra Unit R (EvalResult V)
    := fun _ rec '(MkUnit) env => unit.

  Global Instance Eval__Unit
    : forall {R}, ProgramAlgebra ForEval Unit R (EvalResult V)
    := fun _ => {| programAlgebra := eval__Unit; |}.

  Definition Eval__Unit'
    : forall R, ProgramAlgebra ForEval Unit R (EvalResult V)
    := fun _ => Eval__Unit.

  Global Instance WF_Eval__Bool
    : WellFormedMendlerAlgebra Eval__Unit'.
  Proof.
    constructor.
    move => T T' f rec [] //.
  Qed.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports Unit}
    `{!WellFormedSubFunctor Unit E}
  .

  Inductive EvalRelation__Unit
            (EvalRelation__E : (WellFormedValue E * WellFormedValue V) -> Prop)
    : (WellFormedValue E * WellFormedValue V) -> Prop
    :=
    | UnitValue : EvalRelation__Unit EvalRelation__E (unit, unit)
  .

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports UnitType}
    `{! WellFormedSubFunctor UnitType T}
  .

  Inductive WellTyped__Unit
            (WT : (TypedExpr T V)-indexedProp)
    : (TypedExpr T V)-indexedProp
    :=
    | WellTyped__unit : forall t e,
        proj1_sig e = unit__F ->
        proj1_sig t = unitType ->
        WellTyped__Unit WT {| type := t; expr := e; |}
  .

  Global Instance IndexedFunctor_WellTyped__Unit
    : IndexedFunctor (TypedExpr T V) WellTyped__Unit.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] /= => Eq__e Eq__t.
    move : Eq__t Eq__e UP__t UP__e => -> -> => UP__t UP__e.
    econstructor => //.
  Qed.

  Global Instance Soundness__Unit

         (WT : (TypedExpr T V)-indexedPropFunctor)
         `(IndexedFunctor (TypedExpr T V) WT)
         `((WellTyped__Unit <= WT)%IndexedSubFunctor)

         `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
         `{! forall {R}, WellFormedProgramAlgebra Eval__Unit Eval__E (T := R)}
         (recEval   : UniversalPropertyF E -> EvalResult   V)

         `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
         `{! forall {R}, WellFormedProgramAlgebra TypeOf__Unit TypeOf__E (T := R)}
         (recTypeOf : UniversalPropertyF E -> TypeOfResult T)

    : ProofAlgebra
        ForSoundness Unit
        (sig (UniversalPropertyP2
                (AbstractSoundnessStatement' WT recEval recTypeOf))).
  Proof.
    constructor.
    apply Induction2Algebra__Unit.
    rewrite / AbstractSoundnessStatement' / AbstractSoundnessStatement.
    rewrite / UniversalPropertyP2 /=.
    constructor.
    {
      apply conj; apply (proj2_sig unit).
    }
    {
      move => Gamma.
      rewrite / unit__F / unit / inject /=.
      rewrite unwrap__UP'_wrap__F /=.
      rewrite fmapFusion / Extras.compose /=.
      rewrite wellFormedSubFunctor => //=.
      rewrite / programAlgebra'.
      rewrite wellFormedProgramAlgebra.
      rewrite wellFormedProgramAlgebra.
      move => IH tau TY.
      apply (iInject (F := WellTyped__Unit)) => /=.
      econstructor => //.
      move : TY => /=.
      move => [] <- //.
    }
  Qed.

End Unit.
