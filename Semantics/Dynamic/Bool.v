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

Definition eval__Bool
           {V} `{FunctorLaws V}
           `{! V supports Bool}
  : forall {T}, MixinAlgebra Bool T (EvalResult V)
  := fun _ rec '(MkBool b) env => boolean b.

Global Instance Eval__Bool
       {V} `{FunctorLaws V}
       `{! V supports Bool}
  : forall {T}, ProgramAlgebra Eval Bool T (EvalResult V)
  := fun _ => {| programAlgebra := eval__Bool; |}.

Inductive EvalP__Bool {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! E supports Bool}
          `{! V supports Bool}
          (EvalP__E : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | BoolValue : forall b, EvalP__Bool EvalP__E (boolean b, boolean b)
.

Inductive WellTyped__Bool
          {T E}
          `{FunctorLaws T} `{FunctorLaws E}
          `{! T supports BoolType}
          `{! E supports Bool}
          (WT : TypedExpr T E -> Prop) : TypedExpr T E -> Prop :=
| WellTyped__boolean : forall t e b,
    proj1_sig e = boolean__F b ->
    proj1_sig t = boolType ->
    WellTyped__Bool WT {| type := t; expr := e; |}
.

Global Instance IndexedFunctor_WellTyped__Bool
       {T V}
       `{FunctorLaws T} `{FunctorLaws V}
       `{! T supports BoolType}
       `{! V supports Bool}
  : IndexedFunctor (TypedExpr T V) WellTyped__Bool.
Proof.
  constructor.
  move => A B i IH [] [t UP__t] [e UP__e] b /= => Eq__e Eq__t.
  move : Eq__t Eq__e UP__t UP__e => -> -> => UP__t UP__e.
  econstructor => //.
Qed.

Definition SoundnessStatement__Bool
           {T E V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
           `{! E supports Bool}
           (WT : (TypedExpr T V -> Prop) -> TypedExpr T V -> Prop)
           `{Eval__E   : forall {R}, ProgramAlgebra Eval   E R (EvalResult   V)}
           `{TypeOf__E : forall {R}, ProgramAlgebra TypeOf E R (TypeOfResult T)}
           (recEval   : UniversalPropertyF E -> EvalResult   V)
           (recTypeOf : UniversalPropertyF E -> TypeOfResult T)
  :=
    (SoundnessStatement__EvalAlgebra WT
                                   (eval__E   := fun _ => programAlgebra' Eval__E)
                                   (typeOf__F := fun _ => programAlgebra' TypeOf__E)
                                   recEval recTypeOf
    ).

Global Instance EvalSoundness__Bool

       {T}
       `{FunctorLaws T}
       `{! T supports BoolType}

       {E}
       `{FunctorLaws E}
       `{! E supports Bool}
       `{! WellFormedSubFunctor Bool E}

       {V}
       `{FunctorLaws V}
       `{! V supports Bool}

       (WT : (TypedExpr T V -> Prop) -> TypedExpr T V -> Prop)
       `(IndexedFunctor (TypedExpr T V) WT)
       `((WellTyped__Bool <= WT)%IndexedSubFunctor)

       `{Eval__E   : forall {R}, ProgramAlgebra Eval   E R (EvalResult   V)}
       `{! forall {R}, WellFormedProgramAlgebra Eval__Bool Eval__E (T := R)}
       (recEval   : UniversalPropertyF E -> EvalResult   V)

       `{TypeOf__E : forall {R}, ProgramAlgebra TypeOf E R (TypeOfResult T)}
       `{! forall {R}, WellFormedProgramAlgebra TypeOf__Bool TypeOf__E (T := R)}
       (recTypeOf : UniversalPropertyF E -> TypeOfResult T)

  : ProofAlgebra Bool (sig (UniversalPropertyP2 (SoundnessStatement__Bool WT recEval recTypeOf))).
Proof.
  constructor.
  apply Induction2Algebra_Bool => b.
  rewrite / SoundnessStatement__Bool / SoundnessStatement__EvalAlgebra / UniversalPropertyP2 /=.
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
