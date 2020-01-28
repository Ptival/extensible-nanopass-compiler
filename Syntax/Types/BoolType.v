From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Inductive BoolType (A : Set) : Set :=
| MkBoolType : BoolType A
.
Arguments MkBoolType {A}.

Global Instance Functor_BoolType
  : Functor BoolType
  := {| fmap := fun A B f 'MkBoolType => MkBoolType; |}.

Global Instance FunctorLaws_BoolType
  : FunctorLaws BoolType.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition boolType'
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : TypeFix LT
  := inject MkBoolType.

Definition boolType
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : Fix LT
  := proj1_sig boolType'.

Global Instance ReverseFoldUniversalProperty_boolType
           LT `{FunctorLaws LT} `{LT supports BoolType}
  : Fold__UP' boolType
  := proj2_sig boolType'.

Definition isBoolType
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : Fix LT -> bool
  := fun typ =>
       match project typ with
       | Some MkBoolType => true
       | None            => false
       end.

Definition typeEquality__BoolType
           {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : forall {T}, MixinAlgebra BoolType T (TypeEqualityResult LT)
  := fun _ rec '(MkBoolType) => fun t => isBoolType (proj1_sig t).

Global Instance TypeEquality__BoolType
       {LT} `{FunctorLaws LT} `{LT supports BoolType}
  : forall {T}, ProgramAlgebra ForTypeEquality BoolType T (TypeEqualityResult LT)
  := fun _ => {| programAlgebra := typeEquality__BoolType |}.

Global Instance TypeEqualityCorrectness__BoolType
       T `{FunctorLaws T} `{! T supports BoolType}
       `{! WellFormedSubFunctor BoolType T}
       `{PA : forall {R}, ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
       `{! forall {R}, WellFormedProgramAlgebra (T := R) TypeEquality__BoolType PA}
  : ProofAlgebra
      ForTypeEqualityCorrectness
      BoolType
      (sig (UniversalPropertyP (typeEqualityCorrectnessStatement (T := T)))).
Proof.
  constructor => [] [].
  exists boolType.
  rewrite / UniversalPropertyP.
  econstructor.
  rewrite / typeEqualityCorrectnessStatement.
  move => tau'.
  rewrite / typeEquality / mendlerFold {1} / boolType / boolType'.
  rewrite {1} / inject /=.
  rewrite {1} wellFormedSubFunctor /=.
  rewrite {1} / wrap__F.
  rewrite wellFormedProgramAlgebra /=.
  rewrite / isBoolType.
  case P : (project (proj1_sig tau')) => [ [] | ] // => _.
  move : P.
  rewrite / project.
  move => P.
  move : P (inj_prj _ _ P) => _.
  rewrite / boolType / boolType' /=.
  rewrite wellFormedSubFunctor /=.
  move => P.
  move : P (f_equal wrap__UP' P) => _.
  move => P.
  move : P (f_equal (@proj1_sig _ _) P) => _.
  setoid_rewrite wrap__UP'_unwrap__UP'.
  {
    move => -> /=.
    rewrite wellFormedSubFunctor //.
  }
  {
    apply proj2_sig.
  }
Qed.
