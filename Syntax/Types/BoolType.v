From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProofAlgebra
     ProgramAlgebra
     SubFunctor
     Sum1
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.

Inductive BoolType (A : Set) : Set :=
| MkBoolType : BoolType A
.
Arguments MkBoolType {A}.

Global Instance Functor_BoolType
  : Functor BoolType
  := {| fmap := fun A B f 'MkBoolType => MkBoolType |}.

Global Instance FunctorLaws_BoolType
  : FunctorLaws BoolType.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Section BoolType.

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
    `{! WellFormedSubFunctor BoolType T}
  .

  Definition boolType'
    : TypeFix T
    := inject MkBoolType.

  Definition boolType
    : Fix T
    := proj1_sig boolType'.

  Global Instance FoldUP'__boolType
    : FoldUP' boolType
    := proj2_sig boolType'.

  Definition isBoolType
    : Fix T -> bool
    := fun typ =>
         match project typ with
         | Some MkBoolType => true
         | None            => false
         end.

  Definition typeEquality__BoolType
    : forall R, MixinAlgebra BoolType R (TypeEqualityResult T)
    := fun _ rec '(MkBoolType) => fun t => isBoolType (proj1_sig t).

  Global Instance TypeEquality__BoolType
    : forall {R}, ProgramAlgebra ForTypeEquality BoolType R (TypeEqualityResult T)
    := fun _ => {| programAlgebra := typeEquality__BoolType _ |}.

  Global Instance TypeEqualityCorrectness__BoolType
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
    rewrite {1} / wrapF.
    rewrite wellFormedProgramAlgebra /=.
    rewrite / isBoolType.
    case P : (project (proj1_sig tau')) => [ [] | ] // => _.
    move : P.
    rewrite / project.
    move => P.
    move : P (inj_prj P) => _.
    rewrite / boolType / boolType' /=.
    rewrite wellFormedSubFunctor /=.
    move => P.
    move : P (f_equal wrapUP' P) => _.
    move => P.
    move : P (f_equal (@proj1_sig _ _) P) => _.
    setoid_rewrite wrapUP'_unwrapUP'.
    {
      move => -> /=.
      rewrite wellFormedSubFunctor //.
    }
    {
      apply proj2_sig.
    }
  Qed.

End BoolType.
