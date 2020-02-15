From Coq Require Import
     ssreflect
.

From ExtensibleCompiler.Syntax Require Import
     Terms.Unit
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProgramAlgebra
     SubFunctor
     Sum1
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.
Local Open Scope Sum1.

Inductive UnitType (A : Set) : Set :=
| MkUnitType : UnitType A
.
Arguments MkUnitType {A}.

Global Instance Functor__UnitType
  : Functor UnitType
  :=
    {|
      fmap := fun A B f 'MkUnitType => MkUnitType;
    |}.

Global Instance FunctorLaws__UnitType
  : FunctorLaws UnitType.
Proof.
  apply Build_FunctorLaws.
  {
    move => ? [] //.
  }
  {
    move => ????? [] //.
  }
Qed.

Definition unitType'
           {T} `{FunctorLaws T} `{T supports UnitType}
  : TypeFix T
  := inject MkUnitType.

Definition unitType
           {T} `{FunctorLaws T} `{T supports UnitType}
  : Fix T
  := proj1_sig unitType'.

Global Instance FoldUP'__unitType
           {T} `{FunctorLaws T} `{T supports UnitType}
  : FoldUP' unitType
  := proj2_sig unitType'.

Definition isUnitType
           {T} `{FunctorLaws T} `{T supports UnitType}
  : Fix T -> bool
  := fun typ =>
       match project typ with
       | Some MkUnitType => true
       | None            => false
       end.

Definition typeEquality__UnitType
           T `{FunctorLaws T} `{T supports UnitType}
  : forall {R}, MixinAlgebra UnitType R (TypeEqualityResult T)
  := fun _ _ '(MkUnitType) => fun t => isUnitType (proj1_sig t).

Global Instance TypeEquality__UnitType
       T `{FunctorLaws T} `{T supports UnitType}
  : forall {R}, ProgramAlgebra ForTypeEquality UnitType R (TypeEqualityResult T)
  := fun _ => {| programAlgebra := typeEquality__UnitType T |}.
