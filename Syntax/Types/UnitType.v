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

Local Open Scope SubFunctor_scope.
Local Open Scope Sum1_scope.

Inductive UnitType (A : Set) : Set :=
| MkUnitType : UnitType A
.
Arguments MkUnitType {A}.

Global Instance Functor_UnitType
  : Functor UnitType
  :=
    {|
      fmap := fun A B f 'MkUnitType => MkUnitType;
    |}.

Global Instance FunctorLaws_UnitType
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
           {LT} `{FunctorLaws LT} `{LT supports UnitType}
  : TypeFix LT
  := inject MkUnitType.

Definition unitType
           {LT} `{FunctorLaws LT} `{LT supports UnitType}
  : Fix LT
  := proj1_sig unitType'.

Global Instance ReverseFoldUniversalProperty_unitType
           {LT} `{FunctorLaws LT} `{LT supports UnitType}
  : FoldUP' unitType
  := proj2_sig unitType'.

Definition isUnitType
           {LT} `{FunctorLaws LT} `{LT supports UnitType}
  : Fix LT -> bool
  := fun typ =>
       match project typ with
       | Some MkUnitType => true
       | None            => false
       end.

Definition typeEquality_UnitType
           LT `{FunctorLaws LT} `{LT supports UnitType}
           (R : Set) (rec : R -> TypeEqualityResult LT) (e : UnitType R)
  : TypeEqualityResult LT
  :=
    match e with
    | MkUnitType => fun t => isUnitType (proj1_sig t)
    end.

Global Instance TypeEquality_UnitType
       LT `{FunctorLaws LT} `{LT supports UnitType}
       T
  : ProgramAlgebra ForTypeEquality UnitType T (TypeEqualityResult LT)
  := {| programAlgebra := typeEquality_UnitType LT T|}.
