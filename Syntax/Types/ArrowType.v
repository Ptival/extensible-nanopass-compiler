From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Inductive ArrowType (A : Set) : Set :=
| MkArrowType (domain : A) (codomain : A)
.
Arguments MkArrowType {A}.

Global Instance Functor_ArrowType
  : Functor ArrowType
  := {| fmap := fun A B f '(MkArrowType d c) => MkArrowType (f d) (f c); |}.

Global Instance FunctorLaws_ArrowType
  : FunctorLaws ArrowType.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition arrowType'
           {LT} `{FunctorLaws LT} `{LT supports ArrowType}
           d c
  : TypeFix LT
  := injectUniversalProperty (MkArrowType d c).

Definition arrowType
           {LT} `{FunctorLaws LT} `{LT supports ArrowType}
           d c
  : Fix LT
  := proj1_sig (arrowType' d c).

Global Instance ReverseFoldUniversalProperty_arrowType
       LT `{FunctorLaws LT} `{LT supports ArrowType}
       d c
  : ReverseFoldUniversalProperty (arrowType d c)
  := proj2_sig (arrowType' d c).

Definition isArrowType
           {LT} `{FunctorLaws LT} `{LT supports ArrowType}
  : Fix LT -> option (TypeFix LT * TypeFix LT)%type
  := fun typ =>
       match project typ with
       | Some (MkArrowType d c) => Some (d, c)
       | None                   => None
       end.

(* FIXME *)

(* Definition typeEquality_ArrowType *)
(*            LT `{FunctorLaws LT} `{LT supports ArrowType} *)
(*            (R : Set) (rec : R -> TypeEqualityResult LT) (e : ArrowType R) *)
(*   : TypeEqualityResult LT *)
(*   := *)
(*     match e with *)
(*     | MkArrowType _ _ => fun t => isArrowType (proj1_sig t) *)
(*     end. *)

(* Global Instance TypeEquality_ArrowType *)
(*        LT `{FunctorLaws LT} `{LT supports ArrowType} *)
(*        T *)
(*   : ProgramAlgebra TypeEquality ArrowType T (TypeEqualityResult LT) *)
(*   := {| programAlgebra := typeEquality_ArrowType LT T|}. *)
