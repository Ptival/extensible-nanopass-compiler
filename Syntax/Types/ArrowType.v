From Coq Require Import
     ssreflect
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

Inductive ArrowType (A : Set) : Set :=
| MkArrowType (domain : A) (codomain : A)
.
Arguments MkArrowType {A}.

Global Instance Functor__ArrowType
  : Functor ArrowType.
Proof.
  refine {| fmap := fun A B f '(MkArrowType d c) => MkArrowType (f d) (f c) |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Definition arrowType'
           {T} `{Functor T} `{T supports ArrowType}
           d c
  : TypeFix T
  := injectUP' (MkArrowType d c).

Definition arrowType
           {T} `{Functor T} `{T supports ArrowType}
           d c
  : Fix T
  := proj1_sig (arrowType' d c).

Global Instance FoldUP'__arrowType
       T `{Functor T} `{T supports ArrowType}
       d c
  : FoldUP' (arrowType d c)
  := proj2_sig (arrowType' d c).

Definition isArrowType
           {T} `{Functor T} `{T supports ArrowType}
  : Fix T -> option (TypeFix T * TypeFix T)%type
  := fun typ =>
       match projectUP' typ with
       | Some (MkArrowType d c) => Some (d, c)
       | None                   => None
       end.

(* FIXME *)

(* Definition typeEquality_ArrowType *)
(*            T `{Functor T} `{T supports ArrowType} *)
(*            (R : Set) (rec : R -> TypeEqualityResult T) (e : ArrowType R) *)
(*   : TypeEqualityResult T *)
(*   := *)
(*     match e with *)
(*     | MkArrowType _ _ => fun t => isArrowType (proj1_sig t) *)
(*     end. *)

(* Global Instance TypeEquality_ArrowType *)
(*        T `{Functor T} `{T supports ArrowType} *)
(*        T *)
(*   : ProgramAlgebra TypeEquality ArrowType T (TypeEqualityResult T) *)
(*   := {| programAlgebra := typeEquality_ArrowType T T|}. *)
