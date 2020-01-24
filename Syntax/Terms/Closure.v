From Coq Require Import List.
From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Environment.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Inductive Closure
          L
          `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
          E
  : Set :=
| MkClosure (closure : WellFormedValue (L nat)) (environment : Environment E)
.
Arguments MkClosure {L F FL E}.

Global Instance Functor__Closure
       {L} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
  : Functor (Closure L)
  := {| fmap := fun A B f '(MkClosure c e) => MkClosure c (map f e); |}.

Global Instance FunctorLaws__Closure
       {L} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
  : FunctorLaws (Closure L).
Proof.
  constructor.
  - move => ? [] c e.
    rewrite / fmap / Functor__Closure.
    rewrite map_id //.
  - move => ????? [] c e.
    rewrite / fmap / Functor__Closure.
    rewrite map_map //.
Qed.

Definition closure
           {L V} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
           `{(L V) supports (Closure L)}
           c e
  : UniversalPropertyF (L V)
  := inject (MkClosure c e).

Definition closure__F
           {L V} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
           `{(L V) supports (Closure L)}
           c e
  : Fix (L V)
  := proj1_sig (closure c e).

Global Instance Fold__UP'__closure
       {L V} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
       `{(L V) supports (Closure L)}
       c e
  : Fold__UP' (closure__F c e)
  := proj2_sig (closure c e).

Definition isClosure
           {L V} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
           `{(L V) supports (Closure L)}
  : Fix (L V) -> option _
  := fun v =>
       match project (F := Closure L) v with
       | Some (MkClosure f e) => Some (f, e)
       | None                 => None
       end.