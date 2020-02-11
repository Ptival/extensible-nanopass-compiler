From Coq Require Import
     List
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Environment
     Eval
     Functor
     ProgramAlgebra
     SubFunctor
     Sum1
     Types
     UniversalProperty
.

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
  : WellFormedValue (L V)
  := inject (MkClosure c e).

Definition closureF
           {L V} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
           `{(L V) supports (Closure L)}
           c e
  : Fix (L V)
  := proj1_sig (closure c e).

Global Instance FoldUP'__closure
       {L V} `{F : forall V, Functor (L V)} `{FL : forall V, FunctorLaws (L V)}
       `{(L V) supports (Closure L)}
       c e
  : FoldUP' (closureF c e)
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
