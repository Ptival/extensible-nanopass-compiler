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

Local Open Scope SubFunctor.

Inductive Closure
          L
          `{F : forall V, Functor (L V)} `{FL : forall V, Functor (L V)}
          E
  : Set :=
| MkClosure (closure : WellFormedValue (L nat)) (environment : Environment E)
.
Arguments MkClosure {L F FL E}.

Global Instance Functor__Closure
       {L} `{F : forall V, Functor (L V)} `{FL : forall V, Functor (L V)}
  : Functor (Closure L).
Proof.
  refine {| fmap := fun A B f '(MkClosure c e) => MkClosure c (map f e) |}.
  - move => ? [] c e.
    rewrite map_id //.
  - move => ????? [] c e.
    rewrite map_map //.
Defined.

Definition closure
           {L V} `{F : forall V, Functor (L V)} `{FL : forall V, Functor (L V)}
           `{(L V) supports (Closure L)}
           c e
  : WellFormedValue (L V)
  := injectUP' (MkClosure c e).

Definition closureF
           {L V} `{F : forall V, Functor (L V)} `{FL : forall V, Functor (L V)}
           `{(L V) supports (Closure L)}
           c e
  : Fix (L V)
  := proj1_sig (closure c e).

Global Instance FoldUP'__closure
       {L V} `{F : forall V, Functor (L V)} `{FL : forall V, Functor (L V)}
       `{(L V) supports (Closure L)}
       c e
  : FoldUP' (closureF c e)
  := proj2_sig (closure c e).

Definition isClosure
           {L V} `{F : forall V, Functor (L V)} `{FL : forall V, Functor (L V)}
           `{(L V) supports (Closure L)}
  : Fix (L V) -> option _
  := fun v =>
       match projectUP' (F := Closure L) v with
       | Some (MkClosure f e) => Some (f, e)
       | None                 => None
       end.
