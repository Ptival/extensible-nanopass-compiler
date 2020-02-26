From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax Require Import
     Terms.Bool
     Terms.Stuck
     Terms.Unit
     Types.BoolType
     Types.UnitType
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProgramAlgebra
     ProofAlgebra
     SubFunctor
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.

Inductive If1 (A : Set) : Set :=
| MkIf1 (condition : A) (thenBranch : A)
.
Arguments MkIf1 {A}.

Global Instance Functor__If1
  : Functor If1.
Proof.
  refine {| fmap := fun A B f '(MkIf1 c t) => MkIf1 (f c) (f t) |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section If1.

  Context
    {E}
    `{Functor E}
    `{E supports If1}
  .

  Definition if1 c t
    : WellFormedValue E
    := injectUP' (MkIf1 c t).

  Definition if1F c t
    : Fix E
    := wrapF (inject (MkIf1 c t)).

  Definition if1F' c t
    : Fix E
    := proj1_sig (if1 c t).

  (* Definition If1Induction *)
  (*            (P : forall e, Fix If1 -> Prop) *)
  (*            (H : forall c t, P (if1 c t)) *)
  (*   : Algebra If1 { e | P e } *)
  (*   := fun '(If1 (exist _ c _) (exist _ t _)) => *)
  (*        exist _ (if1 c t) (H c t). *)

End If1.
