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

Inductive Bool (A: Set) : Set :=
| MkBool (boolean : bool)
.
Arguments MkBool {A}.

Global Instance Functor_Bool : Functor Bool :=
  {|
    fmap := fun A B f '(MkBool b) => MkBool b;
  |}.

Global Instance FunctorLaws_Bool : FunctorLaws Bool.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Section Bool.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports Bool}
  .

  Definition boolean
             (b : bool)
    : WellFormedValue E
    := inject (MkBool b).

  Definition booleanF
             (b : bool)
    : Fix E
    := proj1_sig (boolean b).

  Definition isBoolean
    : Fix E -> option bool
    := fun typ =>
         match project typ with
         | Some (MkBool b) => Some b
         | None            => None
         end.

  Definition InductionAlgebra_Bool
             (P : forall (e : Fix E), FoldUP' e -> Prop)
             (H_boolean : forall b, UniversalPropertyP P (booleanF b))
    : Algebra Bool (sig (UniversalPropertyP P))
    := fun '(MkBool b) => exist _ _ (H_boolean b).

End Bool.

Section Bool.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports Bool}

    {F}
    `{FunctorLaws F}
    `{! F supports Bool}
  .

  Definition Induction2Algebra_Bool
             (P : forall (e : Fix E * Fix F), FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
             (H_boolean : forall b, UniversalPropertyP2 P (booleanF b, booleanF b))
    : Algebra Bool (sig (UniversalPropertyP2 P))
    := fun '(MkBool b) => exist _ _ (H_boolean b).

End Bool.
