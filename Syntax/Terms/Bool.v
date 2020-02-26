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

Global Instance Functor__Bool
  : Functor Bool.
Proof.
  refine
    {|
      fmap := fun A B f '(MkBool b) => MkBool b;
    |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section Bool.

  Context
    {E}
    `{Functor E}
    `{E supports Bool}
  .

  Definition boolean
             (b : bool)
    : WellFormedValue E
    := injectUP' (MkBool b).

  Definition booleanF
             (b : bool)
    : Fix E
    := proj1_sig (boolean b).

  Definition isBoolean
    : Fix E -> option bool
    := fun typ =>
         match projectUP' typ with
         | Some (MkBool b) => Some b
         | None            => None
         end.

  Definition InductionAlgebra__Bool
             (P : forall (e : Fix E), FoldUP' e -> Prop)
             (IH__boolean :
                forall b,
                  UniversalPropertyP P (booleanF b))
    : Algebra Bool (sig (UniversalPropertyP P))
    := fun '(MkBool b) => exist _ _ (IH__boolean b).

End Bool.

Section Bool.

  Context
    {E}
    `{Functor E}
    `{E supports Bool}

    {F}
    `{Functor F}
    `{F supports Bool}
  .

  Definition Induction2Algebra__Bool
             (P :
                forall (e : Fix E * Fix F),
                  FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
             (IH__boolean :
                forall b,
                  UniversalPropertyP2 P (booleanF b, booleanF b))
    : Algebra Bool (sig (UniversalPropertyP2 P))
    := fun '(MkBool b) => exist _ _ (IH__boolean b).

End Bool.
