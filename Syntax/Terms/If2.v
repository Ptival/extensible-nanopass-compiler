From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.
From ExtensibleCompiler.Syntax.Terms Require Import Unit.
From ExtensibleCompiler.Syntax.Terms Require Import Stuck.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Inductive If2 (A : Set) : Set :=
| MkIf2 (condition : A) (thenBranch : A) (elseBranch : A)
.
Arguments MkIf2 {A}.

Global Instance Functor_If2 : Functor If2 :=
  {| fmap := fun A B f '(MkIf2 c t e) => MkIf2 (f c) (f t) (f e); |}.

Global Instance FunctorLaws_If2 : FunctorLaws If2.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition if2
           {L} `{FunctorLaws L} `{L supports If2}
           (condition thenBranch elseBranch : UniversalPropertyF L)
  : UniversalPropertyF L
  := inject (MkIf2 condition thenBranch elseBranch).

Definition if2_Fix_UPF
           {L} `{FunctorLaws L} `{L supports If2}
           (condition thenBranch elseBranch : Fix L)
           {H_condition  : Fold__UP' condition}
           {H_thenBranch : Fold__UP' thenBranch}
           {H_elseBranch : Fold__UP' elseBranch}
  : UniversalPropertyF L
  := if2
       (exist _ _ H_condition)
       (exist _ _ H_thenBranch)
       (exist _ _ H_elseBranch).

Definition if2_Fix_Fix
           {L} `{FunctorLaws L} `{L supports If2}
           (condition thenBranch elseBranch : Fix L)
           {H_condition  : Fold__UP' condition}
           {H_thenBranch : Fold__UP' thenBranch}
           {H_elseBranch : Fold__UP' elseBranch}
  : Fix L
  := proj1_sig (if2_Fix_UPF condition thenBranch elseBranch).

Definition if2_UPP_UPF
           {L} `{FunctorLaws L} `{L supports If2}
           {condition thenBranch elseBranch : Fix L}
           {P}
           (H_condition  : UniversalPropertyP P condition)
           (H_thenBranch : UniversalPropertyP P thenBranch)
           (H_elseBranch : UniversalPropertyP P elseBranch)
  : UniversalPropertyF L
  := if2_Fix_UPF condition thenBranch elseBranch
       (H_condition  := proj1_sig H_condition)
       (H_thenBranch := proj1_sig H_thenBranch)
       (H_elseBranch := proj1_sig H_elseBranch).

Definition if2_UPP_Fix
           {L} `{FunctorLaws L} `{L supports If2}
           {condition thenBranch elseBranch : Fix L}
           {P}
           (H_condition  : UniversalPropertyP P condition)
           (H_thenBranch : UniversalPropertyP P thenBranch)
           (H_elseBranch : UniversalPropertyP P elseBranch)
  : Fix L
  := proj1_sig (if2_UPP_UPF H_condition H_thenBranch H_elseBranch).

(* Definition if2_UP_Fix *)
(*            {L} `{FunctorLaws L} `{L supports If2} *)
(*            {condition thenBranch elseBranch : Fix L} *)
(*            (H_condition  : Fold__UP' condition) *)
(*            (H_thenBranch : Fold__UP' thenBranch) *)
(*            (H_elseBranch : Fold__UP' elseBranch) *)
(*   : Fix L *)
(*   := proj1_sig (if2 *)
(*                   (exist _ _ H_condition) *)
(*                   (exist _ _ H_thenBranch) *)
(*                   (exist _ _ H_elseBranch) *)
(*                ). *)

Definition If2Induction
           {F} `{FunctorLaws F} `{S : F supports If2}
           (P : forall (e : Fix F), Fold__UP' e -> Prop)
           (Hif2 : forall (c t e : Fix F)
                     (H_c : UniversalPropertyP P c)
                     (H_t : UniversalPropertyP P t)
                     (H_e : UniversalPropertyP P e),
               UniversalPropertyP P (if2_UPP_Fix H_c H_t H_e))
  : Algebra If2 (sig (UniversalPropertyP P))
  := fun e =>
       match e with
       | MkIf2 c t e =>
         exist _ _ (Hif2 _ _ _ (proj2_sig c) (proj2_sig t) (proj2_sig e))
       end.

(** NOTE: we don't let [SubFunctor] introduce implicitly because it would
introduce a copy of [Functor If2] and make a mess... *)

Global Instance If2ProofAlgebra
       {F} `{FunctorLaws F} `{S : ! F supports If2}
       `(P : forall (e : Fix F), Fold__UP' e -> Prop)
       `(H_if2 : forall c t e
                   (H_c : UniversalPropertyP P c)
                   (H_t : UniversalPropertyP P t)
                   (H_e : UniversalPropertyP P e),
            UniversalPropertyP P (if2_UPP_Fix H_c H_t H_e))
  : ProofAlgebra If2 (sig (UniversalPropertyP P))
  := {| proofAlgebra := If2Induction P H_if2; |}.

Global Instance If2ProofAlgebraWellFormed
       F `{FunctorLaws F} `{! F supports If2} `{! WellFormedSubFunctor If2 F}
       `(P : forall (e : Fix F), Fold__UP' e -> Prop)
       `(H_if2 : forall c t e
                   (IH_c : UniversalPropertyP P c)
                   (IH_t : UniversalPropertyP P t)
                   (IH_e : UniversalPropertyP P e),
            UniversalPropertyP P (if2_Fix_Fix c t e)
        )
  : WellFormedProofAlgebra (If2ProofAlgebra P H_if2).
Proof.
  constructor.
  rewrite /= / If2Induction.
  move => [] c t e /=.
  rewrite / if2_UPP_Fix / if2 / if2 / inject /=.
  erewrite wellFormedSubFunctor => /=.
  reflexivity.
Qed.
