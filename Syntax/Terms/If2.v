From Coq Require Import
     ssreflect
     String
.

From ExtensibleCompiler.Syntax Require Import
     Terms.Bool
     Terms.Unit
     Terms.Stuck
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Eval
     Functor
     ProgramAlgebra
     ProofAlgebra
     SubFunctor
     Sum1
     Types
     UniversalProperty
.

Local Open Scope SubFunctor.

Inductive If2 (A : Set) : Set :=
| MkIf2 (condition : A) (thenBranch : A) (elseBranch : A)
.
Arguments MkIf2 {A}.

Global Instance Functor_If2 : Functor If2 :=
  {| fmap := fun A B f '(MkIf2 c t e) => MkIf2 (f c) (f t) (f e) |}.

Global Instance FunctorLaws_If2 : FunctorLaws If2.
Proof.
  constructor.
  - move => ? [] //.
  - move => ????? [] //.
Qed.

Definition if2
           {E} `{FunctorLaws E} `{E supports If2}
           (condition thenBranch elseBranch : WellFormedValue E)
  : WellFormedValue E
  := inject (MkIf2 condition thenBranch elseBranch).

Definition if2F'
           {E} `{FunctorLaws E} `{E supports If2}
           (condition thenBranch elseBranch : WellFormedValue E)
  : Fix E
  := proj1_sig (if2 condition thenBranch elseBranch).

Definition if2F
           {E} `{FunctorLaws E} `{E supports If2}
           (condition thenBranch elseBranch : Fix E)
  : Fix E
  := wrapF (inj (MkIf2 condition thenBranch elseBranch)).

Definition if2_Fix_UPF
           {E} `{FunctorLaws E} `{E supports If2}
           (condition thenBranch elseBranch : Fix E)
           {H_condition  : FoldUP' condition}
           {H_thenBranch : FoldUP' thenBranch}
           {H_elseBranch : FoldUP' elseBranch}
  : WellFormedValue E
  := if2
       (exist _ _ H_condition)
       (exist _ _ H_thenBranch)
       (exist _ _ H_elseBranch).

(* Definition if2_Fix_Fix *)
(*            {E} `{FunctorLaws E} `{E supports If2} *)
(*            (condition thenBranch elseBranch : Fix E) *)
(*            {H_condition  : FoldUP' condition} *)
(*            {H_thenBranch : FoldUP' thenBranch} *)
(*            {H_elseBranch : FoldUP' elseBranch} *)
(*   : Fix E *)
(*   := proj1_sig (if2_Fix_UPF condition thenBranch elseBranch). *)

Definition if2_UPP_WF
           {E} `{FunctorLaws E} `{E supports If2}
           {condition thenBranch elseBranch : Fix E}
           {P}
           (H_condition  : UniversalPropertyP P condition)
           (H_thenBranch : UniversalPropertyP P thenBranch)
           (H_elseBranch : UniversalPropertyP P elseBranch)
  : WellFormedValue E
  := if2_Fix_UPF condition thenBranch elseBranch
       (H_condition  := proj1_sig H_condition)
       (H_thenBranch := proj1_sig H_thenBranch)
       (H_elseBranch := proj1_sig H_elseBranch).

Definition if2_UPP_Fix
           {E} `{FunctorLaws E} `{E supports If2}
           {condition thenBranch elseBranch : Fix E}
           {P}
           (H_condition  : UniversalPropertyP P condition)
           (H_thenBranch : UniversalPropertyP P thenBranch)
           (H_elseBranch : UniversalPropertyP P elseBranch)
  : Fix E
  := proj1_sig (if2_UPP_WF H_condition H_thenBranch H_elseBranch).

(* Definition if2_UP_Fix *)
(*            {E} `{FunctorLaws E} `{E supports If2} *)
(*            {condition thenBranch elseBranch : Fix E} *)
(*            (H_condition  : FoldUP' condition) *)
(*            (H_thenBranch : FoldUP' thenBranch) *)
(*            (H_elseBranch : FoldUP' elseBranch) *)
(*   : Fix E *)
(*   := proj1_sig (if2 *)
(*                   (exist _ _ H_condition) *)
(*                   (exist _ _ H_thenBranch) *)
(*                   (exist _ _ H_elseBranch) *)
(*                ). *)

(**
The definition of [Induction__If2] uses a very verbose induction hypothesis, whose
conclusion is about [if2_UPP_Fix], because it proves useful in practice.

We could replace the conclusion with:
[UniversalPropertyP P (if2F c t e)]

but then, we need to show that:
[FoldUP' c -> FoldUP' t -> FoldUP' e -> FoldUP' (if2F c t e)]

whereas with the current presentation, this immediately follows as [proj2_sig
(if2 c t e)], since [if2_UPP_Fix] is equal to [proj1_sig (if2 c t e)].
 *)
Definition Induction__If2
           {F} `{FunctorLaws F} `{S : F supports If2}
           (P : forall (e : Fix F), FoldUP' e -> Prop)
           (Hif2 : forall (c t e : Fix F)
                     (IH__c : UniversalPropertyP P c)
                     (IH__t : UniversalPropertyP P t)
                     (IH__e : UniversalPropertyP P e),
               UniversalPropertyP P (if2_UPP_Fix IH__c IH__t IH__e))
  : Algebra If2 (sig (UniversalPropertyP P))
  := fun e =>
       match e with
       | MkIf2 c t e =>
         exist _ _ (Hif2 _ _ _ (proj2_sig c) (proj2_sig t) (proj2_sig e))
       end.

(** NOTE: we don't let [SubFunctor] introduce implicitly because it would
introduce a copy of [Functor If2] and make a mess... *)

Variant ForInduction :=.

Global Instance ProofAlgebra__If2
       {F} `{FunctorLaws F} `{S : ! F supports If2}
       `(P : forall (e : Fix F), FoldUP' e -> Prop)
       `(H__if2 : forall c t e
                   (IH__c : UniversalPropertyP P c)
                   (IH__t : UniversalPropertyP P t)
                   (IH__e : UniversalPropertyP P e),
            UniversalPropertyP P (if2_UPP_Fix IH__c IH__t IH__e))
  : ProofAlgebra ForInduction If2 (sig (UniversalPropertyP P))
  := {| proofAlgebra := Induction__If2 P H__if2 |}.

Global Instance WellFormedProofAlgebra__If2
       F `{FunctorLaws F} `{! F supports If2} `{! WellFormedSubFunctor If2 F}
       `(P : forall (e : Fix F), FoldUP' e -> Prop)
       `(H__if2 : forall c t e
                   (IH__c : UniversalPropertyP P c)
                   (IH__t : UniversalPropertyP P t)
                   (IH__e : UniversalPropertyP P e),
            UniversalPropertyP P (if2_UPP_Fix IH__c IH__t IH__e)
        )
  : WellFormedProofAlgebra (ProofAlgebra__If2 P H__if2).
Proof.
  constructor.
  rewrite /= / Induction__If2.
  move => [] c t e /=.
  rewrite / if2_UPP_Fix / if2 / if2 / inject /=.
  erewrite wellFormedSubFunctor => /=.
  reflexivity.
Qed.

Section Two.

  Context
    {E}
    `{FunctorLaws E}
    `{! E supports If2}
  .

  Context
    {F}
    `{FunctorLaws F}
    `{! F supports If2}
  .

  Definition Induction2__If2
             (P : forall (e : Fix E * Fix F), FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
             (H__if2  : forall c t e
                        (H__c : UniversalPropertyP2 P c)
                        (H__t : UniversalPropertyP2 P t)
                        (H__e : UniversalPropertyP2 P e)
               ,
                 UniversalPropertyP2
                   P
                   (if2F'
                      (exist _ _ (proj1 (proj1_sig H__c)))
                      (exist _ _ (proj1 (proj1_sig H__t)))
                      (exist _ _ (proj1 (proj1_sig H__e)))
                    ,
                    if2F'
                      (exist _ _ (proj2 (proj1_sig H__c)))
                      (exist _ _ (proj2 (proj1_sig H__t)))
                      (exist _ _ (proj2 (proj1_sig H__e)))
             ))
    : Algebra If2 (sig (UniversalPropertyP2 P))
    := fun '(MkIf2 c t e) =>
         exist
           (UniversalPropertyP2 P) _
           (H__if2
              (proj1_sig c)
              (proj1_sig t)
              (proj1_sig e)
              (proj2_sig c)
              (proj2_sig t)
              (proj2_sig e)
           ).

End Two.
