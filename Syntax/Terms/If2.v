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

Global Instance Functor__If2
  : Functor If2.
Proof.
  refine {| fmap := fun A B f '(MkIf2 c t e) => MkIf2 (f c) (f t) (f e) |}.
  - move => ? [] //.
  - move => ????? [] //.
Defined.

Section If2.

  Context
    {E}
    `{Functor E}
    `{E supports If2}
  .

  Definition if2 condition thenBranch elseBranch
    : WellFormedValue E
    := injectUP' (MkIf2 condition thenBranch elseBranch).

  Definition if2F'
             (condition thenBranch elseBranch : WellFormedValue E)
    : Fix E
    := proj1_sig (if2 condition thenBranch elseBranch).

  Definition if2F
             (condition thenBranch elseBranch : Fix E)
    : Fix E
    := wrapF (inject (MkIf2 condition thenBranch elseBranch)).

  (* FIXME: get rid of all these *)

  Definition if2_Fix_UPF
             (condition thenBranch elseBranch : Fix E)
             {IH__condition  : FoldUP' condition}
             {IH__thenBranch : FoldUP' thenBranch}
             {IH__elseBranch : FoldUP' elseBranch}
    : WellFormedValue E
    := if2
         (exist _ _ IH__condition)
         (exist _ _ IH__thenBranch)
         (exist _ _ IH__elseBranch).

  (* Definition if2_Fix_Fix *)
  (*            {E} `{Functor E} `{E supports If2} *)
  (*            (condition thenBranch elseBranch : Fix E) *)
  (*            {H_condition  : FoldUP' condition} *)
  (*            {H_thenBranch : FoldUP' thenBranch} *)
  (*            {H_elseBranch : FoldUP' elseBranch} *)
  (*   : Fix E *)
  (*   := proj1_sig (if2_Fix_UPF condition thenBranch elseBranch). *)

  Definition if2_UPP_WF
             {condition thenBranch elseBranch : Fix E}
             {P}
             (IH__condition  : UniversalPropertyP P condition)
             (IH__thenBranch : UniversalPropertyP P thenBranch)
             (IH__elseBranch : UniversalPropertyP P elseBranch)
    : WellFormedValue E
    := if2_Fix_UPF condition thenBranch elseBranch
                   (IH__condition  := proj1_sig IH__condition)
                   (IH__thenBranch := proj1_sig IH__thenBranch)
                   (IH__elseBranch := proj1_sig IH__elseBranch).

  Definition if2_UPP_Fix
             {condition thenBranch elseBranch : Fix E}
             {P}
             (IH__condition  : UniversalPropertyP P condition)
             (IH__thenBranch : UniversalPropertyP P thenBranch)
             (IH__elseBranch : UniversalPropertyP P elseBranch)
    : Fix E
    := proj1_sig (if2_UPP_WF IH__condition IH__thenBranch IH__elseBranch).

  (* Definition if2_UP_Fix *)
  (*            {E} `{Functor E} `{E supports If2} *)
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
             (P : forall (e : Fix E), FoldUP' e -> Prop)
             (IH__if2 : forall (c t e : Fix E)
                        (IH__c : UniversalPropertyP P c)
                        (IH__t : UniversalPropertyP P t)
                        (IH__e : UniversalPropertyP P e),
                 UniversalPropertyP P (if2_UPP_Fix IH__c IH__t IH__e))
    : Algebra If2 (sig (UniversalPropertyP P))
    := fun e =>
         match e with
         | MkIf2 c t e =>
           exist _ _ (IH__if2 _ _ _ (proj2_sig c) (proj2_sig t) (proj2_sig e))
         end.

  (** NOTE: we don't let [SubFunctor] introduce implicitly because it would
introduce a copy of [Functor If2] and make a mess... *)

  Variant ForInduction :=.

  Global Instance ProofAlgebra__If2
         `{P : forall (e : Fix E), FoldUP' e -> Prop}
         `{H__if2 : forall c t e
                   (IH__c : UniversalPropertyP P c)
                   (IH__t : UniversalPropertyP P t)
                   (IH__e : UniversalPropertyP P e),
             UniversalPropertyP P (if2_UPP_Fix IH__c IH__t IH__e)}
    : ProofAlgebra ForInduction If2 (sig (UniversalPropertyP P))
    := {| proofAlgebra := Induction__If2 P H__if2 |}.

  Definition WellFormedProofAlgebra__If2
             `{P : forall (e : Fix E), FoldUP' e -> Prop}
             `{H__if2 : forall c t e
                       (IH__c : UniversalPropertyP P c)
                       (IH__t : UniversalPropertyP P t)
                       (IH__e : UniversalPropertyP P e),
                       UniversalPropertyP P (if2_UPP_Fix IH__c IH__t IH__e)}
    : @WellFormedProofAlgebra
        ForInduction E If2 (UniversalPropertyP P)
        _ _ _ (ProofAlgebra__If2 (H__if2 := H__if2)).
  Proof.
    constructor.
    rewrite /= / Induction__If2.
    move => [] c t e /=.
    rewrite / if2_UPP_Fix / if2 / if2 / inject /=.
    erewrite wellFormedSubFunctor => /=.
    reflexivity.
  Qed.

End If2.

Section If2.

  Context
    {E}
    `{Functor E}
    `{! E supports If2}
  .

  Context
    {F}
    `{Functor F}
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

End If2.
