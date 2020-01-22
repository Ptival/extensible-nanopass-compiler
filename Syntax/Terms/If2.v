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
Local Open Scope Sum1_scope.

Inductive If2 (A : Set) : Set :=
| MkIf2 (condition : A) (thenBranch : A) (elseBranch : A)
.
Arguments MkIf2 {A}.

Global Instance Functor_If2 : Functor If2 :=
  {|
    fmap := fun A B f '(MkIf2 c t e) => MkIf2 (f c) (f t) (f e);
  |}.

Global Instance FunctorLaws_If2 : FunctorLaws If2.
Proof.
  constructor.
  {
    intros A [].
    reflexivity.
  }
  {
    intros A B C f g [].
    reflexivity.
  }
Qed.

Definition if2'
           {L} `{FunctorLaws L} `{SubFunctor If2 L}
           (condition thenBranch elseBranch : UniversalPropertyF L)
  : UniversalPropertyF L
  := injectUniversalProperty (MkIf2 condition thenBranch elseBranch).

Definition if2__UPP
           {L} `{FunctorLaws L} `{SubFunctor If2 L}
           {condition thenBranch elseBranch : Fix L}
           {P}
           (H_condition  : UniversalPropertyP P condition)
           (H_thenBranch : UniversalPropertyP P thenBranch)
           (H_elseBranch : UniversalPropertyP P elseBranch)
  : Fix L
  := proj1_sig (if2'
                  (exist _ _ (proj1_sig H_condition))
                  (exist _ _ (proj1_sig H_thenBranch))
                  (exist _ _ (proj1_sig H_elseBranch))
               ).

Definition if2
           {L} `{FunctorLaws L} `{SubFunctor If2 L}
           (condition thenBranch elseBranch : Fix L)
           {H_condition  : ReverseFoldUniversalProperty condition}
           {H_thenBranch : ReverseFoldUniversalProperty thenBranch}
           {H_elseBranch : ReverseFoldUniversalProperty elseBranch}
  : Fix L
  := proj1_sig (if2'
                  (exist _ _ H_condition)
                  (exist _ _ H_thenBranch)
                  (exist _ _ H_elseBranch)
               ).

Global Instance EvalIf2
       {O} `{FunctorLaws O}
       `{! SubFunctor Bool  O}
       `{! SubFunctor Stuck O}
       T
  : ProgramAlgebra If2 T (WellFormedValue O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(MkIf2 condition thenBranch elseBranch) =>
        match project (proj1_sig (rec condition)) with
        | Some (MkBool b) =>
          if b
          then rec thenBranch
          else rec elseBranch
        | None => stuck "The condition of a binary branch was not a boolean"
        end
    ;
  |}.

Global Instance EvalIf2Fix
       {O} `{Functor O} `{FunctorLaws O}
       `{! SubFunctor Bool  O}
       `{! SubFunctor Stuck O}
       T
  : ProgramAlgebra If2 T (Fix O)
  | 0 :=
  {|
    programAlgebra :=
      fun rec '(MkIf2 condition thenBranch elseBranch) =>
        match project (rec condition) with
        | Some (MkBool b) =>
          if b
          then rec thenBranch
          else rec elseBranch
        | None =>
          proj1_sig
            (
              stuck "The condition of a binary branch was not a boolean"
            )
        end
    ;
  |}.

Inductive EvalIf2__WF {E V}
          `{FunctorLaws E} `{FunctorLaws V}
          `{! SubFunctor If2   E}
          `{! SubFunctor Bool V}
          `{! SubFunctor Unit V}
          (Eval : (WellFormedValue E * WellFormedValue V) -> Prop)
  : (WellFormedValue E * WellFormedValue V) -> Prop
  :=
  | If2True : forall c t e t',
      Eval (c, boolean' true) ->
      Eval (t, t') ->
      EvalIf2__WF Eval (if2' c t e, t')
  | If2alse : forall c t e e',
      Eval (c, boolean' false) ->
      Eval (e, e') ->
      EvalIf2__WF Eval (if2' c t e, e')
.

Definition If2Induction
           {F} `{FunctorLaws F} `{S : SubFunctor If2 F}
           (P : forall (e : Fix F), ReverseFoldUniversalProperty e -> Prop)
           (Hif2 : forall c t e
                     (H_c : UniversalPropertyP P c)
                     (H_t : UniversalPropertyP P t)
                     (H_e : UniversalPropertyP P e),
               UniversalPropertyP P (if2__UPP H_c H_t H_e))
  : Algebra If2 (sig (UniversalPropertyP P))
  := fun e =>
       match e with
       | MkIf2 c t e =>
         exist _
               (if2 (proj1_sig c) (proj1_sig t) (proj1_sig e))
               (Hif2 _ _ _ (proj2_sig c) (proj2_sig t) (proj2_sig e))
       end.

(** NOTE: we don't let [SubFunctor] introduce implicitly because it would
introduce a copy of [Functor If2] and make a mess... *)

Global Instance If2ProofAlgebra
       {F} `{FunctorLaws F} `{S : ! SubFunctor If2 F}
       `(P : forall (e : Fix F), ReverseFoldUniversalProperty e -> Prop)
       `(H_if2 : forall c t e
                   (H_c : UniversalPropertyP P c)
                   (H_t : UniversalPropertyP P t)
                   (H_e : UniversalPropertyP P e),
            UniversalPropertyP P (if2__UPP H_c H_t H_e))
  : ProofAlgebra If2 (sig (UniversalPropertyP P))
  := {| proofAlgebra := If2Induction P H_if2; |}.

Global Instance If2ProofAlgebraWellFormed
       F `{FunctorLaws F} `{! SubFunctor If2 F} `{! WellFormedSubFunctor If2 F}
       `(P : forall (e : Fix F), ReverseFoldUniversalProperty e -> Prop)
       `(H_if2 : forall c t e
                   (IH_c : UniversalPropertyP P c)
                   (IH_t : UniversalPropertyP P t)
                   (IH_e : UniversalPropertyP P e),
            UniversalPropertyP P (if2 c t e)
        )
  : WellFormedProofAlgebra (If2ProofAlgebra P H_if2).
Proof.
  constructor.
  rewrite /= / If2Induction.
  move => [] c t e /=.
  rewrite / if2 / if2 / injectUniversalProperty /=.
  erewrite wellFormedSubFunctor => /=.
  reflexivity.
Qed.
