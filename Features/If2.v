From Coq Require Import String.

From ExtensibleCompiler.Features Require Import Bool.
From ExtensibleCompiler.Features Require Import Types.
From ExtensibleCompiler.Features Require Import Unit.
From ExtensibleCompiler.Features Require Import Stuck.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Sum1.
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

Definition if2
           {L} `{Functor L} `{FunctorLaws L}
           `{If2 <= L}
           (condition thenBranch elseBranch : Fix L)
  : Fix L
  := inject (MkIf2 condition thenBranch elseBranch).

Definition if2__WF
           {L} `{Functor L} `{FunctorLaws L}
           `{If2 <= L}
           (condition thenBranch elseBranch : WellFormedValue L)
  : WellFormedValue L
  := injectUniversalProperty (MkIf2 condition thenBranch elseBranch).

Global Instance EvalIf2
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports Bool}
       `{O supports Stuck}
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

Global Instance EvalIf2ix
       {O} `{Functor O} `{FunctorLaws O}
       `{O supports Bool}
       `{O supports Stuck}
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

(* Inductive EvalIf2 (E V : Set -> Set) *)
(*           `{FunctorLaws E} `{FunctorLaws V} *)
(*           `{E supports If2} `{V supports BoolF} `{V supports UnitF} *)
(*           (Eval : (WellFormedValue E * WellFormedValue V) -> Prop) *)
(*   : (WellFormedValue E * WellFormedValue V) -> Prop *)
(*   := *)
(*   | If2True : forall c t e t', *)
(*       Eval (c, boolean true) -> *)
(*       Eval (t, t') -> *)
(*       EvalIf2 E V Eval (if2 c t e, t') *)
(*   | If2alse : forall c t e e', *)
(*       Eval (c, boolean false) -> *)
(*       Eval (e, e') -> *)
(*       EvalIf2 E V Eval (if2 c t e, e') *)
(* . *)

Definition If2Induction
           {F} `{FunctorLaws F} `{S : If2 <= F}
           (P : forall (e : Fix F), ReverseFoldUniversalProperty e -> Prop)
           (Hif2 : forall c t e, UniversalPropertyP P (proj1_sig c) ->
                            UniversalPropertyP P (proj1_sig t) ->
                            UniversalPropertyP P (proj1_sig e) ->
                            UniversalPropertyP P (if2 (proj1_sig c) (proj1_sig t) (proj1_sig e)))
  : Algebra If2 (sig (UniversalPropertyP P))
  := fun e =>
       match e with
       | MkIf2 c t e =>
         exist _
               (if2 (proj1_sig c) (proj1_sig t) (proj1_sig e))
               (Hif2 _ _ _ (proj2_sig c) (proj2_sig t) (proj2_sig e))
       end.

Definition If2ProofAlgebra
           {F} `{FunctorLaws F} `{S : If2 <= F}
           (P : forall (e : Fix F), ReverseFoldUniversalProperty e -> Prop)
           (Hif2 : forall c t e, UniversalPropertyP P (proj1_sig c) ->
                            UniversalPropertyP P (proj1_sig t) ->
                            UniversalPropertyP P (proj1_sig e) ->
                            UniversalPropertyP P (if2 (proj1_sig c) (proj1_sig t) (proj1_sig e)))
           : ProofAlgebra If2 (sig (UniversalPropertyP P))
  :=
  {|
    proofAlgebra := If2Induction P Hif2;
  |}.

Global Instance If2ProofAlgebraWellFormed
           {F} `{FunctorLaws F} `{S : If2 <= F}
           (P : forall (e : Fix F), ReverseFoldUniversalProperty e -> Prop)
           (Hif2 : forall c t e, UniversalPropertyP P (proj1_sig c) ->
                            UniversalPropertyP P (proj1_sig t) ->
                            UniversalPropertyP P (proj1_sig e) ->
                            UniversalPropertyP P (if2 (proj1_sig c) (proj1_sig t) (proj1_sig e)))
  : WellFormedProofAlgebra (If2ProofAlgebra P Hif2).
Proof.
  constructor.
  intros.
  simpl.
  unfold If2Induction.
  destruct e.
  simpl.
  unfold if2.
  unfold inject.
  reflexivity.
Qed.

Definition alg1 T
  : MixinAlgebra T (Bool + If2) (Fix (Bool + Stuck))
  := programAlgebra.
