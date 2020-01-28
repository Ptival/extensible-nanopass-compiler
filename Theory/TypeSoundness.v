From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Environment.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import IndexedSubFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Record TypedExpr (* cf. WFValue_i *)
       T E `{FunctorLaws T} `{FunctorLaws E}
  : Set
  := MkTypedValue (* cf. mk_WFValue_i *)
       {
         type : UniversalPropertyF T;
         expr : UniversalPropertyF E;
       }.
Arguments MkTypedValue {T E _ _ _ _}.

(**
In MTC, this is parameterized by some indexed relation.  In practice I don't
think I am using it yet, so leaving it hardcoded until it becomes necessary.
*)

Definition WellTyped
           {T E}
           `{FunctorLaws T} `{FunctorLaws E}
           (WT : (TypedExpr T E)-indexedPropFunctor)
           t e
  : Prop
  := IndexedFix WT {| type := t; expr := e; |}.

(**
This is the most abstract statement of the type soundness of evaluation.

Instead of explicitly calling recursively [evalL] and [typeOfL], this is
abstracted over the operation to run recursively, namely [recEval] and
[recTypeOf].

 *)

Definition AbstractSoundnessStatement (* cf. eval_alg_Soundness_P *)
           {T E F V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws F} `{FunctorLaws V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{eval__E   : forall {R}, MixinAlgebra E R (EvalResult   V)}
           `{typeOf__F : forall {R}, MixinAlgebra F R (TypeOfResult T)}
           (recEval   : UniversalPropertyF E -> EvalResult   V)
           (recTypeOf : UniversalPropertyF F -> TypeOfResult T)
           (e : Fix E * Fix F)
           (RFUP_e : FoldUP' (fst e) /\ FoldUP' (snd e))
  : Prop
  :=
    forall

      (* Commenting those out temporarily to see where they are needed! *)

      (* recEvalProj : forall (e : UniversalPropertyF L),
          recEval e
          =
          recEval (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig e)))
      *)

      (* recTypeOfProj : forall (e : UniversalPropertyF L'),
          recTypeOf e
          =
          recTypeOf (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig e)))
      *)

      Gamma

      (IH : forall (Gamma : Environment (ValueFix V))
              (a : UniversalPropertyF E * UniversalPropertyF F),
          (forall (tau : TypeFix T),
              typeOf__F recTypeOf (unwrapUP' (proj1_sig (snd a))) = Some tau ->
              WellTyped WT tau (eval__E recEval (unwrapUP' (proj1_sig (fst a))) Gamma)
          ) ->
          forall (tau : TypeFix T),
            recTypeOf (snd a) = Some tau ->
            WellTyped WT tau (recEval (wrapUP' (unwrapUP' (proj1_sig (fst a)))) Gamma)
      )
    ,
    forall (tau : TypeFix T),
      typeOf__F recTypeOf (unwrapUP' (snd e)) = Some tau ->
      WellTyped WT tau (eval__E recEval (unwrapUP' (fst e)) Gamma).

Variant ForSoundness := .

Definition Soundness__ProofAlgebra
           {T E V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
           `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
  := forall recEval recTypeOf,
    ProofAlgebra ForSoundness
      E
      (sig
         (UniversalPropertyP2
            (AbstractSoundnessStatement
               (eval__E   := fun _ => programAlgebra' Eval__E)
               (typeOf__F := fun _ => programAlgebra' TypeOf__E)
               WT
               recEval recTypeOf
      ))).

Lemma Soundness
      {T E V}
      `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
      (WT : (TypedExpr T V)-indexedPropFunctor)
      `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
      `{WFEval__E : ! WellFormedMendlerAlgebra (@Eval__E)}
      `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
      `{WFTypeOf__E : ! WellFormedMendlerAlgebra (@TypeOf__E)}
      (soundness__ProofAlgebra : Soundness__ProofAlgebra WT)
      (WF_eval_Soundness_alg_F :
         forall recEval recTypeOf,
           WellFormedProofAlgebra2 (soundness__ProofAlgebra recEval recTypeOf)
      )
  : forall (e : WellFormedValue E) Gamma (tau : TypeFix T),
    typeOf (proj1_sig e) = Some tau ->
    WellTyped WT tau (eval (proj1_sig e) Gamma).
Proof.
  move => e Gamma tau TO.
  rewrite <- (wrapUP'_unwrapUP' (proj1_sig e) (proj2_sig e)).
  rewrite /= / eval / mendlerFold / wrapF.
  rewrite wellFormedMendlerAlgebra / mendlerFold.
  elim (
      Induction2
        (PA := soundness__ProofAlgebra (fun e => eval (proj1_sig e)) (fun e => typeOf (proj1_sig e)))
        _
        (proj2_sig e)
    ) => e' E'.
  apply:  E'.
  (* Missing: one premise *)
  (* Missing: one premise *)
  move => Gamma' a IH tau1 TY1.
  rewrite / eval / mendlerFold /= / wrapF.
  rewrite wellFormedMendlerAlgebra.
  rewrite / mendlerFold.
  apply : IH.
  {
    rewrite <- (wrapUP'_unwrapUP' (proj1_sig (snd a)) (proj2_sig (snd a))) in TY1.
    rewrite /= in TY1.
    rewrite / typeOf / mendlerFold / wrapF in TY1.
    erewrite wellFormedMendlerAlgebra in TY1 => //.
  }
  {
    rewrite <- (wrapF_unwrapF (proj1_sig e) (proj2_sig e)) in TO.
    rewrite / typeOf / mendlerFold / wrapF /= in TO.
    rewrite / programAlgebra'.
    erewrite <- wellFormedMendlerAlgebra.
    rewrite /= / unwrapUP'.
    erewrite Fusion.
    {
      eapply TO.
    }
    {
      move => a.
      do 2 rewrite fmapFusion => //.
    }
  }
Qed.

(*
A more concise version of [AbstractSoundnessStatement], to be used in client
files.
 *)
Definition AbstractSoundnessStatement'
           {T E V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
           `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
           (recEval   : UniversalPropertyF E -> EvalResult   V)
           (recTypeOf : UniversalPropertyF E -> TypeOfResult T)
  :=
    (AbstractSoundnessStatement
       WT
       (eval__E   := fun _ => programAlgebra' Eval__E)
       (typeOf__F := fun _ => programAlgebra' TypeOf__E)
       recEval recTypeOf
    ).

(*
A nicer version of [AbstractSoundnessStatement], to be used in client files.
 *)
Definition SoundnessStatement
           {T E V}
           `{FunctorLaws T} `{FunctorLaws E} `{FunctorLaws V}
           (WT : (TypedExpr T V)-indexedPropFunctor)
           `{Eval__E   : forall {R}, ProgramAlgebra ForEval   E R (EvalResult   V)}
           `{TypeOf__E : forall {R}, ProgramAlgebra ForTypeOf E R (TypeOfResult T)}
           (recEval   : UniversalPropertyF E -> EvalResult   V)
           (recTypeOf : UniversalPropertyF E -> TypeOfResult T)
           (e : Fix E)
           (RFUP_e : FoldUP' e)
  : Prop
  :=
    forall Gamma (tau : TypeFix T),
      typeOf e = Some tau ->
      WellTyped WT tau (eval e Gamma).
