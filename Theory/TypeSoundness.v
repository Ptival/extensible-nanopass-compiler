From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Environment.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Record TypedValue (* cf. WFValue_i *)
       V LT `{FunctorLaws V} `{FunctorLaws LT}
  : Set
  := MkTypedValue (* cf. mk_WFValue_i *)
       {
         type  : UniversalPropertyF LT;
         value : UniversalPropertyF V;
       }.
Arguments MkTypedValue {V LT _ _ _ _}.

(**
In MTC, this is parameterized by some indexed relation.  In practice I don't
think I am using it yet, so leaving it hardcoded until it becomes necessary.
*)

Definition WellTyped
           {V LT}
           `{FunctorLaws V} `{FunctorLaws LT}
           (WT : (TypedValue V LT)-indexedProp)
           v lt
  : Prop
  := IndexedFix WT {| type := lt; value := v; |}.

(**
This is the most abstract statement of the type soundness of evaluation.

Instead of explicitly calling recursively [evalL] and [typeOfL], this is
abstracted over the operation to run recursively, namely [recEval] and
[recTypeOf].

 *)

Definition SoundnessStatement__EvalAlgebra (* cf. eval_alg_Soundness_P *)
           {L L' LT V}
           `{FunctorLaws L} `{FunctorLaws L'} `{FunctorLaws LT} `{FunctorLaws V}
           (WT : (TypedValue V LT -> Prop) -> TypedValue V LT -> Prop)
           `{evalL   : forall {T}, MixinAlgebra L  T (EvalResult   V)}
           `{typeOfL : forall {T}, MixinAlgebra L' T (TypeOfResult LT)}
           (recEval   : UniversalPropertyF L -> EvalResult   V)
           (recTypeOf : UniversalPropertyF L' -> TypeOfResult LT)
           (e : Fix L' * Fix L)
           (RFUP_e : Fold__UP' (fst e) /\ Fold__UP' (snd e))
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
              (a : UniversalPropertyF L' * UniversalPropertyF L),
          (forall T,
              typeOfL recTypeOf (unwrap__UP' (proj1_sig (fst a))) = Some T ->
              WellTyped WT (evalL recEval (unwrap__UP' (proj1_sig (snd a))) Gamma) T
          ) ->
          forall T,
            recTypeOf (fst a) = Some T ->
            WellTyped WT (recEval (wrap__UP' (unwrap__UP' (proj1_sig (snd a)))) Gamma) T
      )
    ,
    forall (T : TypeFix LT),
      typeOfL recTypeOf (unwrap__UP' (fst e)) = Some T ->
      WellTyped WT (evalL recEval (unwrap__UP' (snd e)) Gamma) T.

Definition Soundness__EvalAlgebra
           {L LT V}
           `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
           (WT : (TypedValue V LT -> Prop) -> TypedValue V LT -> Prop)
           `{EvalL   : forall {T}, ProgramAlgebra Eval   L T (EvalResult V)}
           `{TypeOfL : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
  := forall recTypeOf recEval,
    ProofAlgebra
      L
      (sig
         (UniversalPropertyP2
            (SoundnessStatement__EvalAlgebra
               (evalL   := fun _ => programAlgebra' EvalL)
               (typeOfL := fun _ => programAlgebra' TypeOfL)
               WT
               recTypeOf recEval
      ))).

Definition SoundnessStatement__Eval
           {L LT V}
           `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
           (WT : (TypedValue V LT -> Prop) -> TypedValue V LT -> Prop)
           `{EvalL   : forall {T}, ProgramAlgebra Eval   L T (EvalResult V)}
           `{TypeOfL : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
           (recEval : UniversalPropertyF L -> EvalResult V)
           (recTypeOf : UniversalPropertyF L -> TypeOfResult LT)
           (e : Fix L)
           (RFUP_e : Fold__UP' e)
  : Prop
  :=
    forall Gamma (T : TypeFix LT),
      typeOf e = Some T ->
      WellTyped WT (eval e Gamma) T.

Lemma Soundness__Eval
      {L LT V}
      `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
      (WT : (TypedValue V LT -> Prop) -> TypedValue V LT -> Prop)
      `{EvalL   : forall {T}, ProgramAlgebra Eval   L T (EvalResult V)}
      `{TypeOfL : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
      `{WFEvalL : ! WellFormedMendlerAlgebra (@EvalL)}
      (soundness__EvalAlgebra : Soundness__EvalAlgebra WT)
      (WF_eval_Soundness_alg_F :
         forall recTypeOf recEval,
           WellFormedProofAlgebra2 (soundness__EvalAlgebra recTypeOf recEval)
      )
  : forall (e : WellFormedValue L) Gamma (T : TypeFix LT),
    typeOf (proj1_sig e) = Some T ->
    WellTyped WT (eval (proj1_sig e) Gamma) T.
Proof.
  move => e Gamma T TO.
  rewrite <- (wrap_unwrap__UP' _ (proj1_sig e)).
  {
    rewrite // / eval / mendlerFold / wrap__UP' / wrap__F /=.
    rewrite wellFormedMendlerAlgebra.
    rewrite / mendlerFold.
    elim (
        Induction2
          (PA := soundness__EvalAlgebra (fun e => eval (proj1_sig e)) (fun e => typeOf (proj1_sig e)))
          _
          (proj2_sig e)
      ).
    rewrite / SoundnessStatement__EvalAlgebra.
    move => e' E'.
    eapply E'.
    move => Gamma' [[f F][g G]].
    rewrite wrap_unwrap__UP' /=.
    rewrite / eval / mendlerFold / unwrap__F / programAlgebra'.
    admit.
Admitted.
