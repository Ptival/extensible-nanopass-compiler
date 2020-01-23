From Coq Require Import ssreflect.

From ExtensibleCompiler.Theory Require Import Algebra.
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

Record WellTypedValue (* cf. WellTypedValue *)
       V LT `{FunctorLaws V} `{FunctorLaws LT}
  : Set
  := MkWellTypedValue (* cf. mk_WellTypedValue *)
       {
         wellFormedValue : UniversalPropertyF V;
         wellFormedType  : UniversalPropertyF LT;
       }.

(**
In MTC, this is parameterized by some indexed relation.  In practice I don't
think I am using it yet, so leaving it hardcoded until it becomes necessary.
*)

Definition WFValue
           V LT
           `{FunctorLaws V} `{FunctorLaws LT}
           (WT : (WellTypedValue V LT)-indexedProp)
  : WellTypedValue V LT -> Prop
  := IndexedFix WT.

Definition WFValueC
           {V LT}
           `{FunctorLaws V} `{FunctorLaws LT}
           (WT : (WellTypedValue V LT)-indexedProp)
           v lt
  : Prop
  := WFValue V LT WT (MkWellTypedValue V LT _ _ _ _ v lt).

(**
This is the most abstract statement of the type soundness of evaluation.

Instead of explicitly calling recursively [evalL] and [typeOfL], this is
abstracted over the operation to run recursively, namely [recEval] and
[recTypeOf].

 *)

Definition eval_alg_Soundness_P
           {L L' LT V}
           `{FunctorLaws L} `{FunctorLaws L'} `{FunctorLaws LT} `{FunctorLaws V}
           (WT : (WellTypedValue V LT -> Prop) -> WellTypedValue V LT -> Prop)
           `{evalL   : forall {T}, MixinAlgebra L  T (EvalResult   V)}
           `{typeOfL : forall {T}, MixinAlgebra L' T (TypeOfResult LT)}
           (recEval : UniversalPropertyF L -> EvalResult V)
           (recTypeOf : UniversalPropertyF L' -> TypeOfResult LT)
           (e : Fix L' * Fix L)
           (RFUP_e : ReverseFoldUniversalProperty (fst e) /\ ReverseFoldUniversalProperty (snd e))
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

      (IH : forall (a : UniversalPropertyF L' * UniversalPropertyF L),
          (forall T,
              typeOfL recTypeOf (reverseFoldUnwrapFix (proj1_sig (fst a))) = Some T ->
              WFValueC WT (evalL recEval (reverseFoldUnwrapFix (proj1_sig (snd a)))) T
          ) ->
          forall T,
            recTypeOf (fst a) = Some T ->
            WFValueC WT (recEval (reverseFoldWrapFix (reverseFoldUnwrapFix (proj1_sig (snd a))))) T
      )
    ,
    forall (T : TypeFix LT),
      typeOfL recTypeOf (reverseFoldUnwrapFix (fst e)) = Some T ->
      WFValueC WT (evalL recEval (reverseFoldUnwrapFix (snd e))) T.

Definition Eval_Soundness_alg_F
           {L LT V}
           `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
           (WT : (WellTypedValue V LT -> Prop) -> WellTypedValue V LT -> Prop)
           `{EvalL   : forall {T}, ProgramAlgebra Eval   L T (EvalResult V)}
           `{TypeOfL : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
  := forall recTypeOf recEval,
    ProofAlgebra
      L
      (sig
         (UniversalPropertyP2
            (eval_alg_Soundness_P
               (evalL   := fun _ => programAlgebra' EvalL)
               (typeOfL := fun _ => programAlgebra' TypeOfL)
               WT
               recTypeOf recEval
      ))).

Definition eval_Soundness_P
           {L LT V}
           `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
           (WT : (WellTypedValue V LT -> Prop) -> WellTypedValue V LT -> Prop)
           `{EvalL   : forall {T}, ProgramAlgebra Eval   L T (EvalResult V)}
           `{TypeOfL : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
           (recEval : UniversalPropertyF L -> EvalResult V)
           (recTypeOf : UniversalPropertyF L -> TypeOfResult LT)
           (e : Fix L)
           (RFUP_e : ReverseFoldUniversalProperty e)
  : Prop
  :=
    forall (T : TypeFix LT),
      typeOf e = Some T ->
      WFValueC WT (eval e) T.

Lemma eval_Soundness
      {L LT V}
      `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
      (WT : (WellTypedValue V LT -> Prop) -> WellTypedValue V LT -> Prop)
      `{EvalL   : forall {T}, ProgramAlgebra Eval   L T (EvalResult V)}
      `{TypeOfL : forall {T}, ProgramAlgebra TypeOf L T (TypeOfResult LT)}
      `{WFEvalL : ! WellFormedMendlerAlgebra (@EvalL)}
      (eval_Soundness_alg_F : Eval_Soundness_alg_F WT)
      (WF_eval_Soundness_alg_F :
         forall recTypeOf recEval,
           WellFormedProofAlgebra2 (eval_Soundness_alg_F recTypeOf recEval)
      )
  : forall (e : WellFormedValue L) (T : TypeFix LT),
    typeOf (proj1_sig e) = Some T ->
    WFValueC WT (eval (proj1_sig e)) T.
Proof.
  move => e T TO.
  setoid_rewrite <- reverseFoldWrapUnwrapFix_inverse.
  {
    rewrite // / eval / mendlerFold / reverseFoldWrapFix / wrapFix /=.
    setoid_rewrite wellFormedMendlerAlgebra.
    rewrite / mendlerFold.
    elim (
        Induction2
          (PA :=
             eval_Soundness_alg_F
               (fun e => eval (proj1_sig e))
               (fun e => typeOf (proj1_sig e))
          )
          _
          (proj2_sig e)
      ).
    rewrite / eval_alg_Soundness_P.
    move => e' E'.
    eapply E'.
    move => [[f F][g G]].
    rewrite reverseFoldWrapUnwrapFix_inverse /=.
    rewrite / eval / mendlerFold / reverseFoldUnwrapFix / programAlgebra'.
    admit.
Admitted.
