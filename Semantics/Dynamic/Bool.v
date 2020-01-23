From Coq Require Import ssreflect.

From ExtensibleCompiler.Syntax.Terms Require Import Bool.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Eval.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedAlgebra.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Definition eval__Bool
           {V} `{FunctorLaws V}
           `{! V supports Bool}
  : forall {T}, MixinAlgebra Bool T (WellFormedValue V)
  := fun _ rec '(MkBool b) => boolean b.

Global Instance EvalAlgebra__Bool
       {V} `{FunctorLaws V}
       `{! V supports Bool}
  : forall {T}, ProgramAlgebra Bool T (WellFormedValue V)
  := fun _ => {| programAlgebra := eval__Bool; |}.

Inductive Eval__Bool {L V}
          `{FunctorLaws L} `{FunctorLaws V}
          `{! L supports Bool}
          `{! V supports Bool}
          (Eval_E : (WellFormedValue L * WellFormedValue V) -> Prop)
  : (WellFormedValue L * WellFormedValue V) -> Prop
  :=
  | BoolValue : forall b, Eval__Bool Eval_E (boolean b, boolean b)
.

Global Instance EvalSoundness__Bool
       {L LT V}
       `{FunctorLaws L} `{FunctorLaws LT} `{FunctorLaws V}
       `{! L supports Bool}
       (WT : (WellTypedValue V LT -> Prop) -> WellTypedValue V LT -> Prop)
       `{Eval_L   : forall {T}, ProgramAlgebra L T (EvalResult   V)}
       `{TypeOf_L : forall {T}, ProgramAlgebra L T (TypeOfResult LT)}
       (recEval   : UniversalPropertyF L -> EvalResult   V)
       (recTypeOf : UniversalPropertyF L -> TypeOfResult LT)
  : ProofAlgebra Bool
      (sig
         (UniversalPropertyP2
            (eval_alg_Soundness_P WT
               (evalL   := fun _ => programAlgebra' Eval_L)
               (typeOfL := fun _ => programAlgebra' TypeOf_L)
               recEval recTypeOf
      ))).
Proof.
  constructor.
  pose proof (
         Induction2Algebra_Bool
           (@eval_alg_Soundness_P
              _ _ _ _ _ _ _ _ _ _ _ _
              WT
              (fun _ => programAlgebra' (Eval_L   _))
              (fun _ => programAlgebra' (TypeOf_L _))
              recEval
              recTypeOf
           )
       ) as PP.
  apply : PP.
  (* apply : Induction2Algebra_Bool => b. *)
  rewrite / eval_alg_Soundness_P / UniversalPropertyP2.
  constructor => /=.
  {
    apply conj; apply : (proj2_sig (boolean b)).
  }
  {
    admit.
  }
Admitted.
