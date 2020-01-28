From Coq Require Import ssreflect.

From ExtensibleCompiler.Syntax.Terms Require Import If2.

From ExtensibleCompiler.Syntax.Types Require Import BoolType.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import IndexedFunctor.
From ExtensibleCompiler.Theory Require Import ProgramAlgebra.
From ExtensibleCompiler.Theory Require Import ProofAlgebra.
From ExtensibleCompiler.Theory Require Import SubFunctor.
From ExtensibleCompiler.Theory Require Import Types.
From ExtensibleCompiler.Theory Require Import TypeSoundness.
From ExtensibleCompiler.Theory Require Import UniversalProperty.

Local Open Scope SubFunctor_scope.

Section If2.

  Context
    {T}
    `{FunctorLaws T}
    `{! T supports BoolType}
    `{! WellFormedSubFunctor BoolType T}
  .

  Context
    {typeEqualityForT : forall R, ProgramAlgebra ForTypeEquality T R (TypeEqualityResult T)}
    (* {typeEqualityCorrectnessForT
     : ProofAlgebra ForTypeEqualityCorrectness
                    T (sig (UniversalPropertyP typeEqualityCorrectnessStatement))} *)
  .

  Definition typeOf__If2
    : forall {R}, MixinAlgebra If2 R (TypeOfResult T)
    := fun _ rec '(MkIf2 c t e) =>
         match rec c with
         | Some cType =>
           if isBoolType (proj1_sig cType)
           then
             match (rec t, rec e) with
             | (Some tType, Some eType) =>
               if typeEquality (proj1_sig tType) eType
               then Some tType
               else None
             | _ => None
             end
           else None
         | None => None
         end.

  Global Instance TypeOf__If2
    : forall {R}, ProgramAlgebra ForTypeOf If2 R (TypeOfResult T)
    := fun _ => {| programAlgebra := typeOf__If2; |}.

  Definition TypeOf__If2'
    : forall R, ProgramAlgebra ForTypeOf If2 R (TypeOfResult T)
    := fun _ => TypeOf__If2.

  Global Instance WellFormedMendlerAlgebra_TypeOf__If2
    : WellFormedMendlerAlgebra TypeOf__If2'.
  Proof.
    constructor.
    move => T' T'' f rec [] //.
  Qed.

  Context
    {E}
    `{FunctorLaws E}
    `{E supports If2}
  .

  Inductive WellTyped__If2
            (WT : (TypedExpr T E)-indexedProp)
    : (TypedExpr T E)-indexedProp
    :=
    | WellTyped__if2 : forall t e condition thenBranch elseBranch,
        proj1_sig e = if2__F condition thenBranch elseBranch ->
        WT {| type := boolType';  expr := condition; |} ->
        WT {| type := t;          expr := thenBranch; |} ->
        WT {| type := t;          expr := elseBranch; |} ->
        WellTyped__If2 WT {| type := t; expr := e; |}
  .

  Global Instance IndexedFunctor_WellTyped__If2
    : IndexedFunctor (TypedExpr T E) WellTyped__If2.
  Proof.
    constructor.
    move => A B i IH [] [t UP__t] [e UP__e] /= => cond thenB elseB Eq__e.
    move : Eq__e UP__e => -> => UP__e H__c H__t H__e.
    econstructor => //; apply IH => //.
  Qed.

End If2.
