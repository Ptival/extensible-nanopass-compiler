From Coq Require Import FunctionalExtensionality.
From Coq Require Import String.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.

(*

The universal property of folds is as follows:

  [h = fold alg   <->   h . wrapFix = alg h]

In an initial algebra setting, there is a unique implementation of [fold], so
the property can be checked once and for all.  In a Church encoding setting,
each term carries its fold, and with it, it should carry a proof.  Fortunately,
the direct direction follows from the overloaded definition of [fold] and
[wrapFix], independent of the choice of term of [Fix F].

*)

Lemma DirectMendlerFoldUniversalProperty
      F A
      (alg : MendlerAlgebra F A) (h : Fix F -> A)
  : h = mendlerFold alg ->
    forall e, h (wrapFix e) = alg (Fix F) h e.
Proof.
  intros P.
  rewrite P.
  unfold wrapFix, mendlerFold.
  reflexivity.
Qed.

Class ReverseMendlerFoldUniversalProperty
      {F} `{Functor F} (e : Fix F)
  :=
    {
      elimMendlerFoldUniversalProperty
      : forall A (f : MendlerAlgebra F A) (h : Fix F -> A),
        (forall e', h (wrapFix e') = f _ h e') ->
        h e = mendlerFold f e;
    }.

Lemma DirectFoldUniversalProperty
           F `{Functor F}
           A (alg : Algebra F A) (h : Fix F -> A)
  : h = fold alg ->
    forall e, h (wrapFix e) = alg (fmap h e).
Proof.
  intros P e.
  rewrite P.
  reflexivity.
Qed.

Class ReverseFoldUniversalProperty
      {F} {FF : Functor F} (e : Fix F)
  :=
    {
      elimFoldUniversalProperty
      : forall A (alg : Algebra F A) (h : Fix F -> A),
        (forall e, h (wrapFix e) = alg (fmap h e)) ->
        h e = fold alg e;
    }.

Lemma foldWrapFixIdentity
      {F : Set -> Set} `{FF : Functor F} `{FunctorLaws F}
      (e : Fix F)
      {RFUP : ReverseFoldUniversalProperty e}
  : fold wrapFix e = e.
Proof.
  apply sym_eq.
  replace e with (id e) at 1 by reflexivity.
  apply elimFoldUniversalProperty; intros e'.
  rewrite fmapId.
  reflexivity.
Qed.

Definition WellFormedValue (V : Set -> Set) `{Functor V} :=
  { e | ReverseFoldUniversalProperty (F := V) e }.

Definition reverseFoldWrapFix
           {F} `{Functor F} `{FunctorLaws F}
           (v : F (WellFormedValue F))
  : WellFormedValue F.
  apply (exist _ (wrapFix (fmap (F := F) (@proj1_sig _ _) v))).
  constructor.
  intros A alg rec EQ.
  rewrite EQ.
  unfold fold, mendlerFold.
  unfold wrapFix.
  repeat rewrite fmapFusion.
  f_equal.
  f_equal.
  unfold Extras.compose.
  apply functional_extensionality.
  intros [e' E'].
  simpl.
  apply elimFoldUniversalProperty.
  assumption.
Qed.

Local Open Scope SubFunctor_scope.

Definition
  injectUniversalProperty
  {F G}
  `{Functor F}
  `{Functor G} `{FunctorLaws G}
  `{F <= G}
  (fexp : F (WellFormedValue G))
  : WellFormedValue G
  := reverseFoldWrapFix (inj fexp).
