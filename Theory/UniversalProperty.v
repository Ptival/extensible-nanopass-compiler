From Coq Require Import FunctionalExtensionality.
From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.

(**

The universal property of folds is as follows:

  [h = fold alg   <->   h . wrapFix = alg h]

In an initial algebra setting, there is a unique implementation of [fold], so
the property can be checked once and for all.  In a Church encoding setting,
each term carries its fold, and with it, it should carry a proof.  Fortunately,
the direct direction follows from the overloaded definition of [fold] and
[wrapFix], independent of the choice of term of [Fix F].

*)

(**
[h = fold alg -> h . wrapFix = alg h]

Holds by definition of [mendlerFold] and [wrapFix].
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

(**
[h . wrapFix = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class ReverseMendlerFoldUniversalProperty
      {F} `{Functor F} (e : Fix F)
  :=
    {
      elimMendlerFoldUniversalProperty
      : forall A (f : MendlerAlgebra F A) (h : Fix F -> A),
        (forall e', h (wrapFix e') = f _ h e') ->
        h e = mendlerFold f e;
    }.


(**
[h = fold alg -> h . wrapFix = alg h]

Holds by definition of [fold] and [wrapFix].
 *)
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

(**
[h . wrapFix = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class ReverseFoldUniversalProperty (* cf. [Universal_Property'_fold] *)
      {F} {FF : Functor F} (e : Fix F)
  :=
    {
      elimFoldUniversalProperty (* cf. [E_fUP'] *)
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

(**
A [WellFormedValue] for a functor [V] is a value of type [Fix V] s.t. it has
been properly constructed, and as such, satisfies
[ReverseFoldUniversalProperty].
 *)
Definition WellFormedValue
           V `{FunctorLaws V}
  := { e : Fix V | ReverseFoldUniversalProperty e }.

Definition reverseFoldWrapFix (* cf. [in_t_UP'] *)
           {F} `{FunctorLaws F}
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
Defined.

Definition reverseFoldUnwrapFix (* cf. [out_t_UP'] *)
           {F} `{FunctorLaws F}
           (v : Fix F)
  : F (WellFormedValue F)
  := fold (fmap reverseFoldWrapFix) v.

Theorem reverseFoldWrapUnwrapFix_inverse (* cf. [in_out_UP'_inverse] *)
        H `{FunctorLaws H}
  : forall (h : Fix H),
    ReverseFoldUniversalProperty h ->
    proj1_sig (reverseFoldWrapFix (reverseFoldUnwrapFix h)) = h.
Proof.
  move => h UP /=.
  admit.
Admitted.

Local Open Scope SubFunctor_scope.

Definition injectUniversalProperty (* cf. [inject'] *)
           {F G}
           `{S : SubFunctor F G}
           (fexp : F (WellFormedValue G))
  : WellFormedValue G
  := reverseFoldWrapFix (inj fexp).

Fixpoint boundedFixWellFormed
         {A} {F} `{FunctorLaws F}
         (n : nat)
         (fM : MixinAlgebra (WellFormedValue F) F A)
         (default : A)
         (e : WellFormedValue F)
  : A
  :=
  match n with
  | 0   => default
  | S n => fM (boundedFixWellFormed n fM default) (reverseFoldUnwrapFix (proj1_sig e))
  end.

Definition UniversalPropertyP (* cf. [UP'_P] *)
           {F} `{FunctorLaws F}
           (P : forall e : Fix F, ReverseFoldUniversalProperty e -> Prop)
           (e : Fix F)
  : Prop
  := sig (P e).

Definition UniversalPropertyP2 (* cf. [UP'_P2] *)
           {F G} `{FunctorLaws F} `{FunctorLaws G}
           (P : forall e : Fix F * Fix G,
               ReverseFoldUniversalProperty (fst e) /\
               ReverseFoldUniversalProperty (snd e) ->
               Prop
           )
           (e : Fix F * Fix G)
  : Prop
  := sig (P e).

Definition UniversalPropertyF (* cf. [UP'_F] *)
           F `{FunctorLaws F}
  : Set
  := sig (ReverseFoldUniversalProperty (F := F)).
