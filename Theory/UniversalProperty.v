From Coq Require Import FunctionalExtensionality.
From Coq Require Import ssreflect.
From Coq Require Import String.

From ExtensibleCompiler.Theory Require Import Algebra.
From ExtensibleCompiler.Theory Require Import Functor.
From ExtensibleCompiler.Theory Require Import SubFunctor.

Local Open Scope SubFunctor_scope.

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
Lemma MendlerFold__UP (* cf. [Universal_Property] *)
      F A
      (alg : MendlerAlgebra F A) (h : Fix F -> A)
  : h = mendlerFold alg ->
    forall e, h (wrap__F e) = alg (Fix F) h e.
Proof.
  intros P.
  rewrite P.
  unfold wrap__F, mendlerFold.
  reflexivity.
Qed.

(**
[h . wrapFix = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class MendlerFold__UP' (* cf. [Universal_Property'] *)
      {F} `{Functor F} (e : Fix F)
  :=
    {
      mendlerFold__UP' (* cf.  *)
      : forall A (f : MendlerAlgebra F A) (h : Fix F -> A),
        (forall e', h (wrap__F e') = f _ h e') ->
        h e = mendlerFold f e;
    }.

(**
[h = fold alg -> h . wrapFix = alg h]

Holds by definition of [fold] and [wrapFix].
 *)
Lemma Fold__UP
           F `{Functor F}
           A (alg : Algebra F A) (h : Fix F -> A)
  : h = fold alg ->
    forall e, h (wrap__F e) = alg (fmap h e).
Proof.
  intros P e.
  rewrite P.
  reflexivity.
Qed.

(**
[h . wrapFix = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class Fold__UP' (* cf. [Universal_Property'_fold] *)
      {F} {FF : Functor F} (e : Fix F)
  :=
    {
      fold__UP' (* cf. [E_fUP'] *)
      : forall A (alg : Algebra F A) (h : Fix F -> A),
        (forall e, h (wrap__F e) = alg (fmap h e)) ->
        h e = fold alg e;
    }.

Lemma fold_wrap__F_Identity
      {F : Set -> Set} `{FF : Functor F} `{FunctorLaws F}
      (e : Fix F)
      {RFUP : Fold__UP' e}
  : fold wrap__F e = e.
Proof.
  apply sym_eq.
  replace e with (id e) at 1 by reflexivity.
  apply fold__UP'; intros e'.
  rewrite fmapId.
  reflexivity.
Qed.

(**
A [WellFormedValue] for a functor [V] is a value of type [Fix V] s.t. it has
been properly constructed, and as such, satisfies [Fold__UP'].
 *)
Definition WellFormedValue
           V `{FunctorLaws V}
  := { e : Fix V | Fold__UP' e }.

Definition wrap__UP' (* cf. [in_t_UP'] *)
           {F} `{FunctorLaws F}
           (v : F (WellFormedValue F))
  : WellFormedValue F.
  apply (exist _ (wrap__F (fmap (F := F) (@proj1_sig _ _) v))).
  constructor.
  intros A alg rec EQ.
  rewrite EQ.
  unfold fold, mendlerFold.
  unfold wrap__F.
  repeat rewrite fmapFusion.
  f_equal.
  f_equal.
  unfold Extras.compose.
  apply functional_extensionality.
  intros [e' E'].
  simpl.
  apply fold__UP'.
  assumption.
Defined.

Definition unwrap__UP' (* cf. [out_t_UP'] *)
           {F} `{FunctorLaws F}
           (v : Fix F)
  : F (WellFormedValue F)
  := fold (fmap wrap__UP') v.

Theorem wrap_unwrap__UP' (* cf. [in_out_UP'_inverse] *)
        H `{FunctorLaws H}
  : forall (h : Fix H),
    Fold__UP' h ->
    proj1_sig (wrap__UP' (unwrap__UP' h)) = h.
Proof.
  move => h UP /=.
  admit.
Admitted.

Lemma unwrap__UP'_wrap__F
      {F} `{FunctorLaws F}
  : forall (e : F (Fix F)),
    unwrap__UP' (wrap__F e) = fmap (fun e => wrap__UP' (unwrap__UP' e)) e.
Proof.
  move => e.
  rewrite {1} / unwrap__UP'.
  setoid_rewrite Fold__UP => //.
  rewrite fmapFusion //.
Qed.

(**
This could be called [inject__UP'], but we will use it a lot, so it gets to be
[inject].
 *)
Definition inject (* cf. [inject'] *)
           {F G}
           `{S : SubFunctor F G}
           (fexp : F (WellFormedValue G))
  : WellFormedValue G
  := wrap__UP' (inj fexp).

Fixpoint boundedFix__UP'
         {A} {F} `{FunctorLaws F}
         (n : nat)
         (fM : MixinAlgebra F (WellFormedValue F) A)
         (default : A)
         (e : WellFormedValue F)
  : A
  :=
  match n with
  | 0   => default
  | S n => fM (boundedFix__UP' n fM default) (unwrap__UP' (proj1_sig e))
  end.

Definition UniversalPropertyP (* cf. [UP'_P] *)
           {F} `{FunctorLaws F}
           (P : forall e : Fix F, Fold__UP' e -> Prop)
           (e : Fix F)
  : Prop
  := sig (P e).

Definition UniversalPropertyP2 (* cf. [UP'_P2] *)
           {F G} `{FunctorLaws F} `{FunctorLaws G}
           (P : forall e : Fix F * Fix G, Fold__UP' (fst e) /\ Fold__UP' (snd e) -> Prop)
           (e : Fix F * Fix G)
  : Prop
  := sig (P e).

Definition UniversalPropertyF (* cf. [UP'_F] *)
           F `{FunctorLaws F}
  : Set
  := sig (Fold__UP' (F := F)).

(**
This could be called [project__UP'], but we will almost always use it so let's
just call it [project].
 *)
Definition project
           {F G}
           `{S : SubFunctor F G}
           (g : Fix G)
  : option (F (WellFormedValue G))
  := prj (unwrap__UP' g).

Definition project__F
           {F G}
           `{S : SubFunctor F G}
           (g : WellFormedValue G)
  : option (F (Fix G))
  := option_map (fmap (proj1_sig (A := Fix G) (P := _))) (project (proj1_sig g)).
