From Coq Require Import
     FunctionalExtensionality
     Setoid
     ssreflect
.

From ExtensibleCompiler.Theory Require Import
     Algebra
     Functor
     SubFunctor
.

Local Open Scope SubFunctor.

(**

The universal property of folds is as follows:

  [h = fold alg   <->   h . wrapF = alg h]

In an initial algebra setting, there is a unique implementation of [fold], so
the property can be checked once and for all.  In a Church encoding setting,
each term carries its fold, and with it, it should carry a proof.  Fortunately,
the direct direction follows from the overloaded definition of [fold] and
[wrapF], independent of the choice of term of [Fix F].

*)

(**
[h = fold alg -> h . wrapF = alg h]

Holds by definition of [mendlerFold] and [wrapF].
 *)
Lemma MendlerFoldUP (* cf. [Universal_Property] *)
      F A
      (alg : MendlerAlgebra F A) (h : Fix F -> A)
  : h = mendlerFold alg ->
    forall e,
      h (wrapF e) = alg (Fix F) h e.
Proof.
  move => -> //.
Qed.

(**
[h . wrapF = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class MendlerFoldUP' (* cf. [Universal_Property'] *)
      {F}
      (e : Fix F)
  :=
    {
      mendlerFoldUP' : (* cf.  *)
        forall A (f : MendlerAlgebra F A) (h : Fix F -> A),
          (forall e', h (wrapF e') = f _ h e'
          ) ->
          h e = mendlerFold f e;
    }.

(**
[h = fold alg -> h . wrapF = alg h]

Holds by definition of [fold] and [wrapF].
 *)
Lemma FoldUP
      F `{Functor F}
      A (alg : Algebra F A) (h : Fix F -> A)
  : h = fold alg ->
    forall e,
      h (wrapF e) = alg (fmap h e).
Proof.
  move => -> //.
Qed.

(**
[h . wrapF = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class FoldUP' (* cf. [Universal_Property'_fold] *)
      {F} `{Functor F} (e : Fix F)
  :=
    {
      foldUP' : (* cf. [E_fUP'] *)
        forall A (alg : Algebra F A) (h : Fix F -> A),
          (forall e, h (wrapF e) = alg (fmap h e)) ->
          h e = fold alg e;
    }.

Lemma fold_wrapF_Identity
      {F} `{Functor F}
      (e : Fix F)
      {UP'__e : FoldUP' e}
  : fold wrapF e = e.
Proof.
  apply : sym_eq.
  apply : foldUP' => e'.
  rewrite fmapId //.
Qed.

(**
A [WellFormedValue] for a functor [V] is a value of type [Fix V] s.t. it has
been properly constructed, and as such, satisfies [FoldUP'].
 *)
Definition WellFormedValue (* cf. [UP'_F] *)
           V `{Functor V}
  := { e : Fix V | FoldUP' e }.

Definition wrapUP' (* cf. [in_t_UP'] *)
           {F} `{Functor F}
           (v : F (WellFormedValue F))
  : WellFormedValue F.
  apply (exist _ (wrapF (fmap (F := F) (@proj1_sig _ _) v))).
  constructor => A alg rec EQ.
  rewrite EQ.
  rewrite /fold /mendlerFold /wrapF.
  rewrite !fmapFusion.
  f_equal.
  f_equal.
  rewrite /compose.
  apply functional_extensionality.
  move => [e' E'] /=.
  apply foldUP' => //.
Defined.

Definition unwrapUP' (* cf. [out_t_UP'] *)
           {F} `{Functor F}
           (v : Fix F)
  : F (WellFormedValue F)
  := fold (fmap wrapUP') v.

Lemma unwrapUP'_wrapF
      {E} `{Functor E}
  : forall (e : E (Fix E)),
    unwrapUP' (wrapF e)
    =
    fmap (fun e => wrapUP' (unwrapUP' e)) e.
Proof.
  move => e.
  rewrite {1} / unwrapUP'.
  setoid_rewrite FoldUP => //.
  rewrite fmapFusion //.
Qed.

Lemma fmap_unwrapUP'
      {E} `{Functor E}
  : forall (e : Fix E),
    FoldUP' e ->
    fmap (@proj1_sig _ _) (unwrapUP' e) = unwrapF e.
Proof.
  move => e UP__e.
  rewrite / unwrapF.
  apply (foldUP' _ _ (fun e => fmap (@proj1_sig _ _) (unwrapUP' e))).
  move => e'.
  rewrite fmapFusion / compose.
  rewrite unwrapUP'_wrapF.
  rewrite fmapFusion //.
Qed.

Lemma fmap_wrapF
      {E} `{Functor E}
  :
    (fun (R : Set) (rec : R -> E (Fix E)) (e : E R) => fmap wrapF (fmap rec e))
    =
    (fun (R : Set) (rec : R -> E (Fix E)) (e : E R) => fmap (fun r => wrapF (rec r)) e).
Proof.
  eapply functional_extensionality_dep => R.
  eapply functional_extensionality_dep => rec.
  eapply functional_extensionality_dep => e.
  rewrite fmapFusion //.
Qed.

Lemma unwrapF_wrapF
   {E} `{Functor E}
  : forall (e : E (Fix E)),
    unwrapF (wrapF e) = fmap (fun e => wrapF (unwrapF e)) e.
Proof.
  move => e.
  rewrite / unwrapF /=.
  erewrite (MendlerFoldUP _ _ (fun R rec fp => fmap (fun r => wrapF (rec r)) fp)) => //.
  rewrite / fold / mendlerFold.
  eapply functional_extensionality.
  move => e'.
  rewrite fmap_wrapF //.
Qed.

Lemma wrapF_unwrapF
      {E} `{Functor E}
  : forall (e : Fix E),
    FoldUP' e ->
    wrapF (unwrapF e) = e.
Proof.
  move => e UP__e.
  rewrite <- fold_wrapF_Identity => //.
  apply (foldUP' _ _ (fun e => wrapF (unwrapF e))).
  move => e'.
  rewrite unwrapF_wrapF //.
Qed.

Lemma wrapF_fold_fmap_wrapF
   {E} `{Functor E}
  : (fun e : sig FoldUP' =>
         wrapF (fold (fmap wrapF) (proj1_sig e))) =
    @proj1_sig _ _.
Proof.
  apply : functional_extensionality.
  move => x.
  setoid_rewrite wrapF_unwrapF => //.
  move : x => [] //.
Qed.

Lemma unwrapF_wrapF_fmap
   {E} `{Functor E}
  : forall (e : E (sig (FoldUP' (F := E)))),
    unwrapF (wrapF (fmap (@proj1_sig _ _) e)) = fmap (@proj1_sig _ _) e.
Proof.
  move => e.
  rewrite / unwrapF.
  erewrite FoldUP => //.
  rewrite fmapFusion.
  rewrite fmapFusion.
  setoid_rewrite wrapF_fold_fmap_wrapF => //.
Qed.

Theorem wrapUP'_unwrapUP' (* cf. [in_out_UP'_inverse] *)
        {E} `{Functor E}
  : forall (e : Fix E),
    FoldUP' e ->
    proj1_sig (wrapUP' (unwrapUP' e)) = e.
Proof.
  move => e UP__e /=.
  rewrite fmap_unwrapUP'.
  rewrite wrapF_unwrapF //.
Qed.

(**
Proof that [wrapF] is injective, as long as the subterms have the universal
property.
 *)
Lemma wrapF_inversion (* cf. [in_t_UP'_inject] *)
      {E} `{Functor E}
  : forall (e e' : E (sig FoldUP')),
      wrapF (fmap (@proj1_sig _ _) e) = wrapF (fmap (@proj1_sig _ _) e') ->
      fmap (@proj1_sig _ _) e = fmap (@proj1_sig _ _) e'.
Proof.
  move => e e' / (f_equal unwrapF).
  do 2 rewrite unwrapF_wrapF_fmap.
  rewrite //.
Qed.

Definition wrapF_inversion'
           {E} `{Functor E}
  := fun (a b : WellFormedValue E) EQ =>
  wrapF_inversion
    (E := E)
    (unwrapUP' (proj1_sig a))
    (unwrapUP' (proj1_sig b))
    EQ.

(**
This could be called [injectUP'], but we will use it a lot, so it gets to be
[inject].
 *)
Definition injectUP' (* cf. [inject'] *)
           {E F}
           `{Functor E} `{Functor F}
           `{SubFunctor F E}
           (fexp : F (WellFormedValue E))
  : WellFormedValue E
  := wrapUP' (inject fexp).

Definition injectF (* cf. [inject] *)
           {F G}
           `{SubFunctor F G}
           (fexp : F (WellFormedValue G))
  : Fix G
  := proj1_sig (injectUP' fexp).

Fixpoint boundedFixUP'
         {F A}
         `{Functor F}
         (n : nat)
         (fM : MixinAlgebra F (WellFormedValue F) A)
         (default : A)
         (e : WellFormedValue F)
  : A
  :=
  match n with
  | 0   => default
  | S n => fM (boundedFixUP' n fM default) (unwrapUP' (proj1_sig e))
  end.

Definition UniversalPropertyP (* cf. [UP'_P] *)
           {F} `{Functor F}
           (P : forall e : Fix F, FoldUP' e -> Prop)
           (e : Fix F)
  : Prop
  := sig (P e).

Definition UniversalPropertyP2 (* cf. [UP'_P2] *)
           {F G}
           `{Functor F} `{Functor G}
           (P : forall e : Fix F * Fix G, FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
           (e : Fix F * Fix G)
  : Prop
  := sig (P e).

Definition projectUP'
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (e : Fix E)
  : option (F (WellFormedValue E))
  := project (unwrapUP' e).

Definition projectF
           {E F}
           `{Functor E} `{Functor F}
           `{E supports F}
           (e : WellFormedValue E)
  : option (F (Fix E))
  := option_map
       (fmap (proj1_sig (A := Fix E) (P := _)))
       (projectUP' (proj1_sig e)).

Theorem project_successUP'
        {E F}
        `{Functor E} `{Functor F}
        `{E supports F}
        (e : Fix E)
        (f : F { e : Fix E | FoldUP' e })
  : FoldUP' e ->
    projectUP' e = Some f ->
    e = injectF f.
Proof.
  move => UP'__g /project_success.
  rewrite /injectF /injectUP' => <- .
  rewrite wrapUP'_unwrapUP' //.
Qed.
