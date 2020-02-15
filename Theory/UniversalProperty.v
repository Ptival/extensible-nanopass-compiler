From Coq Require Import
     FunctionalExtensionality
     ssreflect
     String
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
    forall e, h (wrapF e) = alg (Fix F) h e.
Proof.
  intros P.
  rewrite P.
  unfold wrapF, mendlerFold.
  reflexivity.
Qed.

(**
[h . wrapF = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class MendlerFoldUP' (* cf. [Universal_Property'] *)
      {F} `{Functor F} (e : Fix F)
  :=
    {
      mendlerFoldUP' (* cf.  *)
      : forall A (f : MendlerAlgebra F A) (h : Fix F -> A),
        (forall e', h (wrapF e') = f _ h e') ->
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
    forall e, h (wrapF e) = alg (fmap h e).
Proof.
  intros P e.
  rewrite P.
  reflexivity.
Qed.

(**
[h . wrapF = alg h -> h = fold alg]

To be proven for each value of type [Fix F].
 *)
Class FoldUP' (* cf. [Universal_Property'_fold] *)
      {F} {FF : Functor F} (e : Fix F)
  :=
    {
      foldUP' (* cf. [E_fUP'] *)
      : forall A (alg : Algebra F A) (h : Fix F -> A),
        (forall e, h (wrapF e) = alg (fmap h e)) ->
        h e = fold alg e;
    }.

Lemma fold_wrapF_Identity
      {F : Set -> Set} `{FF : Functor F} `{FunctorLaws F}
      (e : Fix F)
      {UP'__e : FoldUP' e}
  : fold wrapF e = e.
Proof.
  apply sym_eq.
  replace e with (id e) at 1 by reflexivity.
  apply foldUP'; intros e'.
  rewrite fmapId.
  reflexivity.
Qed.

(**
A [WellFormedValue] for a functor [V] is a value of type [Fix V] s.t. it has
been properly constructed, and as such, satisfies [FoldUP'].
 *)
Definition WellFormedValue (* cf. [UP'_F] *)
           V `{FunctorLaws V}
  := { e : Fix V | FoldUP' e }.

Definition wrapUP' (* cf. [in_t_UP'] *)
           {F} `{FunctorLaws F}
           (v : F (WellFormedValue F))
  : WellFormedValue F.
  apply (exist _ (wrapF (fmap (F := F) (@proj1_sig _ _) v))).
  constructor.
  intros A alg rec EQ.
  rewrite EQ.
  unfold fold, mendlerFold.
  unfold wrapF.
  repeat rewrite fmapFusion.
  f_equal.
  f_equal.
  unfold Extras.compose.
  apply functional_extensionality.
  intros [e' E'].
  simpl.
  apply foldUP'.
  assumption.
Defined.

Definition unwrapUP' (* cf. [out_t_UP'] *)
           {F} `{FunctorLaws F}
           (v : Fix F)
  : F (WellFormedValue F)
  := fold (fmap wrapUP') v.

Lemma unwrapUP'_wrapF
      {E} `{FunctorLaws E}
  : forall (e : E (Fix E)),
    unwrapUP' (wrapF e) = fmap (fun e => wrapUP' (unwrapUP' e)) e.
Proof.
  move => e.
  rewrite {1} / unwrapUP'.
  setoid_rewrite FoldUP => //.
  rewrite fmapFusion //.
Qed.

Lemma fmap_unwrapUP'
      {E} `{FunctorLaws E}
  : forall (e : Fix E),
    FoldUP' e ->
    fmap (@proj1_sig _ _) (unwrapUP' e) = unwrapF e.
Proof.
  move => e UP__e.
  rewrite / unwrapF.
  apply (foldUP' _ _ (fun e => fmap (@proj1_sig _ _) (unwrapUP' e))).
  move => e'.
  rewrite fmapFusion / Extras.compose.
  rewrite unwrapUP'_wrapF.
  rewrite fmapFusion //.
Qed.

Lemma fmap_wrapF
      {E} `{FunctorLaws E}
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
   {E} `{FunctorLaws E}
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
      {E} `{FunctorLaws E}
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
   {E} `{FunctorLaws E}
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
   {E} `{FunctorLaws E}
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
        {E} `{FunctorLaws E}
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
      {E} `{FunctorLaws E}
  : forall (e e' : E (sig FoldUP')),
      wrapF (fmap (@proj1_sig _ _) e) = wrapF (fmap (@proj1_sig _ _) e') ->
      fmap (@proj1_sig _ _) e = fmap (@proj1_sig _ _) e'.
Proof.
  move => e e' / (f_equal unwrapF).
  do 2 rewrite unwrapF_wrapF_fmap.
  rewrite //.
Qed.

Definition wrapF_inversion'
           {E} `{FunctorLaws E}
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
Definition inject (* cf. [inject'] *)
           {F G}
           `{S : SubFunctor F G}
           (fexp : F (WellFormedValue G))
  : WellFormedValue G
  := wrapUP' (inj fexp).

Definition injectF (* cf. [inject] *)
           {F G}
           `{S : SubFunctor F G}
           (fexp : F (WellFormedValue G))
  : Fix G
  := proj1_sig (inject fexp).

Fixpoint boundedFixUP'
         {A} {F} `{FunctorLaws F}
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
           {F} `{FunctorLaws F}
           (P : forall e : Fix F, FoldUP' e -> Prop)
           (e : Fix F)
  : Prop
  := sig (P e).

Definition UniversalPropertyP2 (* cf. [UP'_P2] *)
           {F G} `{FunctorLaws F} `{FunctorLaws G}
           (P : forall e : Fix F * Fix G, FoldUP' (fst e) /\ FoldUP' (snd e) -> Prop)
           (e : Fix F * Fix G)
  : Prop
  := sig (P e).

(**
This could be called [projectUP'], but we will almost always use it so let's
just call it [project].
 *)
Definition project
           {F G}
           `{S : SubFunctor F G}
           (g : Fix G)
  : option (F (WellFormedValue G))
  := prj (unwrapUP' g).

Definition projectF
           {F G}
           `{S : SubFunctor F G}
           (g : WellFormedValue G)
  : option (F (Fix G))
  := option_map (fmap (proj1_sig (A := Fix G) (P := _))) (project (proj1_sig g)).

Theorem project_inject
        {F G}
        `{SubFunctor F G}
        (g : Fix G)
        (f : F (sig FoldUP'))
  : FoldUP' g ->
    project g = Some f -> g = injectF f.
Proof.
  move => UP'__g P.
  move : P (inj_prj P) => _ P.
  rewrite / injectF / inject.
  rewrite <- P.
  now rewrite wrapUP'_unwrapUP'.
Qed.
