(**
This hack by @gares forces the ssrflect [have] tactic to resolve typeclasses.

Without it, given a lemma:
L : forall a `{C a}, P a
running [have (L a)] adds [(C a ->  P a) -> ...] in front of your goal.

With it, running [have (L a)] adds [P a -> ...], assuming it can resolve [C a] in
front of your goal.
 *)
Notation "!! x" := (ltac:(refine x)) (at level 100, only parsing).
