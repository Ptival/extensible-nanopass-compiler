(* TODO: better data structure *)

Definition Environment (A : Set) := list A.

Fixpoint lookup
         {A: Set} (Gamma : Environment A) (i : nat)
  : option A :=
  match (Gamma, i) with
  | (nil,         _) => None
  | (cons _ Gamma, S i') => lookup Gamma i'
  | (cons a _,    0) => Some a
  end.

Fixpoint insert
         {A : Set} (e : A) (Gamma : Environment A)
  : Environment A
  :=
    match Gamma with
    | nil       => cons e (nil)
    | cons e' Gamma => cons e' (insert e Gamma)
    end.

Definition empty A
  : Environment A
  := nil.
