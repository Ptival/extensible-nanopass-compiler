(* TODO: better data structure *)

Definition Environment (A : Set) := list A.

Fixpoint lookup
         {A: Set} (env : Environment A) (i : nat)
  : option A :=
  match (env, i) with
  | (nil,         _)            => None
  | (cons _ env', S i') => lookup env' i'
  | (cons a _,    0)       => Some a
  end.

Fixpoint insert
         {A : Set} (e : A) (env : Environment A)
  : Environment A
  :=
    match env with
    | nil          => cons e (nil)
    | cons e' env' => cons e' (insert e env')
    end.

Definition empty A
  : Environment A
  := nil.
