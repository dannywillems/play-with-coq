Require Import List.

Check 1::2::3::nil.

Compute
  map (fun x => x + 2) (1::2::3::nil).

(* 6. Proving properties of programs on lists *)

Fixpoint count (n : nat) (l : list nat) : nat :=
  match l with
  | nil => 0
  | h::tl =>
      let r := count n tl in if Nat.eqb n h then 1 + r else r
  end.
