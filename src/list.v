(* Arith includes <=?, =?, etc *)
Require Import Arith.
Require Import List.

Check 1::2::3::nil.

Compute
  map (fun x => x + 2) (1::2::3::nil).

(** Insert n in l in ascending order *)
Fixpoint insert n l :=
  match l with
    | nil => n::nil
    | h::tl => if n <=? h then n::l else h::(insert n tl)
  end.

(** Sort the list [l] by reinserting in order *)
Fixpoint sort l :=
  match l with
    | nil => nil
    | h::tl => insert h (sort tl)
  end.

(* 6. Proving properties of programs on lists *)

(** Count the number of occurences of [n] in the list [l] *)
Fixpoint count (n : nat) (l : list nat) : nat :=
  match l with
  | nil => 0
  | h::tl =>
      (* =? is equivalent to Nat.eqb *)
      let r := count n tl in if n =? h then 1 + r else r
  end.

(* Lemma insert_incr: forall n l, count n (insert n l) = 1 + count n l. *)
