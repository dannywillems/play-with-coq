Definition is_zero (n: nat) : bool :=
  match n with
  | 0 => true
  | S _ => false
  end.

(* Print is_zero. *)

(* Print pred. *)

Fixpoint sum_n (m: nat) : nat :=
  match m with
  | 0 => 0
  | S m' => m + sum_n m'
  end.


Print sum_n.

Fixpoint sum_2n (m: nat) (n: nat) : nat :=
  match m with
    | 0 => n
    | S m' => S (sum_2n m' n)
  end.

(* Search bool. *)

Fixpoint evenb (m: nat) : bool :=
  match m with
    | 0 => true
    | 1 => false
    | S m => negb (evenb (pred m))
  end.

Print evenb.
