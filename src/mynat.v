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
  | S p => m + sum_n p
  end.


(* Print sum_n. *)

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

(* Print evenb. *)

Require Import Ring.
(* See https://coq.inria.fr/doc/V8.4pl6/refman/Reference-Manual027.html
  Otherwise, we get
  > Error: Cannot find a declared ring structure over "nat".

```
The tactic must be loaded by Require Import Ring. The ring structures must be
declared with the Add Ring command (see below). The ring of booleans is
predefined; if one wants to use the tactic on nat one must first require the
module ArithRing (exported by Arith); for Z, do Require Import ZArithRing or
simply Require Import ZArith; for N, do Require Import NArithRing
or Require Import NArith.
```
*)

Require Import ArithRing.

(* 2 * (n * (n + 1)) / 2 = n^2 + n *)
(* Lemma sum_n_p: forall n: nat, 2 * sum_n n = n * n + n. *)
(* Proof. *)
(*   induction n. *)
(*   reflexivity. *)
(*   assert (SnSn: S n * S n = n * n + 2 * n + 1). *)
(*   ring. *)
(*   rewrite SnSn. *)
(*   rewrite <- IHn. *)
(*   simpl. *)
(*   ring. *)
(* Qed. *)
