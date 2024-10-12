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
Require Import Ring.
Require Import ArithRing.

Definition is_zero (n: nat) : bool :=
  match n with
  | 0 => true
  | S _ => false
  end.

(* Page 27, 28, 29 *)
Lemma not_is_zero_pred: forall x: nat, is_zero x = false -> S (pred x) = x.
Proof.
  intros x.
  unfold is_zero, Nat.pred.
  destruct x as [ | p ].
  discriminate.
  intros h.
  reflexivity.
Qed.

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

(* Section 4: Proving properties of programs on numbers *)

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

(* Lemma evenb_p: forall n: nat, evenb n = true <-> exists m: nat, n = 2 * m. *)
(* Proof. *)
(*   assert (H: forall n: nat, (evenb n = true -> exists x: nat, n = 2 * x) /\ (evenb (S n) = true -> exists x: nat, S n = 2 * x)). *)
(*   induction n. *)
(*   split. *)
(*   exists 0; ring. *)
(*   simpl; intros H; discriminate H. *)
(*   split. *)
(*   destruct IHn as [_ IHn']; exact IHn'. *)
(*   simpl evenb; intros H; destruct IHn as [IHn' _]. *)
(*   assert (H' : exists x, n = 2 * x). *)
(*   apply IHn'; exact H. *)
(*   destruct H' as [x q]; exists (x + 1); rewrite q; ring. *)
(*   destruct (Main n) as [H _]; apply H; exact ev. *)
(* Qed. *)

