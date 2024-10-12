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

(** When we write Qed., it means that the lemma is going to be saved as a
    theorem, and saved in the environment as a true statement.
    It will allow us to use it later.

    If we didn't finish to prove all the goals of a lemma, the compiler will tell us something like:
    ```
    Error: Attempt to save an incomplete proof
    (there are remaining open goals).
    ```
 *)

Lemma example2: forall a b: Prop, a /\ b -> b /\ a.
Proof.
  intros a b H.
  split.
  destruct H as [Ha Hb].
  exact Hb.
  intuition.
Qed.


Lemma example1: forall a b: Prop, a \/ b -> b \/ a.
Proof.
  intros a b H.
  destruct H as [Ha | Hb].
  right; assumption.
  left; assumption.
Qed.

(* This example shows how to use other tactics. We use the keyword apply to use
   a previously demonstrated theorem *)
Lemma example4: 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Require Import Arith.

Lemma example5: forall x y: nat, (x + y) * (x + y) = x * x + 2 * x * y + y * y.
Proof.
  intros x y.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.add_assoc.
  rewrite <- Nat.add_assoc with (n := x * x).
  rewrite <- Nat.mul_comm with (n:=y) (m:=x).
  rewrite <- (Nat.mul_1_l (y * x)) at 1.
  rewrite <- Nat.mul_succ_l.
  rewrite <- Nat.mul_comm with (n:=x) (m:=y).
  rewrite <- Nat.mul_assoc.
  reflexivity.
Qed.

Lemma pred_S_eq: forall n: nat, pred (S n) = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Lemma pred_S_eq2: forall x y, x = S y -> pred x = y.
Proof.
  intros x y H.
  unfold pred.
  rewrite H.
  reflexivity.
Qed.

(* Section 3.4 of Coq in a hurry *)
(* The book mentions Omega, but it has been replaced by Lia (see
   https://coq.gitlab.io/zulip-archive/stream/237977-Coq-users/topic/.E2.9C.94.20Troubleshooting.20missing.20Omega.html)
 *)
Require Import Lia.

Lemma omega_example: forall f x y, 0 < x -> 0 < f x -> 3 * f x <= 2 * y -> f x <= y.
Proof.
  (* omega has been replaced by lia *)
  intros; lia.
Qed.

(* Exercices page 24 *)
Lemma ex1: forall a b c: Prop, a /\ (b /\ c) -> (a /\ b) /\ c.
Proof.
  intros a b c H.
  destruct H as [Ha [Hb Hc]].
  split. (* split the conjunction in two different goals *)
  split.
  exact Ha.
  exact Hb.
  exact Hc.
Qed.

Lemma ex1': forall a b c: Prop, a /\ (b /\ c) -> (a /\ b) /\ c.
Proof.
  tauto.
Qed.

Lemma ex2: forall a b c d: Prop, (a -> b) /\ (c -> d) -> (a /\ c) -> (b /\ d).
Proof.
  intros a b c d H H'.
  destruct H' as [Ha Hc].
  destruct H as [Hab Hcd].
  split.
  apply Hab.
  exact Ha.
  apply Hcd.
  exact Hc.
Qed.

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

