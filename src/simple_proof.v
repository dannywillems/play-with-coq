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
