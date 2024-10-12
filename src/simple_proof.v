(** When we write Qed., it means that the lemma is going to be saved as a
    theorem, and saved in the environment as a true statement.
    It will allow us to use it later.
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
