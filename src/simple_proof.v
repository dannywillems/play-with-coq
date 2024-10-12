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
