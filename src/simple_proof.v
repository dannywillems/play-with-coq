Lemma example2: forall a b: Prop, a /\ b -> b /\ a.
Proof.
  intros a b H.
  split.
  destruct H as [Ha Hb].
  exact Hb.
  intuition.
Qed.
