Require Import Ensembles.

Section KnasterTarski.
  Variable U : Type.
  Variable f : Ensemble U -> Ensemble U.
  Hypotheses monotone : forall X Y, Included _ X Y -> Included _ (f X) (f Y).

  Definition lfp : Ensemble U := fun x => forall X, Included _ (f X) X -> X x.

  Lemma lfp_lower_bound X : Included U (f X) X -> Included _ lfp X.
  Proof. intros HIncl ? HIn. apply HIn, HIncl. Qed.

  Lemma lfp_f_closed : Included _ (f lfp) lfp.
  Proof.
    intros ? Hf ? HIncl.
    eapply HIncl, monotone; [ | apply Hf ].
    apply lfp_lower_bound, HIncl.
  Qed.

  Lemma lfp_f_consistent : Included _ lfp (f lfp).
  Proof. intros ? HIn. apply HIn, monotone, lfp_f_closed. Qed.
End KnasterTarski.