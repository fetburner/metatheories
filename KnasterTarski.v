Require Import Ensembles.

Section KnasterTarski.
  Variable U : Type.
  Variable f : Ensemble U -> Ensemble U.
  Hypotheses monotone : forall X Y, Included _ X Y -> Included _ (f X) (f Y).

  Definition lfp : Ensemble U := fun x => forall X, Included _ (f X) X -> In _ X x.

  Lemma lfp_lower_bound X : Included _ (f X) X -> Included _ lfp X.
  Proof. intros HIncl ? HIn. apply HIn, HIncl. Qed.

  Lemma lfp_f_closed : Included _ (f lfp) lfp.
  Proof.
    intros ? Hf ? HIncl.
    eapply HIncl, monotone.
    - apply lfp_lower_bound, HIncl.
    - apply Hf.
  Qed.

  Lemma lfp_f_consistent : Included _ lfp (f lfp).
  Proof. intros ? HIn. apply HIn, monotone, lfp_f_closed. Qed.

  Definition gfp : Ensemble U := fun x => exists X, Included _ X (f X) /\ In _ X x.

  Lemma gfp_upper_bound X : Included _ X (f X) -> Included _ X gfp.
  Proof. intros HIncl ? HIn. exists X. eauto. Qed.

  Lemma gfp_f_consistent : Included _ gfp (f gfp).
  Proof.
    intros ? [? [HIncl HIn]].
    eapply monotone.
    - apply gfp_upper_bound, HIncl.
    - eapply HIncl, HIn.
  Qed.

  Lemma gfp_f_closed : Included _ (f gfp) gfp.
  Proof.
    intros ? HIn.
    exists (f gfp). split.
    - apply monotone, gfp_f_consistent.
    - apply HIn.
  Qed.
End KnasterTarski.