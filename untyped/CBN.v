Require Import Autosubst.Autosubst.
Require Import Relations.
From Metatheories Require Import ARS Term Reduction Leftmost.

Inductive cbn : relation term :=
  | cbn_appabs t11 t2 : cbn (tapp (tabs t11) t2) (t11.[t2/])
  | cbn_app t1 t1' t2 :
      cbn t1 t1' ->
      cbn (tapp t1 t2) (tapp t1' t2).

Hint Constructors cbn.
Local Hint Constructors clos_refl_trans.

Lemma ecbn_appabs t11 t2 t' :
  t' = t11.[t2/] ->
  cbn (tapp (tabs t11) t2) t'.
Proof. intros. subst. eauto. Qed.

Lemma cbn_app_multi t1 t1' t2 :
  clos_refl_trans _ cbn t1 t1' ->
  clos_refl_trans _ cbn (tapp t1 t2) (tapp t1' t2).
Proof. induction 1; eauto. Qed.

Lemma cbn_abs_multi_inv t1 t' :
  clos_refl_trans _ cbn (tabs t1) t' ->
  t' = tabs t1.
Proof.
  intros Hrt.
  apply clos_rt_rt1n in Hrt.
  inversion Hrt; subst; eauto.
  - inversion H.
Qed.

Lemma cbn_rename t t' r :
  cbn t t' ->
  cbn (rename r t) (rename r t').
Proof.
  induction 1; simpl; eauto.
  - apply ecbn_appabs.
    autosubst.
Qed.
Hint Resolve cbn_rename.

Lemma cbn_multi_rename t t' r :
  clos_refl_trans _ cbn t t' ->
  clos_refl_trans _ cbn (rename r t) (rename r t').
Proof. induction 1; eauto. Qed.
Hint Resolve cbn_multi_rename.

Lemma cbn_subst t t' s :
  cbn t t' ->
  cbn t.[s] t'.[s].
Proof.
  induction 1; simpl; eauto.
  - apply ecbn_appabs.
    autosubst.
Qed.
Hint Resolve cbn_subst.

Lemma cbn_multi_subst t1 t1' s :
  clos_refl_trans _ cbn t1 t1' ->
  clos_refl_trans _ cbn (t1.[s]) (t1'.[s]).
Proof. induction 1; eauto. Qed.
Hint Resolve cbn_multi_subst.

Lemma cbn_leftmost t t' : cbn t t' -> leftmost t t'.
Proof.
  induction 1; eauto.
  - destruct (neutral_dec t1) as [[] |]; subst; eauto.
    inversion H.
Qed.

Corollary cbn_multi_leftmost_multi t t' :
  clos_refl_trans _ cbn t t' ->
  clos_refl_trans _ leftmost t t'.
Proof.
  apply clos_rt_impl.
  apply cbn_leftmost.
Qed.

Hint Resolve cbn_leftmost cbn_multi_leftmost_multi.

Lemma cbn_det t t' t'' : cbn t t' -> cbn t t'' -> t' = t''.
Proof. intros ? ?. eapply leftmost_det; eauto. Qed.

Section CBNInternal.
  Inductive internal : relation term :=
  | internal_abs t t' :
      red t t' ->
      internal (tabs t) (tabs t')
  | internal_appl t1 t1' t2 :
      internal t1 t1' ->
      internal (tapp t1 t2) (tapp t1' t2)
  | internal_appr t1 t2 t2' :
      red t2 t2' ->
      internal (tapp t1 t2) (tapp t1 t2').
  Local Hint Constructors internal.

  Lemma internal_red t t' :
    internal t t' ->
    red t t'.
  Proof. induction 1; eauto. Qed.
  Hint Resolve internal_red.

  Lemma cbn_or_internal t t' :
    red t t' ->
    cbn t t' \/ internal t t'.
  Proof.
    induction 1; eauto.
    - destruct IHred; eauto.
  Qed.

  Lemma internal_cbn_swap t1 t2 :
    internal t1 t2 ->
    forall t3,
      cbn t2 t3 ->
      exists t2', cbn t1 t2' /\ clos_refl_trans _ red t2' t3.
  Proof.
    Local Hint Resolve red_subst.
    induction 1; inversion 1; subst.
    - inversion H; subst; eauto.
    - edestruct IHinternal as [? []]; eauto.
    - eexists.
      split; eauto.
      apply red_subst_multi; eauto.
      intros [| ?]; simpl; eauto.
    - eauto 7.
  Qed.

  Corollary red_cbn_swap t1 t2 :
    red t1 t2 ->
    forall t3,
      cbn t2 t3 ->
      exists t2', cbn t1 t2' /\ clos_refl_trans _ red t2' t3.
    Proof.
      intros Hred ? Hcbn.
      destruct (cbn_or_internal _ _ Hred); eauto 6.
      eapply internal_cbn_swap; eauto.
    Qed.

  Lemma red_multi_cbn_swap t1 t2 :
    clos_refl_trans _ red t1 t2 ->
    forall t3,
      cbn t2 t3 ->
      exists t2', cbn t1 t2' /\ clos_refl_trans _ red t2' t3.
  Proof.
    intros Hrt.
    apply clos_rt_rt1n in Hrt.
    induction Hrt; eauto.
    - intros ? ?.
      edestruct IHHrt as [? [? ?]]; eauto.
      edestruct red_cbn_swap as [? [? ?]]; eauto.
  Qed.

  Theorem quasi_cbn_theorem t :
    Acc (fun t2 t1 => cbn t1 t2) t ->
    Acc (fun t3 t1 => exists t2, clos_refl_trans _ red t1 t2 /\ cbn t2 t3) t.
  Proof.
    induction 1 as [t ? IH].
    constructor.
    intros ? [? [Hred Hcbn]].
    destruct (red_multi_cbn_swap _ _ Hred _ Hcbn) as [? [Hcbn']].
    destruct (IH _ Hcbn') as [IH'].
    constructor.
    intros ? [? [? ?]].
    eauto.
  Qed.
End CBNInternal.