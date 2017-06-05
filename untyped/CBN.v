Require Import Autosubst.Autosubst.
Require Import Relations.
From Metatheories Require Import Term Reduction Leftmost.

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
  - inversion H; subst; eauto.
Qed.
Hint Resolve cbn_leftmost.

Lemma cbn_det t t' t'' : cbn t t' -> cbn t t'' -> t' = t''.
Proof. intros ? ?. eapply leftmost_det; eauto. Qed.
