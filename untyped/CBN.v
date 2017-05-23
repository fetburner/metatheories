Require Import Autosubst.Autosubst.
Require Import Relations.
Require Import Term Reduction Leftmost.

Inductive cbn : relation term :=
  | cbn_appabs t11 t2 : cbn (tapp (tabs t11) t2) (t11.[t2/])
  | cbn_app t1 t1' t2 :
      cbn t1 t1' ->
      cbn (tapp t1 t2) (tapp t1' t2).

Hint Constructors cbn.
Local Hint Constructors clos_refl_trans.

Lemma cbn_app_multi t1 t1' t2 :
  clos_refl_trans _ cbn t1 t1' ->
  clos_refl_trans _ cbn (tapp t1 t2) (tapp t1' t2).
Proof. induction 1; eauto. Qed.

Lemma cbn_leftmost t t' : cbn t t' -> leftmost t t'.
Proof.
  induction 1; eauto.
  - inversion H; subst; eauto.
Qed.

Hint Resolve cbn_leftmost.

Lemma cbn_det t t' t'' : cbn t t' -> cbn t t'' -> t' = t''.
Proof. intros ? ?. eapply leftmost_det; eauto. Qed.
