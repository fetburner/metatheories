Require Import Autosubst.Autosubst ARS.ARS.
Require Import Relations.
Require Import Term Reduction.

Notation neutral t :=
  match t with tabs _ => False | _ => True end.

Inductive leftmost : relation term :=
  | leftmost_appabs t11 t2 : leftmost (tapp (tabs t11) t2) (t11.[t2/])
  | leftmost_appl t1 t1' t2 :
      neutral t1 ->
      leftmost t1 t1' ->
      leftmost (tapp t1 t2) (tapp t1' t2)
  | leftmost_appr t1 t2 t2' :
      neutral t1 ->
      in_normal_form _ red t1 ->
      leftmost t2 t2' ->
      leftmost (tapp t1 t2) (tapp t1 t2')
  | leftmost_abs t t' :
      leftmost t t' ->
      leftmost (tabs t) (tabs t').
Hint Constructors leftmost.
Local Hint Constructors clos_refl_trans.

Lemma leftmost_abs_multi t t' :
  clos_refl_trans _ leftmost t t' ->
  clos_refl_trans _ leftmost (tabs t) (tabs t').
Proof. induction 1; eauto. Qed.

Lemma leftmost_appr_multi t1 t2 t2' :
  neutral t1 ->
  in_normal_form _ red t1 ->
  clos_refl_trans _ leftmost t2 t2' ->
  clos_refl_trans _ leftmost (tapp t1 t2) (tapp t1 t2').
Proof. induction 3; eauto. Qed.

Lemma leftmost_abs_multi_inv t t' :
  clos_refl_trans _ leftmost t t' ->
  forall t1, t = tabs t1 ->
  exists t1', t' = tabs t1'.
Proof.
  induction 1; intros ? ?; subst; eauto.
  - inversion H; subst; eauto.
  - destruct (IHclos_refl_trans1 _ eq_refl); subst.
    destruct (IHclos_refl_trans2 _ eq_refl); subst.
    eauto.
Qed.

Lemma leftmost_appl_multi t1 t1' t2 :
  neutral t1 ->
  neutral t1' ->
  clos_refl_trans _ leftmost t1 t1' ->
  clos_refl_trans _ leftmost (tapp t1 t2) (tapp t1' t2).
Proof.
  induction 3; eauto.
  - assert (neutral y).
    { destruct y; simpl; eauto.
      - destruct (leftmost_abs_multi_inv _ _ H1_0 _ eq_refl); subst; simpl in *.
        eauto. }
    eauto.
Qed.

Lemma leftmost_red t t' : leftmost t t' -> red t t'.
Proof. induction 1; eauto. Qed.

Hint Resolve leftmost_abs_multi leftmost_red.

Lemma leftmost_det t t' :
  leftmost t t' ->
  forall t'',
  leftmost t t'' ->
  t' = t''.
Proof.
  induction 1;
    intros ? Hleftmost;
    inversion Hleftmost;
    subst;
    simpl in *;
    unfold in_normal_form in *;
    unfold not in *;
    f_equal;
    solve [ eauto | exfalso; eauto ].
Qed.

