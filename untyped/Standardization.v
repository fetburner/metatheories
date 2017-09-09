Require Import Autosubst.Autosubst.
Require Import Relations.
From Metatheories Require Import ARS Term Reduction Leftmost CBN.

Inductive st : relation term :=
  | st_var t x :
      clos_refl_trans _ cbn t (tvar x) ->
      st t (tvar x)
  | st_app t t1 t2 t1' t2' :
      clos_refl_trans _ cbn t (tapp t1 t2) ->
      st t1 t1' ->
      st t2 t2' ->
      st t (tapp t1' t2')
  | st_abs t t1 t1' :
      clos_refl_trans _ cbn t (tabs t1) ->
      st t1 t1' ->
      st t (tabs t1').
Hint Constructors st.
Local Hint Constructors clos_refl_trans.

Lemma st_refl t : st t t.
Proof. induction t; eauto. Qed.

Lemma st_abs_inv t1 t' :
  st (tabs t1) t' ->
  exists t1', t' = tabs t1'.
Proof.
  inversion 1; subst; eauto.
  - apply cbn_abs_multi_inv in H0.
    congruence.
  - apply cbn_abs_multi_inv in H0.
    congruence.
Qed.

Lemma cbn_multi_st_comp t1 t2 t3 :
  clos_refl_trans _ cbn t1 t2 ->
  st t2 t3 ->
  st t1 t3.
Proof. inversion 2; eauto. Qed.

Lemma st_rename t t' :
  st t t' ->
  forall r,
  st (rename r t) (rename r t').
Proof.
  induction 1; intros ?; simpl.
  - eapply cbn_multi_st_comp.
    + apply cbn_multi_rename.
      eassumption.
    + apply st_refl.
  - econstructor; eauto.
    apply (cbn_multi_rename _ _ _ H).
  - econstructor; eauto.
    apply (cbn_multi_rename _ _ _ H).
Qed.

Lemma st_subst t1 t1' :
  st t1 t1' ->
  forall s s',
  (forall x, st (s x) (s' x)) ->
  st (t1.[s]) (t1'.[s']).
Proof.
  induction 1; simpl; intros ? ? Hsub.
  - eapply cbn_multi_st_comp.
    + apply cbn_multi_subst.
      eassumption.
    + apply Hsub.
  - econstructor; eauto.
    apply (cbn_multi_subst _ _ _ H).
  - econstructor.
    + eapply (cbn_multi_subst _ _ _ H).
    + apply IHst.
      intros [| ?]; simpl.
      * apply st_refl.
      * apply st_rename.
        eauto.
Qed.

Lemma st_red_comp t2 t3 : red t2 t3 -> forall t1, st t1 t2 -> st t1 t3.
Proof.
  induction 1; intros ? Hst; inversion Hst; subst; eauto.
  - inversion H3; subst.
    eapply cbn_multi_st_comp.
    eapply rt_trans.
    + eassumption.
    + eapply rt_trans.
      * apply cbn_app_multi.
        eassumption.
      * apply rt_step.
        eauto.
    + apply st_subst.
      * eauto.
      * intros [| ?]; [ apply H4 | apply st_refl ].
Qed.
Hint Resolve st_red_comp.

Lemma beta_multi_st t t' :
  clos_refl_trans _ red t t' ->
  st t t'.
Proof.
  intros H.
  apply clos_rt_rtn1 in H.
  induction H; eauto.
  - apply st_refl.
Qed.

Lemma st_beta_multi t t' :
  st t t' ->
  clos_refl_trans _ red t t'.
Proof. induction 1; eauto 7. Qed.
Hint Resolve st_beta_multi.

Theorem call_by_name_property t t1 :
  clos_refl_trans _ red t (tabs t1) ->
  exists t1', clos_refl_trans _ cbn t (tabs t1').
Proof.
  intros Hred.
  apply beta_multi_st in Hred.
  inversion Hred; subst.
  eauto.
Qed.

Theorem leftmost_theorem t t' :
  in_normal_form _ red t' ->
  clos_refl_trans _ red t t' ->
  clos_refl_trans _ leftmost t t'.
Proof.
  unfold in_normal_form.
  unfold not.
  intros ? Hred.
  apply beta_multi_st in Hred.
  induction Hred; eauto 7.
  eapply rt_trans.
  - apply cbn_multi_leftmost_multi. eauto.
  - destruct (neutral_dec t1') as [[]|]; subst.
    + edestruct H; eauto.
    + destruct (neutral_dec t1) as [[]|]; subst; eauto.
        * destruct (st_abs_inv _ _ Hred1) as []; subst.
           edestruct H; eauto.
        * { apply rt_trans with (y := tapp t1' t2).
             - apply leftmost_appl_multi; eauto.
             - apply leftmost_appr_multi; unfold in_normal_form; unfold not; eauto. }
Qed.

Lemma red_multi_leftmost_swap t1 t2 t3 :
  clos_refl_trans _ red t1 t2 ->
  leftmost t2 t3 ->
  exists t2', leftmost t1 t2' /\ clos_refl_trans _ red t2' t3.
Proof.
  intros Hrt Hleftmost.
  apply beta_multi_st in Hrt.
  generalize dependent t1.
  induction Hleftmost; inversion 1; subst.
  - inversion H3; subst.
    destruct (strip_lemma _ _ _ _ H1) as [|[? []]]; subst; eauto 7.
    destruct (strip_lemma _ _ _ _ H0) as [|[? []]]; subst; eexists; split; eauto.
    apply red_subst_multi; eauto.
    intros [| ?]; simpl; eauto.
  - destruct (strip_lemma _ _ _ _ H2) as [|[? []]]; subst.
    + edestruct IHHleftmost as [? []]; eauto.
       eapply neutral_red_multi in H; eauto 8.
    + destruct (neutral_dec t0) as [[]|]; subst; eauto 8.
  - destruct (strip_lemma _ _ _ _ H3) as [|[? []]]; subst; eauto 8.
    edestruct IHHleftmost as [? []]; eauto.
    destruct (strip_lemma _ _ _ _ (leftmost_theorem _ _ H0 (st_beta_multi _ _ H5))) as [|[? []]]; subst; eauto.
    apply neutral_red_multi with (t := t3) in H; eauto.
    eexists.
    split; eauto.
    apply rt_trans with (y := tapp t1 t4); eauto 6.
  - destruct (strip_lemma _ _ _ _ H0) as [|[? []]]; subst; eauto 8.
    edestruct IHHleftmost as [? []]; eauto.
Qed.

Theorem quasi_leftmost_theorem t :
  Acc (fun t2 t1 => leftmost t1 t2) t ->
  Acc (fun t3 t1 => exists t2, clos_refl_trans _ red t1 t2 /\ leftmost t2 t3) t.
Proof.
  induction 1 as [t ? IH].
  constructor.
  intros ? [? [Hred Hleftmost]].
  destruct (red_multi_leftmost_swap _ _ _ Hred Hleftmost) as [? [Hleftmost']].
  destruct (IH _ Hleftmost') as [IH'].
  constructor.
  intros ? [? [? ?]].
  eauto.
Qed.