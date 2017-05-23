Require Import Autosubst.Autosubst.
Require Import Relations Classical.
Require Import Term Reduction.

Definition Ycombinator :=
  let w := tabs (tapp (tvar 1) (tapp (tvar 0) (tvar 0))) in
  tabs (tapp w w).

Definition fixedpoint_combinator c :=
  forall f, clos_refl_sym_trans _ red (tapp c f) (tapp f (tapp c f)).

Lemma Ycombinator_is_fixedpoint_combinator : fixedpoint_combinator Ycombinator.
Proof.
  intros ?.
  apply clos_rst1n_rst.
  eright.
  - left. apply red_appabs.
  - eright.
    + left. apply red_appabs.
    + eright; [| left ].
      right.
      simpl.
      eapply ered_appr.
      * apply red_appabs.
      * autosubst.
Qed.

Theorem fixedpoint_theorem f : { x | clos_refl_sym_trans _ red x (tapp f x) }.
Proof. eexists. eapply Ycombinator_is_fixedpoint_combinator. Qed.

Notation tbool b := (tabs (tabs (tvar (if b then 1 else 0)))).

Theorem undefinability (P : term -> Prop) t t' :
  P t ->
  ~P t' ->
  (forall t t', P t -> clos_refl_sym_trans _ red t t' -> P t') ->
  ~exists f, forall t,
    (P t -> clos_refl_sym_trans _ red (tapp f t) (tbool true)) /\
    (~P t -> clos_refl_sym_trans _ red (tapp f t) (tbool false)).
Proof.
  Local Hint Constructors clos_refl_sym_trans.
  intros ? ? ? [f Hdecidable].
  (* \x. F x t' t *)
  remember (tabs (tapp (tapp (tapp (rename (+1) f) (tvar 0)) (rename (+1) t')) (rename (+1) t))) as g.
  destruct (fixedpoint_theorem g) as [p Hfixedpoint]; subst.
  destruct (Hdecidable p) as [Htrue Hfalse].
  destruct (classic (P p)) as [Hp | Hp].
  - assert (clos_refl_sym_trans _ red p t'); eauto.
    apply Htrue in Hp.
    eapply rst_trans.
    + apply Hfixedpoint.
    + eapply rst_trans.
      * apply rst_step.
        eauto.
      * { simpl.
          replace ((rename (+1) f).[p/]) with f by autosubst.
          replace ((rename (+1) t).[p/]) with t by autosubst.
          replace ((rename (+1) t').[p/]) with t' by autosubst.
          eapply rst_trans.
          - apply red_app_equiv.
            + apply red_app_equiv; eauto.
            + eauto.
          - eapply rst_trans.
            + apply rst_step.
              eauto.
            + apply rst_step.
              apply ered_appabs.
              autosubst. }
  - assert (clos_refl_sym_trans _ red p t); eauto.
    apply Hfalse in Hp.
    eapply rst_trans.
    + apply Hfixedpoint.
    + eapply rst_trans.
      * apply rst_step.
        eauto.
      * { simpl.
          replace ((rename (+1) f).[p/]) with f by autosubst.
          replace ((rename (+1) t).[p/]) with t by autosubst.
          replace ((rename (+1) t').[p/]) with t' by autosubst.
          eapply rst_trans.
          - apply red_app_equiv.
            + apply red_app_equiv; eauto.
            + eauto.
          - eapply rst_trans.
            + apply rst_step.
              eauto.
            + apply rst_step.
              apply ered_appabs.
              autosubst. }
Qed.