Require Import Autosubst.Autosubst.
Require Types Term.
Require Import Reduction Typing.

Notation SN e :=
  (Acc (fun e e' => red e' e) e).

Fixpoint reducible e t : Prop :=
  match t with
  | Types.Var _ => SN e
  | Types.Fun t1 t2 =>
      forall v, reducible v t1 -> reducible (Term.App e v) t2
  end.
Hint Constructors Acc.

Notation neutral t := match t with Term.Abs _ _ => False | _ => True end.

Lemma CR2 t : forall e e',
  red e e' ->
  reducible e t -> reducible e' t.
Proof.
  induction t; intros ? ? ? Hreducible; simpl in *; eauto.
  - inversion Hreducible; eauto.
Qed.
Hint Resolve CR2.

Lemma CR1_CR3 t :
  (forall e, reducible e t -> SN e) /\
  (forall e, neutral e ->
    (forall e', red e e' -> reducible e' t) -> reducible e t).
Proof.
  induction t; split; simpl in *; eauto.
  - intros ? H.
    destruct IHt1 as [ IHt1C1 IHt1C3 ].
    assert (Hc : reducible (Term.Var 0) t1).
    { apply IHt1C3; eauto.
      intros ? Hred.
      inversion Hred. }
    apply H in Hc.
    destruct IHt2 as [ IHt2C1 ].
    apply IHt2C1 in Hc.
    clear H.
    remember (Term.App e (Term.Var 0)) as e'.
    generalize dependent e.
    induction Hc; intros; subst.
    eauto.
  - intros ? Hneutral H ? HRt1.
    destruct IHt1 as [ IHt1C1 IHt1C3 ].
    destruct IHt2 as [ IHt2C1 IHt2C3 ].
    apply IHt2C3; eauto.
    specialize (IHt1C1 _ HRt1).
    induction IHt1C1.
    intros ? Hred.
    inversion Hred; subst; eauto.
    inversion Hneutral.
Qed.

Let CR1 t := proj1 (CR1_CR3 t).
Let CR3 t := proj2 (CR1_CR3 t).
Hint Resolve CR1.

Lemma reducible_abs : forall e1 t1 t2,
  (forall v, reducible v t1 -> reducible (e1.[v/]) t2) ->
  reducible (Term.Abs t1 e1) (Types.Fun t1 t2).
Proof.
  simpl.
  intros ? ? ? Hsubst ? Hreducible.
  generalize (CR1 _ _ Hreducible). intros HSN.
  generalize (CR1 _ _ (Hsubst _ Hreducible)). intros HSNsubst.
  generalize dependent e1.
  induction HSN as [? ? IH].
  intros.
  remember (e1.[x/]) as e.
  generalize dependent e1.
  generalize dependent x.
  induction HSNsubst as [? ? IH'].
  intros. subst.
  apply CR3; eauto.
  intros ? Hred.
  inversion Hred; subst; eauto 7.
  inversion H4; subst.
  eapply IH'; try reflexivity; eauto.
Qed.

Lemma fundamental_property env t T :
  typed env t T ->
  forall s,
  (forall x T, env x = Some T -> reducible (s x) T) ->
  reducible (t.[s]) T.
Proof.
  induction 1; intros ? Hsubst; simpl in *; eauto.
  - intros ? Hreducible.
    apply reducible_abs; eauto.
    intros ? ?.
    rewrite subst_comp.
    apply IHtyped.
    intros [| x] ? Heq; simpl in *.
    + congruence.
    + replace ((up s (S x)).[v0/]) with (s x) by autosubst.
      eauto.
Qed.

Theorem strong_normalization env t T :
  typed env t T ->
  SN t.
Proof.
  intros Htyped.
  apply fundamental_property with (s := ids) in Htyped.
  - rewrite subst_id in Htyped.
    eauto.
  - intros ? ? ?.
    apply CR3; simpl; eauto.
    intros ? Hred.
    inversion Hred.
Qed.
