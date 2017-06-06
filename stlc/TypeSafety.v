Require Import Autosubst.Autosubst.
Require Import List Relations Program.
Require Types Term Reduction Typing.

Lemma preservation e e' :
  Reduction.red e e' ->
  forall env t,
  Typing.typed env e t ->
  Typing.typed env e' t.
Proof.
  induction 1; intros ? ? Htyped; inversion Htyped; subst; eauto.

  inversion H2; subst.
  eapply Typing.typed_subst; eauto.
  intros [| ?] ? Heq; simpl in *.
  - congruence.
  - eauto.
Qed.
    