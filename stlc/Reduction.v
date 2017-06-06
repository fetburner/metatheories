Require Import Autosubst.Autosubst.
Require Import Arith List Program Omega Relations.
Require Term Types.

Inductive red : Term.t -> Term.t -> Prop :=
  | R_Abs : forall t e e',
      red e e' ->
      red (Term.Abs t e) (Term.Abs t e')
  | R_AppL : forall e1 e1' e2,
      red e1 e1' ->
      red (Term.App e1 e2) (Term.App e1' e2)
  | R_AppR : forall e1 e2 e2',
      red e2 e2' ->
      red (Term.App e1 e2) (Term.App e1 e2')
  | R_Red : forall t e e2,
      red (Term.App (Term.Abs t e) e2) (e.[e2/]).
Hint Constructors red clos_refl_trans.

Lemma ered_appabs T t11 t2 t :
  t = t11.[t2/] ->
  red (Term.App (Term.Abs T t11) t2) t.
Proof. intros. subst. econstructor. Qed.

Lemma red_subst t t' :
  red t t' ->
  forall s,
  red t.[s] t'.[s].
Proof.
  induction 1; simpl; intros ?; eauto.
  - apply ered_appabs.
    autosubst.
Qed.
Hint Resolve red_subst.
