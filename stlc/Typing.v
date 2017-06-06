Require Import Autosubst.Autosubst.
Require Import Arith List Program.
Require VarSet Types Term Constraint.

Lemma Forall_app : forall X (P : X -> Prop) l l',
  Forall P (l ++ l') -> Forall P l /\ Forall P l'.
Proof.
  intros ? ? l ? H.
  induction l; simpl in *.
  + eauto.
  + inversion H; subst.
    destruct (IHl H3).
    eauto.
Qed.

Inductive typed : (var -> option Types.t) -> Term.t -> Types.t -> Prop :=
  | T_Var env x t :
      env x = Some t ->
      typed env (Term.Var x) t
  | T_Abs env e t1 t2 :
      typed (Some t1 .: env) e t2 ->
      typed env (Term.Abs t1 e) (Types.Fun t1 t2)
  | T_App env e1 e2 t1 t2 :
      typed env e1 (Types.Fun t1 t2) ->
      typed env e2 t1 ->
      typed env (Term.App e1 e2) t2.
Hint Constructors typed.

Lemma typed_weakening env t T :
  typed env t T ->
  forall env',
  (forall x T, env x = Some T -> env' x = Some T) ->
  typed env' t T.
Proof.
  induction 1; intros ? Henv; econstructor; eauto.
  - apply IHtyped.
    intros [| ?] ? Heq.
    + inversion Heq.
      reflexivity.
    + apply Henv.
      apply Heq.
Qed.

Lemma typed_rename env t T :
  typed env t T ->
  forall r env',
  (forall x, env' (r x) = env x) ->
  typed env' (rename r t) T.
Proof.
  induction 1; intros ? ? Henv; simpl; econstructor; eauto.
  - congruence.
  - apply IHtyped.
    intros [| ?].
    + reflexivity.
    + apply Henv.
Qed.

Lemma typed_subst env t T :
  typed env t T ->
  forall s env',
  (forall x T, env x = Some T -> typed env' (s x) T) ->
  typed env' (t.[s]) T.
Proof.
  induction 1; intros ? ? Henv; simpl; eauto.
  - constructor.
    apply IHtyped.
    intros [| ?] ? Heq.
    + constructor.
      apply Heq.
    + inversion Heq.
      eapply typed_rename; eauto.
Qed.