Require Import Bool Arith Omega.

Variable var : Set.
Hypotheses var_eq_dec : forall x y : var, { x = y } + { x <> y }.

Definition state := var -> nat.

Definition update {A} x n (s : var -> A) := fun y =>
  if var_eq_dec x y then n else s y.

Inductive aexp : Set :=
  | AVar (x : var)
  | ANum (n : nat)
  | AMinus (a1 a2 : aexp).

Inductive bexp : Set :=
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Set :=
  | CSkip
  | CAss (x : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Fixpoint aeval s a :=
  match a with
  | ANum n => n
  | AVar x => s x
  | AMinus a1 a2 => aeval s a1 - aeval s a2
  end.

Fixpoint beval s b :=
  match b with
  | BLe a1 a2 => Nat.leb (aeval s a1) (aeval s a2)
  | BNot b => negb (beval s b)
  | BAnd b1 b2 => beval s b1 && beval s b2
  end.

Inductive ceval : com -> state -> state -> Prop :=
  | ceval_skip s : ceval CSkip s s
  | ceval_asgn a s x : ceval (CAss x a) s (update x (aeval s a) s)
  | ceval_seq c1 c2 s s' s'' :
      ceval c1 s s' ->
      ceval c2 s' s'' ->
      ceval (CSeq c1 c2) s s''
  | ceval_if_true b c1 c2 s s' :
      beval s b = true ->
      ceval c1 s s' ->
      ceval (CIf b c1 c2) s s'
  | ceval_if_false b c1 c2 s s' :
      beval s b = false ->
      ceval c2 s s' ->
      ceval (CIf b c1 c2) s s'
  | ceval_while_true b c s s' s'' :
      beval s b = true ->
      ceval c s s' ->
      ceval (CWhile b c) s' s'' ->
      ceval (CWhile b c) s s''
  | ceval_while_false b c s :
      beval s b = false ->
      ceval (CWhile b c) s s.
Hint Constructors ceval.

Lemma ceval_det c s s1 :
  ceval c s s1 ->
  forall s2,
  ceval c s s2 ->
  s1 = s2.
Proof.
  induction 1; inversion 1; subst;
    repeat match goal with
    | H : ceval ?c ?s _, IH : forall _, ceval ?c ?s _ -> _ = _ |- _ =>
        rewrite (IH _ H) in *; clear H
    end; congruence.
Qed.

Definition assert := state -> Prop.

Inductive hoare : assert -> com -> assert -> Prop :=
  | hoare_skip P : hoare P CSkip P
  | hoare_asgn a P x :
      hoare (fun s => P (update x (aeval s a) s)) (CAss x a) P
  | hoare_seq c1 c2 P Q R :
      hoare P c1 Q ->
      hoare Q c2 R ->
      hoare P (CSeq c1 c2) R
  | hoare_if b c1 c2 P Q :
      hoare (fun s => P s /\ beval s b = true) c1 Q ->
      hoare (fun s => P s /\ beval s b = false) c2 Q ->
      hoare P (CIf b c1 c2) Q
  | hoare_while b c P :
      hoare (fun s => P s /\ beval s b = true) c P ->
      hoare P (CWhile b c) (fun s => P s /\ beval s b = false)
  | hoare_conseq c (P P' Q Q' : assert) :
      (forall s, P' s -> P s) ->
      hoare P c Q ->
      (forall s, Q s -> Q' s) ->
      hoare P' c Q'.
Hint Constructors hoare.

Theorem hoare_sound c P Q :
  hoare P c Q ->
  forall s s',
  P s -> ceval c s s' -> Q s'.
Proof.
  induction 1; try solve [ inversion 2; subst; eauto ].
  remember (CWhile b c) as c0.
  induction 2; inversion Heqc0; subst; eauto.
Qed.

Definition wp c (Q : assert) : assert := fun s =>
  forall s', ceval c s s' -> Q s'.

Lemma hoare_wp c : forall Q, hoare (wp c Q) c Q.
Proof.
  induction c.
  - eauto.
  - intros P. apply hoare_conseq with (P := fun s => P (update x (aeval s a) s)) (Q := P); eauto.
  - intros R.
    apply hoare_seq with (Q := wp c2 R); eauto.
    apply hoare_conseq with (P := fun s => wp c1 (wp c2 R) s) (Q := wp c2 R); eauto.
    intros ? H ? ? ? ?. eapply H. eauto.
  - intros Q. constructor;
      [ apply hoare_conseq with (P := wp c1 Q) (Q := Q)
      | apply hoare_conseq with (P := wp c2 Q) (Q := Q) ]; eauto;
      intros ? [H ?] ? ?; eapply H; eauto.
  - intros Q. apply hoare_conseq with (P := wp (CWhile b c) Q) (Q := fun s => wp (CWhile b c) Q s /\ beval s b = false); eauto.
    + constructor. apply hoare_conseq with (P := wp c (wp (CWhile b c) Q)) (Q := wp (CWhile b c) Q); eauto.
      intros ? [H ?] ? ? ? ?. eapply H. eauto.
    + intros ? [H ?]. eapply H. eauto.
Qed.

Theorem hoare_complete c (P Q : assert) :
  (forall s s', P s -> ceval c s s' -> Q s') ->
  hoare P c Q.
Proof.
  intros H.
  apply hoare_conseq with (P := wp c Q) (Q := Q); eauto.
  - intros ? ? ?. apply H. eauto.
  - apply hoare_wp.
Qed.
