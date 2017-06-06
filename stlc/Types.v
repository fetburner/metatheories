Require Import Autosubst.Autosubst.
Require Import List Omega.
Require VarSet.

Inductive t :=
  | Fun : t -> t -> t
  | Var : var -> t.

Instance Ids_t : Ids t. derive. Defined.
Instance Rename_t : Rename t. derive. Defined.
Instance Subst_t : Subst t. derive. Defined.
Instance SubstLemmas_t : SubstLemmas t. derive. Qed.

Fixpoint FV t :=
  match t with
  | Fun t1 t2 => VarSet.union (FV t1) (FV t2)
  | Var x => VarSet.singleton x
  end.

Fixpoint size t :=
  match t with
  | Fun t1 t2 => 1 + size t1 + size t2
  | Var _ => 1
  end.

Definition eq_dec : forall t1 t2 : t, { t1 = t2 } + { t1 <> t2 }.
Proof.
  refine (fix eq_dec t1 t2 :=
    match t1 as t1_ return { t1_ = t2 } + { t1_ <> t2 } with
    | Fun t11 t12 =>
        match t2 with
        | Fun t21 t22 =>
            if eq_dec t11 t21 then
              if eq_dec t12 t22 then left _
              else right _
            else right _
        | _ => right _
        end
    | Var x =>
        match t2 with
        | Var y =>
            if eq_nat_dec x y then left _
            else right _
        | _ => right _
        end
    end); congruence.
Qed.

Lemma size_gt_0 : forall t,
  0 < size t.
Proof.
  intros t.
  destruct t; simpl in *; omega.
Qed.

Lemma subst_FV : forall x s t,
  VarSet.In x (FV t.[s]) ->
  exists y, VarSet.In x (FV (s y)) /\ VarSet.In y (FV t).
Proof.
  intros x s t H.
  induction t; simpl in *; eauto.
  - apply VarSet.union_spec in H.
    destruct H as [H | H];
    [ destruct (IHt1 H) as [? []]
    | destruct (IHt2 H) as [? []]];
    eauto.
Qed.

Lemma subst_ext : forall s s' t,
  (forall x, VarSet.In x (FV t) -> s x = s' x) ->
  t.[s] = t.[s'].
Proof.
  intros ? ? t ?.
  induction t; simpl in *; f_equal; eauto.
Qed.

Lemma unifies_occur : forall x t,
  Var x <> t -> VarSet.In x (FV t) -> forall s, s x <> t.[s].
Proof.
  intros x t ? ? s Hunifies.
  assert (Hsize : size t.[s] <= size (s x)) by (rewrite Hunifies; omega).
  clear Hunifies.
  induction t; simpl in *.
  - apply VarSet.union_spec in H0.
    destruct H0; [ apply IHt1 | apply IHt2 ];
      try (intros Hcontra; rewrite <- Hcontra in *; simpl in *);
      solve [ omega | eauto ].
  - apply VarSet.singleton_spec in H0.
    congruence.
Qed.

Definition subst_single x t1 y :=
  if eq_nat_dec x y then t1
  else Var y.

Lemma subst_single_preserves_unifies : forall x t0 s t,
  s x = t0.[s] ->
  t.[subst_single x t0].[s] = t.[s].
Proof.
  intros ? ? ? t ?.
  induction t; simpl in *; f_equal; eauto.
  unfold subst_single.
  destruct (Nat.eq_dec x v); subst; eauto.
Qed.
