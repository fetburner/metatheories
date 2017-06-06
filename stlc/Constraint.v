Require Import Autosubst.Autosubst.
Require Import List Recdef Omega.
Require VarSet Types.

Lemma Forall_map : forall X Y (P : Y -> Prop) (f : X -> Y) l,
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  intros ? ? ? ? l.
  split; intros H; induction l; simpl in *; inversion H; eauto.
Qed.

Definition t := list (Types.t * Types.t).

Notation FV c :=
  (fold_right VarSet.union VarSet.empty
    (map (fun p => VarSet.union (Types.FV (fst p)) (Types.FV (snd p))) c)).

Notation size c :=
  (fold_right plus 0 (map (fun p =>
    Types.size (fst p) + Types.size (snd p)) c)).

Instance HSubst_t : HSubst Types.t t :=
  fun sigma c => map (fun p => (subst sigma (fst p), subst sigma (snd p))) c.

Notation unifies s c :=
  (Forall (fun p => (fst p).[s] = (snd p).[s]) c).

Lemma subst_FV : forall x s c,
  VarSet.In x (FV (c.|[s])) ->
  exists y, VarSet.In x (Types.FV (s y)) /\ VarSet.In y (FV c).
Proof.
  intros ? ? c H.
  induction c as [| [] ]; simpl in *.
  - destruct (VarSet.empty_spec H).
  - apply VarSet.union_spec in H.
    destruct H as [ H | H ].
    + apply VarSet.union_spec in H.
      destruct H as [H | H];
      destruct (Types.subst_FV _ _ _ H) as [? []]; eauto 7.
    + destruct (IHc H) as [? []]; eauto.
Qed.

Definition lt c1 c2 :=
  (VarSet.cardinal (FV c1) <= VarSet.cardinal (FV c2)) /\
  (VarSet.cardinal (FV c2) <= VarSet.cardinal (FV c1) -> size c1 < size c2).

Lemma lt_subst : forall c x t t1 t2,
  ~VarSet.In x (Types.FV t) ->
  (t1 = t /\ t2 = Types.Var x \/ t1 = Types.Var x /\ t2 = t) ->
  lt (c.|[Types.subst_single x t]) ((t1, t2) :: c).
Proof.
  intros c x t ? ? Hmem Heq.
  assert (Hcardinal : VarSet.cardinal (FV c.|[Types.subst_single x t]) < VarSet.cardinal (FV ((t1, t2) :: c))).
  - apply VarSet.subset_cardinal_lt with (x := x); simpl.
    + intros y HIn.
      destruct (subst_FV _ _ _ HIn) as [z [H]].
      unfold Types.subst_single in *.
      destruct (Nat.eq_dec x z);
      [| apply VarSet.singleton_spec in H ];
      destruct Heq as [[] | []]; subst; simpl in *; eauto.
    + destruct Heq as [[] | []]; subst; simpl; eauto 6.
    + intros Hoccur.
      destruct (subst_FV _ _ _ Hoccur) as [z [H]].
      unfold Types.subst_single in *.
      destruct (Nat.eq_dec x z);
      [| apply VarSet.singleton_spec in H ];
      subst; eauto.
  - split; omega.
Qed.

Lemma lt_cons : forall p c,
  lt c (p :: c).
Proof.
  intros [t] c.
  split; simpl in *.
  - apply VarSet.subset_cardinal.
    intros ? ?.
    eauto.
  - specialize (Types.size_gt_0 t). intros. omega.
Qed.

Lemma lt_fun : forall t11 t12 t21 t22 c',
  lt ((t11, t21) :: (t12, t22) :: c')
    ((Types.Fun t11 t12, Types.Fun t21 t22) :: c').
Proof.
  intros.
  split; simpl.
  - apply VarSet.subset_cardinal.
    intros ? H.
    apply VarSet.union_spec in H.
    destruct H as [ H | H ].
    + apply VarSet.union_spec in H.
      destruct H; eauto 7.
    + apply VarSet.union_spec in H.
      destruct H as [ H | H ].
      * apply VarSet.union_spec in H.
        destruct H; eauto 7.
      * eauto.
  - omega.
Qed.

Hint Resolve lt_subst lt_cons lt_fun.

Lemma lt_wf : well_founded lt.
Proof.
  intros c.
  remember (VarSet.cardinal (FV c)) as n.
  generalize dependent c.
  induction n as [n IHn] using lt_wf_ind.
  intros.
  induction c as [c IHc] using (induction_ltof1 _ (fun c => size c)).
  subst.
  constructor.
  intros c' Hlt.
  destruct Hlt as [ ? Hlt ].
  destruct (eq_nat_dec (VarSet.cardinal (FV c)) (VarSet.cardinal (FV c'))).
  - apply IHc; eauto.
    apply Hlt.
    omega.
  - eapply IHn; eauto.
    omega.
Qed.

Function unify_aux c { wf lt c } :=
  match c with
  | nil => Some nil
  | (t1, t2) :: c' =>
      if Types.eq_dec t1 t2 then unify_aux c'
      else
        match t1, t2 with
        | Types.Var x, _ =>
            if VarSet.mem x (Types.FV t2) then None
            else option_map (cons (x, t2)) (unify_aux (c'.|[Types.subst_single x t2]))
        | _, Types.Var x =>
            if VarSet.mem x (Types.FV t1) then None
            else option_map (cons (x, t1)) (unify_aux (c'.|[Types.subst_single x t1]))
        | Types.Fun t11 t12, Types.Fun t21 t22 =>
            unify_aux ((t11, t21) :: (t12, t22) :: c')
        end
  end.
Proof.
  - intros. eauto.
  - intros. eauto.
  - intros. apply lt_subst; eauto.
    apply VarSet.Dec.F.not_mem_iff.
    eauto.
  - intros. apply lt_subst; eauto.
    apply VarSet.Dec.F.not_mem_iff.
    eauto.
  - apply lt_wf.
Qed.

Definition unify c :=
  option_map (fold_right
    (fun p s x => (Types.subst_single (fst p) (snd p) x).[s])
    Types.Var) (unify_aux c).

Theorem unify_sound : forall c s,
  unify c = Some s -> unifies s c.
Proof.
  intros c.
  unfold unify.
  induction c as [[| [t1 t2]] IHc] using (well_founded_induction lt_wf);
    rewrite unify_aux_equation;
    intros ? Hunify.
  - inversion Hunify.
    eauto.
  - destruct (Types.eq_dec t1 t2).
    + subst.
      eauto.
    + destruct t1; destruct t2;
        repeat match goal with
        | H : context [if VarSet.mem ?x ?s then _ else _] |- _ =>
            let b := fresh in
            let Heqb := fresh in
            remember (VarSet.mem x s) as b eqn:Heqb;
            symmetry in Heqb;
            destruct b;
            [| apply VarSet.Dec.F.not_mem_iff in Heqb ]
        | H : context [option_map _ (unify_aux ?c)] |- _ =>
            let o := fresh in
            let Heqo := fresh in
            remember (unify_aux c) as o eqn:Heqo;
            destruct o; [ simpl in H; inversion H; subst |]
        | H : Some ?s = unify_aux ?c |- _ =>
            assert (unifies (fold_right
              (fun p s x => (Types.subst_single (fst p) (snd p) x).[s])
              Types.Var s) c) by
              (apply IHc; [| rewrite <- H ]; eauto);
            clear H
        | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
        | |- Forall _ (_ :: _) => constructor
        | H : unifies _ _.|[_] |- _ => generalize (proj1 (Forall_map _ _ _ _ _) H); simpl; intros; clear H
        | H : Forall _ ?l |- Forall _ ?l =>
            eapply Forall_impl; [| apply H ];
            intros
        end;
        repeat (simpl in *; match goal with
        | H : ~VarSet.In ?x (VarSet.union ?s1 ?s2) |- _ =>
            assert (~VarSet.In x s1) by eauto;
            assert (~VarSet.In x s2) by eauto;
            clear H
        | H : context [_.[_].[_]] |- _ => rewrite subst_comp in H
        | |- context [_.[_].[_]] => rewrite subst_comp
        | |- context [Types.subst_single] => unfold Types.subst_single
        | H : context [Types.subst_single] |- _ => unfold Types.subst_single in *
        | |- context [scomp] => unfold scomp
        | H : context [scomp] |- _ => unfold scomp in H
        | |- context [funcomp] => unfold funcomp
        | H : context [funcomp] |- _ => unfold funcomp in H
        | |- context [Nat.eq_dec ?x ?y] => destruct (Nat.eq_dec x y)
        end); simpl in *; try congruence.
      * f_equal; apply Types.subst_ext; intros;
          destruct (Nat.eq_dec v x); simpl; congruence.
      * f_equal; apply Types.subst_ext; intros;
          destruct (Nat.eq_dec v x); simpl; congruence.
Qed.

Notation moregen s s' :=
  (exists s0, forall e, e.[s] = e.[s'].[s0]).

Lemma subst_single_preserves_unifies : forall x t0 s c,
  s x = t0.[s] ->
  unifies s c ->
  unifies s (c.|[Types.subst_single x t0]).
Proof.
  intros ? ? ? ? ? H.
  apply Forall_map.
  eapply Forall_impl; [| apply H ].
  intros.
  simpl in *.
  repeat rewrite Types.subst_single_preserves_unifies; eauto.
Qed.
Hint Resolve subst_single_preserves_unifies.

Lemma moregen_extend : forall s x t s',
  s x = t.[s] ->
  moregen s s' ->
  moregen s (fun y => (Types.subst_single x t y).[s']).
Proof.
  intros ? ? ? ? ? H.
  destruct H as [s'' H].
  exists s''.
  intros.
  replace (e.[fun y : var => (Types.subst_single x t0 y).[s']])
    with (e.[Types.subst_single x t0].[s']) by autosubst.
  rewrite <- H.
  rewrite Types.subst_single_preserves_unifies; eauto.
Qed.

Theorem unify_complete : forall c s,
  unifies s c ->
  exists s', unify c = Some s' /\ moregen s s'.
Proof.
  intros c.
  unfold unify.
  induction c as [[| [t1 t2]] IHc] using (well_founded_induction lt_wf);
    rewrite unify_aux_equation;
    intros s Hunifies.
  - exists Types.Var.
    split; eauto.
    eexists s.
    intros.
    autosubst.
  - destruct (Types.eq_dec t1 t2).
    + subst.
      inversion Hunifies.
      eauto.
    + inversion Hunifies. subst. clear Hunifies.
      simpl in *.
      destruct t1; destruct t2;
        repeat match goal with
        | |- context [VarSet.mem ?x ?s] =>
            let b := fresh in
            let Heqb := fresh in
            remember (VarSet.mem x s) as b eqn:Heqb;
            symmetry in Heqb;
            destruct b;
            [ apply VarSet.mem_spec in Heqb;
              exfalso;
              eapply Types.unifies_occur; eauto
            | apply VarSet.Dec.F.not_mem_iff in Heqb ]
        | |- context [unify_aux ?c] =>
            assert (H : exists s', option_map (fold_right
              (fun p s x => (Types.subst_single (fst p) (snd p) x).[s])
              Types.Var) (unify_aux c) = Some s' /\ moregen s s');
            [ apply IHc; eauto
            | destruct H as [? [H]];
              let o := fresh in
              let Heqo := fresh in
              remember (unify_aux c) as o eqn:Heqo;
              destruct o;
              [ simpl in Heqo; inversion Heqo; subst
              | simpl in H; congruence ]]
        end; simpl in *;
        repeat (match goal with
        | |- Forall _ (_ :: _) => constructor
        | |- exists _, Some _ = Some _ /\ _ =>
            eexists;
            split; [ reflexivity |]
        | H : Some _ = Some _ |- _ => inversion H; clear H
        | |- _ => apply moregen_extend
        end; simpl in *; subst);
        solve [ eauto | congruence ].
Qed.

Definition unify' : forall c,
  { s | unifies s c /\ (forall s', unifies s' c -> moregen s' s) } + {(forall s, ~unifies s c)}.
Proof.
  intros c.
  remember (unify c) as o.
  destruct o as [ s |].
  - left.
    exists s.
    split.
    + apply unify_sound; eauto.
    + intros ? Hunifies.
      destruct (unify_complete _ _ Hunifies) as [? [H]].
      rewrite <- Heqo in H.
      inversion H.
      eauto.
  - right.
    intros ? Hunifies.
    destruct (unify_complete _ _ Hunifies) as [? [H]].
    congruence.
Defined.
