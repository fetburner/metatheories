Require Import Autosubst.Autosubst.
Require Import Arith MSets.

Module VarSet := MSetList.Make (Nat_as_OT).
Include VarSet.
Include (WProperties (VarSet)).

Definition fresh s :=
  match max_elt s with
  | None => 0
  | Some n => S n
  end.

Lemma fresh_spec : forall s, ~ In (fresh s) s.
Proof.
  unfold fresh.
  intros s ?.
  remember (max_elt s) as m.
  symmetry in Heqm.
  destruct m.
  - eapply max_elt_spec2; eauto.
  - apply max_elt_spec3 in Heqm.
    destruct (Heqm _ H).
Qed.

Hint Extern 1 (In _ (union _ _)) =>
  apply union_spec.
Hint Extern 1 (In _ (singleton _)) =>
  apply singleton_spec.
