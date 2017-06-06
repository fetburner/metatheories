Require Import Autosubst.Autosubst.
Require Import Arith List Omega Program.
Require Types.

Inductive t :=
  | Var (x : var)
  | Abs (T : Types.t) (s : {bind t})
  | App (t1 t2 : t).

Fixpoint FTV e :=
  match e with
  | Var _ => VarSet.empty
  | Abs t e => VarSet.union (Types.FV t) (FTV e)
  | App e1 e2 => VarSet.union (FTV e1) (FTV e2)
  end.

Instance Ids_t : Ids t. derive. Defined.
Instance Rename_t : Rename t. derive. Defined.
Instance Subst_t : Subst t. derive. Defined.
Instance SubstLemmas_t : SubstLemmas t. derive. Qed.
Instance HSubst_t : HSubst Types.t t. derive. Defined.
Instance HSubstLemmas_t : HSubstLemmas Types.t t. derive. Defined.
Instance SubstHSubstComp_t : SubstHSubstComp Types.t t. derive. Defined.

Inductive value : t -> Prop :=
  | V_Abs : forall e t, value (Abs t e).
Hint Constructors value.
