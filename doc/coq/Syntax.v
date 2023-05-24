From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Strings.String.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Inductive expr_id :=
  | eid (x : nat)
.

Inductive mod_id :=
  | mid (M : nat)
.

Inductive mod_tm :=
  | m_empty
  | m_var (M : mod_id)
  | m_lete (x : expr_id) (e : expr_tm) (m : mod_tm)
  | m_letm (M : mod_id) (m1 : mod_tm) (m2 : mod_tm)

with expr_tm :=
  | e_var (x : expr_id)
  | e_lam (x : expr_id) (e : expr_tm)
  | e_app (e1 : expr_tm) (e2 : expr_tm)
  | e_link (m : mod_tm) (e : expr_tm)
.

Inductive value : expr_tm -> Prop :=
  | v_fn (x : expr_id) (e : expr_tm) : value (e_lam x e)
.

Scheme expr_ind_mut := Induction for expr_tm Sort Prop
with mod_ind_mut := Induction for mod_tm Sort Prop.
