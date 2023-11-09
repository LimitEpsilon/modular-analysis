From Signature Require Import Concrete.
Require Import String.
Open Scope string_scope.

#[local] Instance NatEq : Eq nat :=
{ eqb := Nat.eqb; eqb_eq := Nat.eqb_eq }.

#[local, refine] Instance NatOrder : TotalOrder nat :=
{ leb := Nat.leb }.
Proof.
  all:(intros; try (rewrite Nat.leb_le in *; nia)).
  des_goal; try reflexivity.
  assert ((t <=? t')%nat <> true). refl_bool. eauto.
  rewrite Nat.leb_le in *. nia.
Defined.

#[local, refine] Instance NatTime : @time nat _ _ :=
{ tick _ _ t _ _ := S t }.
Proof.
  all:(intros; eauto).
  red. s. split; try refl_bool; try rewrite Nat.leb_le;
  try rewrite Nat.eqb_eq; nia.
Defined.

Definition x : ID := "x".
Definition temp := e_lam x (e_var x).
Definition fact : ID := "fact".
Definition M : ID := "M".
Definition F : ID := "F".
Definition sx : st_ctx := st_binde x ([[||]]).
Definition sfact : st_ctx := st_binde fact ([[||]]).
Definition sM : st_ctx := st_bindm M sx ([[||]]).
Definition sF : st_ctx := st_bindm F sfact ([[||]]).

Definition e1 := m_app (e_lam x m_empty) temp sx.
Definition e2 := m_app (e_lam fact m_empty) temp sfact.
Definition e := 
  e_app 
    (e_app temp (e_app (e_link (m_var F) (e_var fact)) temp))
    (e_link (m_var M) (e_var x)).

Definition m1 := m_app (m_lam M sx m_empty) e1 sM.
Definition m2 := m_app (m_lam F sfact m_empty) e2 sF.

Definition linked1 := e_link (e_link m1 m2) e.
Definition linked2 := e_link m1 (e_link m2 e).

Definition ev1 := eval linked1 ([||]) [] 0 [] 6.
Definition ev2 := eval linked2 ([||]) [] 0 [] 7.

Definition res1 :=
  match ev1 with
  | Resolved V m t _ => Some (V, m, t)
  | _ => None
  end.

Definition res2 := 
  match ev2 with
  | Resolved V m t _ => Some (V, m, t)
  | _ => None
  end.

Notation "'⟨' e '❟' C '⟩'" := (Closure e C)
  (at level 60, right associativity).

Notation "'λ' x '｡' e" := (v_fn x e)
  (at level 60, right associativity).

Notation "'λ' M ':⟩' s '。' e" := (v_ft M s e)
  (at level 60, right associativity).

Notation "'⸨' x '❟' t '⸩' C" := (dy_binde x t C)
  (at level 60, right associativity).

Notation "'⟪' M '❟' C1 '⟫' C2" := (dy_bindm M C1 C2)
  (at level 60, right associativity).

Example eval_assoc : res1 = res2.
Proof.
  vm_compute. reflexivity.
Qed.

Example ev1_compute : ev1 = Error [].
Proof.
  vm_compute.
Abort.


