From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Basics Require Export tactics.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Types with decidable equality *)
Class Eq T : Type :=
{
  eqb : T -> T -> bool;
  eqb_eq : forall (t t' : T), eqb t t' = true <-> t = t';
}.

Lemma eqb_comm {T} `{Eq T} :
  forall x x', eqb x x' = eqb x' x.
Proof.
  intros.
  destruct (eqb x x') eqn:EQ; destruct (eqb x' x) eqn:EQ';
  try reflexivity;
  try rewrite eqb_eq in *; subst;
  try rewrite <- EQ; try rewrite <- EQ';
  match goal with
  | |- true = _ => symmetry
  | _ => idtac
  end; rewrite eqb_eq; eauto.
Qed.

Lemma eqb_neq {T} `{Eq T} : 
  forall x x', eqb x x' = false <-> x <> x'.
Proof.
  intros; split; intros contra.
  - red; intros RR. rewrite <- eqb_eq in *.
    rewrite RR in contra. inversion contra.
  - destruct (eqb x x') eqn:EQ; try reflexivity.
    exfalso. apply contra. rewrite <- eqb_eq. eauto.
Qed.

Lemma t_refl {T} `{Eq T} : forall t, eqb t t = true.
Proof. intros; apply eqb_eq; eauto. Qed.

Fixpoint Inb {T} `{Eq T} t (l : list T) :=
  match l with
  | [] => false
  | hd :: tl => eqb hd t || Inb t tl
  end.

Lemma Inb_eq {T} `{Eq T} :
  forall (l : list T) (t : T),
    Inb t l = true <-> In t l.
Proof.
  induction l; intros; simpl in *;
  split; intros EQ; try contradict.
  - repeat des_hyp;
    simpl in *; try (inversion EQ; fail);
    match goal with
    | _ => left; rewrite <- eqb_eq; eauto; fail
    | _ => right; rewrite <- IHl; eauto; fail
    end.
  - destruct EQ as [EQhd | EQtl].
    subst. rewrite t_refl. eauto.
    rewrite <- IHl in EQtl. rewrite EQtl.
    des_goal; eauto.
Qed.

Lemma Inb_neq {T} `{Eq T} :
  forall (l : list T) (t : T),
    Inb t l = false <-> ~ (In t l).
Proof.
  induction l; intros; simpl in *;
  split; intros NEQ; eauto.
  - red; intros EQ.
    destruct (eqb a t) eqn:NEQhd;
    destruct (Inb t l) eqn:NEQtl;
    try (inversion NEQ; fail).
    rewrite eqb_neq in NEQhd.
    rewrite IHl in NEQtl.
    destruct EQ as [EQhd | EQtl];
    match goal with
    | _ => apply NEQhd; eauto; fail
    | _ => apply NEQtl; eauto; fail
    end.
  - destruct (eqb a t) eqn:NEQhd;
    destruct (Inb t l) eqn:NEQtl; simpl;
    match goal with
    | _ => reflexivity; fail
    | [H : eqb _ _ = true |- _] =>
      rewrite eqb_eq in H
    | [H : Inb _ _ = true |- _] =>
      rewrite Inb_eq in H
    end;
    exfalso; apply NEQ; eauto.
Qed.

(* Total order *)
Class TotalOrder (T : Type) `{Eq T} : Type :=
{
  leb : T -> T -> bool;
  leb_refl : forall t, leb t t = true;
  leb_trans : forall t t' t'' (LE : leb t t' = true) (LE' : leb t' t'' = true), leb t t'' = true;
  leb_sym : forall t t' (LE : leb t t' = true) (LE' : leb t' t = true), t = t';
  leb_or : forall t t', leb t t' || leb t' t = true
}.

Definition lt {T} `{TotalOrder T} (t1 t2 : T) :=
  leb t1 t2 = true /\ eqb t1 t2 = false.

Notation "t1 '<<' t2" := (lt t1 t2) (at level 71).

