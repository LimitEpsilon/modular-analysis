From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From sflib Require Export sflib.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* First, some basic definitions*)
Ltac contradict :=
  let contra := fresh "contra" in
  assert False as contra; eauto 3; inversion contra.

Local Lemma __R__ : forall b, b = false <-> b <> true.
Proof.
  intros; split; intros; subst.
  red; intros contra. inversion contra.
  destruct b. contradict. eauto.
Qed.

Ltac refl_bool :=
  match goal with
  | |- _ = false => rewrite __R__; unfold "<>"
  | |- _ <> true => rewrite <- __R__
  | _ => idtac
  end.

Ltac rw :=
  match goal with
  | RR : _ |- _ => 
    lazymatch type of RR with
    | ?a = ?b =>
      lazymatch b with
      | context [a] => fail
      | _ => rewrite RR
      end
    | _ => rewrite RR
    end
  end.

Ltac rrw :=
  match goal with
  | RR : _ |- _ =>
    lazymatch type of RR with
    | ?a = ?b =>
      lazymatch a with
      | context [b] => fail
      | _ => rewrite <- RR
      end
    | _ => rewrite <- RR
    end
  end.

Ltac des_hyp :=
  let DES := fresh "HDES" in
  match goal with
  | [H : context [?E || _] |- _] =>
    destruct E eqn:DES; simpl in H;
    try (inversion H; fail)
  | [H : context [?E && _] |- _] =>
    destruct E eqn:DES; simpl in H;
    try (inversion H; fail)
  | [H : context [match ?E with | _ => _ end] |- _] =>
    destruct E eqn:DES; simpl in H;
    try (inversion H; fail)
  end.

Ltac des_goal :=
  let DES := fresh "GDES" in
  match goal with
  | [|- context [?E || _]] =>
    destruct E eqn:DES; simpl
  | [|- context [?E && _]] =>
    destruct E eqn:DES; simpl
  | [|- context [match ?E with | _ => _ end]] =>
    destruct E eqn:DES; simpl
  end.

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

(** Syntax of our language *)
Definition ID := nat.

Definition eqb_ID := Nat.eqb.

Definition eqb_ID_eq := Nat.eqb_eq.

#[export] Instance EqID : Eq ID := { eqb:= eqb_ID; eqb_eq := eqb_ID_eq; }.

Definition eqb_ID_neq := Nat.eqb_neq.

Lemma ID_refl : forall x, eqb_ID x x = true.
Proof. intros; apply eqb_ID_eq; eauto. Qed.

Inductive tm :=
  | e_var (x : ID)
  | e_lam (x : ID) (e : tm)
  | e_app (e1 : tm) (e2 : tm)
  | e_link (m : tm) (e : tm)
  | m_empty
  | m_var (M : ID)
  | m_lete (x : ID) (e : tm) (m : tm)
  | m_letm (M : ID) (m1 : tm) (m2 : tm)
.

Fixpoint eq_tm e e' :=
  match e, e' with
  | e_var x, e_var x' => eqb_ID x x'
  | e_lam x e, e_lam x' e' => eqb_ID x x' && eq_tm e e'
  | e_app e1 e2, e_app e1' e2' => eq_tm e1 e1' && eq_tm e2 e2'
  | e_link m e, e_link m' e' => eq_tm m m' && eq_tm e e'
  | m_empty, m_empty => true
  | m_var M, m_var M' => eqb_ID M M'
  | m_lete x e m, m_lete x' e' m' => eqb_ID x x' && eq_tm e e' && eq_tm m m'
  | m_letm M m1 m2, m_letm M' m1' m2' => eqb_ID M M' && eq_tm m1 m1' && eq_tm m2 m2'
  | _, _ => false
  end.

Lemma eq_tm_eq : forall e e', eq_tm e e' = true <-> e = e'.
Proof.
  induction e; intros; split; intros EQ; simpl in *;
  destruct e'; try (inversion EQ; fail);
  repeat des_hyp;
  repeat match goal with
  | [H : eqb_ID _ _ = true |- _] =>
    rewrite eqb_ID_eq in H
  | [H : eq_tm _ _ = true |- _] =>
    repeat match goal with
    | [RR : context [eq_tm _ _ = true <-> _] |- _] =>
      rewrite RR in H
    end
  | _ => idtac
  end; subst; try reflexivity;
  inversion EQ; subst;
  try rewrite ID_refl; simpl; try reflexivity;
  repeat match goal with
  | [H : context [eq_tm ?e _ = _] |- _] =>
    match goal with
    | [_ : eq_tm e e = true |- _] => fail
    | _ =>
      let RR := fresh "RR" in
      assert (eq_tm e e = true) as RR;
      try apply H; eauto; rewrite RR
    end
  | _ => fail
  end.
Qed.

#[export] Instance Eqtm : Eq tm := { eqb := eq_tm; eqb_eq := eq_tm_eq; }.

(** Statics *)
Inductive value :=
  | v_fn (x : ID) (e : tm)
.

Inductive st_ctx :=
  | st_hole
  | st_binde (x : ID) (C : st_ctx)
  | st_bindm (M : ID) (CM : st_ctx) (C : st_ctx)
.

Notation "'[[|' '|]]'" := (st_hole) (at level 99).

Fixpoint st_ctx_M (C : st_ctx) (M : ID) :=
  match C with
  | [[||]] => None
  | st_binde _ C' => st_ctx_M C' M
  | st_bindm M' CM' C' =>
    if eqb_ID M M' then Some CM' else st_ctx_M C' M
  end.

(* collect all signatures reachable from the current configuration *)
Fixpoint collect_ctx C e :=
  match e with
  | e_var x => (None, [C])
  | e_lam x e' => 
    let ctx_body := snd (collect_ctx (st_binde x C) e') in
    (None, C :: ctx_body)
  | e_app e1 e2 =>
    let ctxs1 := snd (collect_ctx C e1) in
    let ctxs2 := snd (collect_ctx C e2) in
    (None, ctxs1 ++ ctxs2)
  | e_link m e' =>
    match collect_ctx C m with
    | (Some C_m, ctxs_m) => 
      let (ctx_o, ctxs_e) := collect_ctx C_m e' in
      (ctx_o, ctxs_m ++ ctxs_e)
    | (None, ctxs_m) => (None, ctxs_m)
    end
  | m_empty => (Some C, [C])
  | m_var M =>
    match st_ctx_M C M with
    | Some C_M => (Some C_M, [C_M; C])
    | None => (None, [C])
    end
  | m_lete x e m' =>
    let ctxs_e := snd (collect_ctx C e) in
    let (ctx_o, ctxs_m) := collect_ctx (st_binde x C) m' in
    (ctx_o, ctxs_e ++ ctxs_m)
  | m_letm M m1 m2 =>
    match collect_ctx C m1 with
    | (Some C_M, ctxs_m1) => 
      let (ctx_o, ctxs_m2) := collect_ctx (st_bindm M C_M C) m2 in
      (ctx_o, ctxs_m1 ++ ctxs_m2)
    | (None, ctxs_m1) => (None, ctxs_m1)
    end
  end.

Lemma collect_ctx_refl : forall e C, In C (snd (collect_ctx C e)).
Proof.
  induction e; intros; simpl; eauto;
  repeat des_goal;
  try apply in_app_iff; first [left; eauto; fail | right; eauto; fail | eauto];
  repeat match goal with
  | [H : forall _ : st_ctx, In _ (snd (collect_ctx _ ?e)) |- _] =>
    match goal with
    | [RR : collect_ctx ?C e = _ |- _] =>
      specialize (H C); rewrite RR in H
    end
  end; simpl in *; eauto.
Qed.

(** Dynamics *)
Inductive dy_ctx T :=
  | dy_hole
  | dy_binde (x : ID) (tx : T) (C : dy_ctx T)
  | dy_bindm (M : ID) (CM : dy_ctx T) (C : dy_ctx T)
.

Arguments dy_hole {T}.
Arguments dy_binde {T}.
Arguments dy_bindm {T}.

Notation "'[|' '|]'" := (dy_hole) (at level 99).

(* ctx append *)
Fixpoint capp {T} (C C' : dy_ctx T) :=
  match C with
  | [||] => C'
  | dy_binde x tx C =>
    dy_binde x tx (capp C C')
  | dy_bindm M CM C =>
    dy_bindm M CM (capp C C')
  end.

Notation "C1 '+++' C2" := (capp C1 C2)
  (right associativity, at level 60).

Lemma capp_assoc {T} : forall (c1 c2 c3 : dy_ctx T),
  c1 +++ c2 +++ c3 = (c1 +++ c2) +++ c3.
Proof.
  induction c1; ii; ss; rw; eauto.
Qed.

(* Auxiliary operators *)
Fixpoint addr_x {T} (C : dy_ctx T) (x : ID) :=
  match C with
  | [||] => None
  | dy_binde x' tx' C' =>
    if eqb_ID x x' then (Some tx') else addr_x C' x
  | dy_bindm _ _ C' => addr_x C' x
  end.

Fixpoint ctx_M {T} (C : dy_ctx T) (M : ID) :=
  match C with
  | [||] => None
  | dy_binde _ _ C' => ctx_M C' M
  | dy_bindm M' CM' C' =>
    if eqb_ID M M' then Some CM' else ctx_M C' M
  end.

Lemma capp_addr_x {T} : forall (C1 C2 : dy_ctx T) x,
  addr_x (C1 +++ C2) x =
  match addr_x C1 x with
  | Some t => Some t
  | None => addr_x C2 x
  end.
Proof.
  induction C1; ii; ss. des_goal; eauto.
Qed.

Lemma capp_ctx_M {T} : forall (C1 C2 : dy_ctx T) M,
  ctx_M (C1 +++ C2) M =
  match ctx_M C1 M with
  | Some CM => Some CM
  | None => ctx_M C2 M
  end.
Proof.
  induction C1; ii; ss. des_goal; eauto.
Qed.

(* Auxiliary definition to aid proofs *)
Fixpoint st_level (C : st_ctx) :=
  match C with
  | [[||]] => 0
  | st_binde _ C' => S (st_level C')
  | st_bindm _ C' C'' => S (Nat.max (st_level C') (st_level C''))
  end.

Fixpoint dy_level {T} (C : dy_ctx T) :=
  match C with
  | [||] => 0
  | dy_binde _ _ C' => S (dy_level C')
  | dy_bindm _ C' C'' => S (Nat.max (dy_level C') (dy_level C''))
  end.

Fixpoint dy_to_st {T} (C : dy_ctx T) :=
  match C with
  | [||] => [[||]]
  | dy_binde x _ C' => st_binde x (dy_to_st C')
  | dy_bindm M CM C' => st_bindm M (dy_to_st CM) (dy_to_st C')
  end.

Lemma st_dy_level_eq {T} :
  forall (C : dy_ctx T), dy_level C = st_level (dy_to_st C).
Proof.
  induction C; simpl; eauto.
Qed.

Lemma mod_is_static_none : forall {T} (dC : dy_ctx T) (M : ID),
  (ctx_M dC M = None <-> st_ctx_M (dy_to_st dC) M = None).
Proof. 
  intros. repeat split; induction dC; simpl; eauto;
  repeat des_goal; eauto;
  match goal with
  | _ => let H := fresh "H" in intro H; inversion H
  | _ => idtac
  end.
Qed.

Lemma mod_is_static_some : forall {T} (dC : dy_ctx T) (M : ID),
  (forall v, ctx_M dC M = Some v -> st_ctx_M (dy_to_st dC) M = Some (dy_to_st v)) /\
  (forall v, st_ctx_M (dy_to_st dC) M = Some v -> exists dv, dy_to_st dv = v /\ ctx_M dC M = Some dv).
Proof.
  intros; split; induction dC; simpl; intros; eauto; clarify;
  repeat des_goal; clarify; eauto.
Qed.

(* More semantic domains *)
Inductive expr_value T :=
  | Closure (x : ID) (e : tm) (C : dy_ctx T)
.

Arguments Closure {T}.

Inductive dy_value T :=
  | EVal (ev : expr_value T)
  | MVal (mv : dy_ctx T)
.

Arguments EVal {T}.
Arguments MVal {T}.

Definition memory T := list (T * expr_value T).

Definition update_m {T X} m (t : T) (x : X) := (t, x) :: m.

Definition empty_mem {T} : list T := [].

Notation "p '!->' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Inductive config T :=
  | Cf (e : tm) (C : dy_ctx T) (m : memory T) (t : T)
  | Rs (V : dy_value T) (m : memory T) (t : T)
.

Arguments Cf {T}.
Arguments Rs {T}.

(* memory reads *)
Fixpoint read {T} `{Eq T} (m : memory T) (t : T) :=
  match m with
  | [] => None
  | (t', v) :: m' =>
    if eqb t' t then Some v else read m' t
  end.

Definition same {T} `{Eq T} (m : memory T) (m' : memory T) :=
  forall t v, Some v = read m t <-> Some v = read m' t.

Fixpoint aread {T} `{Eq T} (m : memory T) (t : T) :=
  match m with
  | [] => []
  | (t', v) :: m' =>
    let tl := aread m' t in
    if eqb t' t then v :: tl else tl
  end.

Definition asame {T} `{Eq T} (m : memory T) (m' : memory T) :=
  forall t v, In v (aread m t) <-> In v (aread m' t).

(* Definitions for the (finite) supports *)
Fixpoint supp_C {T} (C : dy_ctx T) (t : T) :=
  match C with
  | [||] => False
  | dy_binde _ t' C' => t = t' \/ supp_C C' t
  | dy_bindm _ C' C'' => supp_C C' t \/ supp_C C'' t
  end.

Definition supp_v {T} (v : expr_value T) :=
  match v with
  | Closure _ _ C => supp_C C
  end.

Definition supp_V {T} (V : dy_value T) :=
  match V with
  | EVal ev => supp_v ev
  | MVal mv => supp_C mv
  end.

Fixpoint supp_m {T} (m : memory T) (t : T) :=
  match m with
  | [] => False
  | (t', v) :: m' =>
    t = t' \/ supp_v v t \/ supp_m m' t
  end.

Definition supp_ρ {T} (ρ : config T) (t : T) :=
  match ρ with
  | Cf _ C m time => supp_C C t \/ supp_m m t \/ time = t
  | Rs V m time => supp_V V t \/ supp_m m t \/ time = t
  end.

(** Graph isomorphism between (C, m) and (C', m') *)
Inductive root T :=
  | Ptr (t : T)
  | Ctx (C : dy_ctx T)
.

Arguments Ptr {T}.
Arguments Ctx {T}.

Inductive path T :=
  | Pnil
  | Px (x : ID) (tx : T) (tl : path T)
  | PM (M : ID) (tl : path T)
  | Pv (v : value) (tl : path T)
.

Arguments Pnil {T}.
Arguments Px {T}.
Arguments PM {T}.
Arguments Pv {T}.

Fixpoint Inp {T} (t : T) (p : path T) :=
  match p with
  | Pnil => False
  | Px x tx p =>
    t = tx \/ Inp t p
  | PM M p => Inp t p
  | Pv v p => Inp t p
  end.

Fixpoint Inpb {T} `{Eq T} (t : T) (p : path T) :=
  match p with
  | Pnil => false
  | Px x tx p =>
    eqb t tx || Inpb t p
  | PM M p => Inpb t p
  | Pv v p => Inpb t p
  end.

Lemma Inpb_In {T} `{Eq T} :
  forall p t,
    Inpb t p = true <-> Inp t p.
Proof.
  induction p; ii; ss;
  split; intros IN;
  des; repeat des_hyp; clarify.
  rewrite eqb_eq in *. clarify. eauto.
  rewrite IHp in IN. eauto.
  rewrite t_refl. eauto.
  des_goal. eauto. rewrite IHp. eauto.
Qed.

Lemma Inpb_nIn {T} `{Eq T} :
  forall p t,
    Inpb t p = false <-> ~ Inp t p.
Proof.
  ii. destruct (Inpb t p) eqn:CASE.
  split; ii; clarify.
  rewrite Inpb_In in *. contradict.
  split; ii; clarify.
  rewrite <- Inpb_In in *. rewrite CASE in *. clarify.
Qed.

(* path map *)
Fixpoint pmap {T T'} (f : T -> T') (p : path T) :=
  match p with
  | Pnil => Pnil
  | Px x tx tl => Px x (f tx) (pmap f tl)
  | PM M tl => PM M (pmap f tl)
  | Pv v tl => Pv v (pmap f tl)
  end.

Fixpoint valid_path {T} `{Eq T}
  (r : root T) (m : memory T) (p : path T) :=
  match p, r with
  | Pnil, _ => True
  | Px x tx tl, Ctx C =>
    match addr_x C x with
    | Some t => 
      tx = t /\ valid_path (Ptr tx) m tl
    | _ => False
    end
  | PM M tl, Ctx C =>
    match ctx_M C M with
    | Some CM => valid_path (Ctx CM) m tl
    | _ => False
    end
  | Pv v tl, Ptr t =>
    exists ev, Some ev = read m t /\
    match ev with
    | Closure x e Cv =>
      v = v_fn x e /\ valid_path (Ctx Cv) m tl
    end
  | _, _ => False
  end.

Definition reachable {T} `{Eq T} (r : root T) (m : memory T) (t : T) :=
  exists p, valid_path r m p /\ Inp t p.

Definition iso {T T'} `{Eq T} `{Eq T'}
  (r : root T) (m : memory T) (r' : root T') (m' : memory T') f f' :=
  (forall p (VALp : valid_path r m p),
    let p' := pmap f p in
    valid_path r' m' p' /\ pmap f' p' = p) /\
  (forall p' (VALp' : valid_path r' m' p'),
    let p := pmap f' p' in
    valid_path r m p /\ pmap f p = p').

Definition equiv {T T'} `{Eq T} `{Eq T'}
  (V : dy_value T) (m : memory T) f (V' : dy_value T') (m' : memory T') f' :=
  match V, V' with
  | MVal C, MVal C' =>
    iso (Ctx C) m (Ctx C') m' f f'
  | EVal (Closure x e C), EVal (Closure x' e' C') =>
    x = x' /\ e = e' /\
    iso (Ctx C) m (Ctx C') m' f f'
  | _, _ => False
  end.

Notation "'<|' V1 m1 f1 '≃' V2 m2 f2 '|>'" :=
  (equiv V1 m1 f1 V2 m2 f2)
  (at level 10, V1 at next level, m1 at next level, V2 at next level, m2 at next level).

Fixpoint avalid_path {T} `{Eq T}
  (r : root T) (m : memory T) (p : path T) :=
  match p, r with
  | Pnil, _ => True
  | Px x tx tl, Ctx C =>
    match addr_x C x with
    | Some t =>
      tx = t /\ avalid_path (Ptr tx) m tl
    | _ => False
    end
  | PM M tl, Ctx C =>
    match ctx_M C M with
    | Some CM => avalid_path (Ctx CM) m tl
    | _ => False
    end
  | Pv v tl, Ptr t =>
    exists ev, In ev (aread m t) /\
    match ev with
    | Closure x e Cv =>
      v = v_fn x e /\ avalid_path (Ctx Cv) m tl
    end
  | _, _ => False
  end.
  
Definition areachable {T} `{Eq T} (r : root T) (m : memory T) (t : T) :=
  exists p, avalid_path r m p /\ Inp t p.

(* weak equivalence *)
Definition aiso {T T'} `{Eq T} `{Eq T'}
  (r : root T) (m : memory T) (r' : root T') (m' : memory T') f f' :=
  (forall p (VALp : avalid_path r m p),
    let p' := pmap f p in
    avalid_path r' m' p' /\ pmap f' p' = p) /\
  (forall p' (VALp' : avalid_path r' m' p'),
    let p := pmap f' p' in
    avalid_path r m p /\ pmap f p = p').

(* equivalence *)
Definition aIso {T T'} `{Eq T} `{Eq T'}
  (r : root T) (m : memory T) (r' : root T') (m' : memory T') f f' :=
  aiso r m r' m' f f' /\
  (forall t v (REACH : areachable r m t) (IN : In v (aread m t)),
    exists v', In v' (aread m' (f t)) /\
      match v, v' with
      | Closure x e C, Closure x' e' C' =>
        x = x' /\ e = e' /\ aiso (Ctx C) [] (Ctx C') [] f f'
      end) /\
  (forall t' v' (REACH : areachable r' m' t') (IN : In v' (aread m' t')),
    exists v, In v (aread m (f' t')) /\
      match v, v' with
      | Closure x e C, Closure x' e' C' =>
        x = x' /\ e = e' /\ aiso (Ctx C) [] (Ctx C') [] f f'
      end)
.
  
Definition aequiv {T T'} `{Eq T} `{Eq T'}
  (V : dy_value T) (m : memory T) (V' : dy_value T') (m' : memory T') :=
  match V, V' with
  | MVal C, MVal C' =>
    exists f f', aIso (Ctx C) m (Ctx C') m' f f'
  | EVal (Closure x e C), EVal (Closure x' e' C') =>
    x = x' /\ e = e' /\
    exists f f', aIso (Ctx C) m (Ctx C') m' f f'
  | _, _ => False
  end.

Notation "'<|' V1 m1 '≃#' V2 m2 '|>'" :=
  (aequiv V1 m1 V2 m2)
  (at level 10, V1 at next level, m1 at next level, V2 at next level, m2 at next level).

(* Translation of timestamps *)
Fixpoint trans_C {T T'} (α : T -> T') (C : dy_ctx T) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' => dy_binde x (α t) (trans_C α C')
  | dy_bindm M CM C' => dy_bindm M (trans_C α CM) (trans_C α C')
  end.

Definition trans_v {T T'} (α : T -> T') (v : expr_value T) :=
  match v with
  | Closure x e C => Closure x e (trans_C α C)
  end.

Definition trans_V {T T'} (α : T -> T') (V : dy_value T) :=
  match V with
  | EVal v => EVal (trans_v α v)
  | MVal C => MVal (trans_C α C)
  end.

Fixpoint trans_m_aux {CT AT} `{Eq CT} (α : CT -> AT) (m : memory CT) (seen : list CT) :=
  match m with
  | [] => []
  | (t, v) :: m' =>
    if Inb t seen then trans_m_aux α m' seen else
    (α t, trans_v α v) :: trans_m_aux α m' (t :: seen)
  end.

Definition trans_m {CT AT} `{Eq CT} (α : CT -> AT) (m : memory CT) : memory AT :=
  trans_m_aux α m [].

Definition trans_ρ {CT AT} `{Eq CT} (α : CT -> AT) (ρ : config CT) :=
  match ρ with
  | Cf e C m t => Cf e (trans_C α C) (trans_m α m) (α t)
  | Rs V m t => Rs (trans_V α V) (trans_m α m) (α t)
  end.

(* Lemmas on translation *)
Lemma trans_C_app {T TT} (α : T -> TT) :
  forall (C1 C2 : dy_ctx T),
    trans_C α (C1 +++ C2) = trans_C α C1 +++ trans_C α C2.
Proof.
  induction C1; ii; ss; rw; exact eq_refl.
Qed.

Lemma aread_in {T} `{Eq T} :
  forall (m : memory T) t v, In v (aread m t) <-> In (t, v) m.
Proof.
  induction m; intros; split; intros IN; simpl in *;
  repeat des_hyp;
  repeat des_goal;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H
  end; clarify;
  try rewrite eqb_eq in *;
  try rewrite IHm in *;
  clarify; eauto.
  rewrite eqb_neq in *. contradict.
Qed.

Lemma trans_m_aux_read {CT AT} `{Eq CT} `{Eq AT} (α : CT -> AT) 
  (INJ : forall x y, α x = α y -> x = y) :
  forall m abs_t abs_v seen,
  Some abs_v = read (trans_m_aux α m seen) abs_t <->
  (exists t v, ~ In t seen /\ Some v = read m t /\ α t = abs_t /\ trans_v α v = abs_v).
Proof.
  induction m; intros; split; intros IN; simpl in *;
  repeat match goal with
  | H : exists _, _ |- _ => destruct H as [t [v ?]]
  | H : _ /\ _ |- _ => destruct H
  end; clarify;
  repeat des_goal; repeat des_hyp;
  try rewrite eqb_eq in *;
  match goal with
  | H : _ |- _ => apply INJ in H
  | _ => idtac
  end; clarify;
  try rewrite t_refl in *;
  try rewrite Inb_eq in *;
  try rewrite Inb_neq in *; clarify. try contradict; eauto.
  - rewrite IHm in IN.
    destruct IN as [t [v [IN [? [? ?]]]]]; clarify.
    exists t. exists v. repeat split; try assumption.
    des_goal; try rewrite eqb_eq in *; subst; try contradict; eauto.
  - exists c. exists e. rewrite t_refl. eauto.
  - rewrite IHm in IN.
    destruct IN as [t [v [IN [? [? ?]]]]]; clarify. simpl in IN.
    exists t. exists v. repeat split; eauto.
    des_goal; try rewrite eqb_eq in *; subst; try contradict; eauto.
  - rewrite IHm. exists t. exists v. eauto.
  - rewrite IHm. exists t. exists v.
    rewrite <- Inb_neq in *. simpl. repeat rw. eauto.
Qed.

Lemma trans_m_aux_aread {CT AT} `{Eq CT} (α : CT -> AT) :
  forall m abs_t abs_v seen,
  In (abs_t, abs_v) (trans_m_aux α m seen) <->
  (exists t v, ~ In t seen /\ Some v = read m t /\ α t = abs_t /\ trans_v α v = abs_v).
Proof.
  induction m; intros; split; intros IN; simpl in *;
  repeat match goal with
  | H : exists _, _ |- _ => destruct H as [t [v ?]]
  | H : _ /\ _ |- _ => destruct H
  end; clarify;
  repeat des_goal; repeat des_hyp;
  try rewrite eqb_eq in *;
  try rewrite t_refl in *; clarify;
  try rewrite Inb_eq in *; try contradict; eauto.
  - rewrite IHm in IN.
    destruct IN as [t [v [IN [READ [TRANSt TRANSv]]]]].
    exists t. exists v. repeat split; try assumption.
    des_goal; try rewrite eqb_eq in *; subst; try contradict; eauto.
  - destruct IN as [IN|IN].
    clarify. exists c. exists e. rewrite t_refl. rewrite <- Inb_neq. eauto.
    rewrite IHm in IN.
    destruct IN as [t [v [IN [READ [TRANSt TRANSv]]]]].
    exists t. exists v. rewrite <- Inb_neq in *. simpl in *.
    repeat des_hyp; clarify; eauto.
  - rewrite IHm. exists t. exists v. eauto.
  - right. rewrite IHm. exists t. exists v.
    rewrite <- Inb_neq in *. simpl.
    repeat des_hyp; clarify; eauto.
Qed.

Lemma trans_m_read {CT AT} `{Eq CT} `{Eq AT} (α : CT -> AT) 
  (INJ : forall x y, α x = α y -> x = y) :
  forall (m : memory CT) t v,
  Some v = read (trans_m α m) t <->
  (exists t' v', Some v' = read m t' /\ α t' = t /\ trans_v α v' = v).
Proof.
  induction m; intros; split; intros IN; simpl in *;
  repeat match goal with
  | H : exists _, _ |- _ => destruct H as [t [v ?]]
  | H : _ /\ _ |- _ => destruct H
  end; clarify;
  repeat des_goal; repeat des_hyp;
  try rewrite eqb_eq in *;
  match goal with
  | H : _ |- _ => apply INJ in H
  | _ => idtac
  end; clarify;
  try rewrite t_refl in *;
  try rewrite Inb_eq in *;
  try rewrite Inb_neq in *; clarify. try contradict; eauto.
  - destruct IN as [? [? [? ?]]]; clarify.
  - unfold trans_m in IN. simpl in IN.
    des_hyp. exists c. exists e. rewrite t_refl. rewrite eqb_eq in *.
    clarify. eauto.
    rewrite trans_m_aux_read in IN; eauto.
    destruct IN as [t' [v' [IN [READ [TRANSt TRANSv]]]]].
    exists t'. exists v'. repeat split; eauto.
    des_goal; try rewrite eqb_eq in *; subst; eauto.
    exfalso. apply IN. simpl. eauto.
  - unfold trans_m. simpl. 
    des_goal; try rewrite eqb_eq in *; subst;
    try rewrite trans_m_aux_read; eauto;
    destruct IN as [t' [v' [READ [TRANSt TRANSv]]]];
    try apply INJ in TRANSt; subst; try rewrite t_refl in *. clarify.
    exists t'. exists v'. 
    des_hyp; 
    try rewrite eqb_eq in *; clarify;
    try rewrite t_refl in *; clarify;
    repeat rewrite eqb_neq in *.
    simpl. repeat split; eauto.
    red; intros contra; destruct contra; eauto.
Qed.

Lemma trans_m_aread {CT AT} `{Eq CT} `{Eq AT} (α : CT -> AT) :
  forall (m : memory CT) t v,
  In v (aread (trans_m α m) t) <->
  (exists t' v', Some v' = read m t' /\ α t' = t /\ trans_v α v' = v).
Proof.
  induction m; intros; split; intros IN;
  try (simpl in IN; contradict);
  try (destruct IN as [t' [v' [? [? ?]]]]; clarify);
  unfold trans_m in *; simpl in *; repeat des_hyp; clarify;
  match goal with
  | _ => simpl in *; rewrite t_refl in *; clarify
  | _ => idtac
  end;
  try rewrite eqb_eq in *; 
  try rewrite aread_in in *;
  subst; simpl; eauto.
  - destruct IN as [IN|IN].
    subst. exists c. exists e. rewrite t_refl; eauto.
    rewrite trans_m_aux_aread in IN.
    destruct IN as [t [v' [IN [? [? ?]]]]].
    rewrite <- Inb_neq in IN. simpl in IN.
    des_hyp.
    exists t. exists v'.
    repeat rw. eauto.
  - rewrite trans_m_aux_aread in IN.
    destruct IN as [t' [v' [IN [? [? ?]]]]].
    rewrite <- Inb_neq in IN. simpl in IN.
    des_hyp.
    exists t'. exists v'.
    repeat rw. eauto.
  - right. rewrite trans_m_aux_aread.
    exists t'. exists v'.
    rewrite <- Inb_neq; simpl.
    repeat rw. eauto.
Qed.

Lemma trans_m_same {CT AT} `{Eq CT} `{Eq AT} (α : CT -> AT)
  (INJ : forall x y, α x = α y -> x = y) :
  forall (m m' : memory CT) (EQ : same m m'),
    same (trans_m α m) (trans_m α m').
Proof.
  induction m; intros; unfold same in *;
  intros; split; intros IN; simpl in *;
  clarify.
  - rewrite trans_m_read in IN; eauto.
    destruct IN as [t' [v' [READ [TRANSt TRANSv]]]].
    rewrite <- EQ in *. clarify.
  - rewrite trans_m_read in *; eauto.
    destruct IN as [t' [v' [READ [TRANSt TRANSv]]]].
    simpl in *. repeat des_hyp; try rewrite eqb_eq in *; clarify.
    exists t'. exists e. repeat split; eauto.
    rewrite <- EQ. rewrite t_refl. eauto.
    exists t'. exists v'. repeat split; eauto.
    rewrite <- EQ. repeat rw. eauto.
  - rewrite trans_m_read in *; eauto.
    destruct IN as [t' [v' [READ [TRANSt TRANSv]]]].
    simpl in *. repeat des_goal; try rewrite eqb_eq in *; clarify.
    exists t'. exists v'. repeat split; eauto.
    rewrite EQ. eauto.
Qed.

Lemma trans_m_asame {CT AT} `{Eq CT} `{Eq AT} (α : CT -> AT) :
  forall (m m' : memory CT) (EQ : same m m'),
    asame (trans_m α m) (trans_m α m').
Proof.
  induction m; intros; unfold same in EQ;
  unfold asame; intros; split; intros IN; simpl in *;
  clarify.
  - rewrite trans_m_aread in IN.
    destruct IN as [? [? [contra [? ?]]]].
    rewrite <- EQ in contra. inversion contra.
  - rewrite trans_m_aread in *.
    destruct IN as [t' [v' [? [? ?]]]].
    simpl in *. repeat des_hyp; clarify.
    exists t'. exists e. repeat split; try reflexivity.
    rewrite <- EQ. repeat rw. eauto.
    exists t'. exists v'. repeat split; try reflexivity.
    rewrite <- EQ. repeat rw. eauto.
  - rewrite trans_m_aread in *.
    destruct IN as [t' [v' [READ [? ?]]]].
    simpl in *. rewrite <- EQ in READ.
    exists t'. exists v'. eauto.
Qed.

Lemma trans_C_addr :
  forall {CT AT} (α : CT -> AT) C x,
    addr_x (trans_C α C) x = 
      match addr_x C x with 
      | None => None 
      | Some addr => Some (α addr)
      end.
Proof.
  induction C; eauto.
  intros. simpl.
  des_goal; eauto.
Qed.

Lemma trans_C_ctx_M :
  forall {CT AT} C (α : CT -> AT) M,
    ctx_M (trans_C α C) M =
      match ctx_M C M with
      | None => None
      | Some CM => Some (trans_C α CM)
      end.
Proof.
  induction C; ii; ss.
  des_goal; eauto.
Qed.

Fixpoint eq_C {T} eqb (C1 C2 : dy_ctx T) :=
  match C1, C2 with
  | [||], [||] => true
  | dy_binde x1 t1 C1', dy_binde x2 t2 C2' =>
    eqb_ID x1 x2 && eqb t1 t2 && eq_C eqb C1' C2'
  | dy_bindm M1 C1' C1'', dy_bindm M2 C2' C2'' =>
    eqb_ID M1 M2 && eq_C eqb C1' C2' && eq_C eqb C1'' C2''
  | _, _ => false
  end.

Lemma ctx_refl {T} eqb (t_refl : forall t, eqb t t = true) : 
  forall (C : dy_ctx T), eq_C eqb C C = true.
Proof.
  induction C; simpl; try rewrite ID_refl; try rewrite t_refl;
  try rewrite IHC; try rewrite IHC1; try rewrite IHC2; eauto.
Qed.

Definition eqb_C {T} `{Eq T} := eq_C eqb.

Lemma eqb_C_eq {T} `{Eq T} :
  forall (C C' : dy_ctx T),
  eqb_C C C' = true <-> C = C'.
Proof.
  induction C; intros; unfold eqb_C in *;
  simpl; repeat des_goal; repeat des_hyp;
  split; intros EQ; clarify;
  try rewrite eqb_ID_eq in *; try rewrite eqb_eq in *;
  try rewrite IHC in *; try rewrite IHC1 in *; try rewrite IHC2 in *;
  subst;
  match goal with
  | _ => reflexivity
  | _ => rewrite eqb_neq in *; contradict
  | _ => rewrite eqb_ID_neq in *; contradict
  | H : eq_C eqb ?C ?C = false |- _ =>
    let contra := fresh "contra" in
    assert (C = C) as contra; try reflexivity;
    match goal with
    | RR : context[C = _] |- _ => 
      rewrite <- RR in *; rewrite contra in *; clarify
    end
  end.
Qed.

#[export] Instance EqC {T} `{Eq T} : `{Eq (dy_ctx T)} := 
  { eqb := eqb_C; eqb_eq := eqb_C_eq; }.

Definition eq_root {T} `{Eq T} (r1 r2 : root T) :=
  match r1, r2 with
  | Ptr t1, Ptr t2 => eqb t1 t2
  | Ctx C1, Ctx C2 => eqb C1 C2
  | _, _ => false
  end.

Lemma eq_root_eq {T} `{Eq T} :
  forall (r r' : root T),
  eq_root r r' = true <-> r = r'.
Proof.
  intros; split; intros EQ; unfold eq_root in *;
  repeat des_goal; repeat des_hyp;
  try rewrite eqb_eq in *;
  try rewrite eqb_C_eq in *; 
  clarify.
Qed.

#[export] Instance EqRoot {T} `{Eq T} : `{Eq (root T)} :=
  { eqb := eq_root; eqb_eq := eq_root_eq; }.

Lemma eq_C_st_eq {T} eqb (C1 C2 : dy_ctx T) :
  eq_C eqb C1 C2 = true -> dy_to_st C1 = dy_to_st C2.
Proof.
  intros EQ. revert C2 EQ.
  induction C1; induction C2; intros; simpl; eauto; try (inversion EQ; fail);
  simpl in EQ; repeat des_hyp;
  repeat match goal with
  | [H : context [eq_C eqb _ _ = true -> _] |- _] =>
    match goal with
    | [RR : eq_C eqb _ _ = true |- _] =>
      apply H in RR; rewrite RR
    end
  | [RR : eqb_ID _ _ = true |- _] =>
    rewrite eqb_ID_eq in RR; rewrite RR
  end; eauto.
Qed.

Lemma eq_C_level_eq {T} eqb (C1 C2 : dy_ctx T) :
  eq_C eqb C1 C2 = true -> dy_level C1 = dy_level C2.
Proof.
  intros EQ.
  repeat rewrite st_dy_level_eq.
  erewrite eq_C_st_eq; eauto.
Qed.

(* injection, deletion *)

Fixpoint inject {T} (Cout Cin : dy_ctx T) :=
  match Cin with
  | [||] => Cout
  | dy_binde x t C' =>
    dy_binde x t (inject Cout C')
  | dy_bindm M C' C'' =>
    dy_bindm M (inject Cout C') (inject Cout C'')
  end.

Fixpoint delete {T} eqb (Cout Cin : dy_ctx T) :=
  if eq_C eqb Cout Cin then [||]
  else match Cin with
  | [||] => [||]
  | dy_binde x t Cin' =>
    dy_binde x t (delete eqb Cout Cin')
  | dy_bindm M Cin' Cin'' =>
    dy_bindm M (delete eqb Cout Cin') (delete eqb Cout Cin'')
  end.

Lemma inject_level_inc {T} (Cout Cin : dy_ctx T) :
  dy_level Cout <= dy_level (inject Cout Cin).
Proof.
  induction Cin; intros; simpl; nia.
Qed.

Lemma delete_inject_eq {T} eqb (t_refl : forall t, eqb t t = true) :
  forall (Cout Cin : dy_ctx T),
    delete eqb Cout (inject Cout Cin) = Cin.
Proof.
  intros. revert Cout. induction Cin; simpl;
  match goal with
  | |- context [if _ then _ else _] =>
    (* inductive case *)
    intros; try rewrite IHCin; try rewrite IHCin1; try rewrite IHCin2;
    des_goal; eauto;
    (* search for a contradiction *)
    match goal with
    | [H : eq_C _ _ _ = true |- _] =>
      apply eq_C_level_eq in H; simpl in H
    end;
    match goal with
    | [H : dy_level ?Cout = _|-_] =>
      match type of H with
      | context [inject ?Cout ?Cin] =>
        pose proof (inject_level_inc Cout Cin); try nia
      end
    end
  | _ =>
    (* base case *)
    induction Cout; eauto;
    simpl;
    repeat rewrite ID_refl;
    repeat rewrite t_refl;
    repeat rewrite ctx_refl; eauto
  end.
Qed.
  
Notation "Cin '[|' Cout '|]'" := (inject Cout Cin)
                              (at level 99, Cout at next level, right associativity).

Definition inject_v {T} `{Eq T} (Cout : dy_ctx T) (v : expr_value T) :=
  match v with
  | Closure x t C => Closure x t (C [|Cout|])
  end.

Definition delete_v {T} eqb (Cout : dy_ctx T) (v : expr_value T) :=
  match v with
  | Closure x t C => Closure x t (delete eqb Cout C)
  end.

Lemma inject_ctx_M :
  forall {T} `{Eq T} M (Cout Cin : dy_ctx T),
    ctx_M (Cin [| Cout |]) M =
    match ctx_M Cin M with
    | Some CM => Some (CM [| Cout |])
    | None => ctx_M Cout M
    end.
Proof.
  intros. revert Cout.
  induction Cin; intros; simpl; eauto.
  rewrite IHCin2.
  des_goal; eauto.
Qed.

Lemma inject_addr_x :
  forall {T} `{Eq T} x (Cout Cin : dy_ctx T),
    addr_x (Cin [| Cout |]) x =
    match addr_x Cin x with
    | Some t => Some t
    | None => addr_x Cout x
    end.
Proof.
  intros. revert Cout.
  induction Cin; intros; simpl; eauto.
  rewrite IHCin.
  des_goal; eauto.
Qed.

(* lemmas for trans_C *)
Lemma trans_C_id_eq {T} :
  forall (C : dy_ctx T), trans_C id C = C.
Proof.
  induction C; simpl; try rewrite IHC; eauto.
  rewrite IHC1. rewrite IHC2. reflexivity.
Qed.

Lemma eq_C_eq {T} `{Eq T} :
  forall (C C' : @dy_ctx T),
  eq_C eqb C C' = true <-> C = C'.
Proof.
  induction C; destruct C'; simpl;
  try (split; intros contra; inversion contra; fail);
  split; intros EQ;
  repeat des_hyp; try reflexivity;
  repeat match goal with
  | [H : eqb_ID _ _ = true|-_] => rewrite eqb_ID_eq in H
  | [H : eqb _ _ = true|-_] => rewrite eqb_eq in H
  | [H : eq_C _ _ _ = true|-_] => 
    try rewrite IHC in H;
    try rewrite IHC1 in H;
    try rewrite IHC2 in H
  | _ => clarify
  end; try reflexivity;
  try rewrite ID_refl;
  try rewrite t_refl;
  repeat match goal with
  | |- context[eq_C ?eqb ?C ?C] =>
    match goal with
    | [H : context [eq_C eqb C _ = true <-> _] |- _] =>
      let RR := fresh "RR" in
      assert (eq_C eqb C C = true) as RR;
      try rewrite H; eauto; rewrite RR
    end
  end.
Qed.

Lemma trans_C_eq_C {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall C C',
    let eqb' t t' := eqb (α t) (α t') in
    eq_C eqb' C C' = true <->
    trans_C α C = trans_C α C'.
Proof.
  induction C; induction C'; simpl;
  try (split; intros contra; inversion contra; eauto; fail);
  split; intros EQ;
  repeat des_hyp;
  repeat match goal with
  | [H : eqb_ID _ _ = true|-_] => 
    rewrite eqb_ID_eq in H; rewrite H
  | [H : eqb _ _ = true|-_] => 
    rewrite eqb_eq in H; rewrite H
  | [H : eq_C _ _ _ = true|-_] => 
    try rewrite IHC in H;
    try rewrite IHC1 in H;
    try rewrite IHC2 in H;
    rewrite H
  | _ => clarify
  end; try reflexivity;
  try rewrite ID_refl;
  repeat match goal with
  | [RR : α _ = α _|-_] => rewrite RR; rewrite t_refl
  | |- context[eq_C ?eqb' ?C ?C'] =>
    match goal with
    | [H : context [eq_C _ C _ = true <-> _]|-_] =>
      let RR := fresh "RR" in
      assert (eq_C eqb' C C' = true) as RR;
      try rewrite H; try assumption; rewrite RR
    | _ => fail
    end
  end; eauto.
Qed.

Lemma trans_C_delete {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall Cout C,
    let eqb' t t' := eqb (α t) (α t') in
    trans_C α (delete eqb' Cout C) = delete eqb (trans_C α Cout) (trans_C α C).
Proof.
  intros.
  assert (forall C', eq_C eqb' Cout C' = eq_C eqb (trans_C α Cout) (trans_C α C')) as RR.
  { induction Cout; induction C'; eauto.
    simpl. rewrite IHCout. eauto.
    simpl. rewrite IHCout1. rewrite IHCout2. eauto. }
  induction C; intros; simpl; rewrite RR; simpl;
  des_goal; eauto;
  try rewrite IHC;
  try rewrite IHC1;
  try rewrite IHC2; eauto.
Qed.

Generalizable Variables T BT AT.

Fixpoint inject_ctx_mem `{Eq T} (Cout : dy_ctx T) (mem : memory T) :=
  match mem with
  | [] => []
  | (t, v) :: tl =>
    (t, inject_v Cout v) :: inject_ctx_mem Cout tl
  end.

Fixpoint delete_ctx_mem `{Eq T} eqb (Cout : dy_ctx T) (mem : memory T) :=
  match mem with
  | [] => []
  | (t, v) :: tl =>
    (t, delete_v eqb Cout v) :: delete_ctx_mem eqb Cout tl
  end.

Lemma delete_ctx_mem_eq `{Eq T} eqb (t_refl : forall t, eqb t t = true) :
  forall (Cout : dy_ctx T) (mem : memory T),
         delete_ctx_mem eqb Cout (inject_ctx_mem Cout mem) = mem.
Proof.
  induction mem; simpl; eauto.
  repeat des_goal; clarify; rw.
  destruct e; simpl.
  pose proof (@delete_inject_eq T eqb) as RR.
  rewrite RR; eauto.
Qed.

Inductive link BT AT :=
  | BF (t : BT)
  | AF (t : AT)
.

Arguments BF {BT AT}.
Arguments AF {BT AT}.

Definition link_eqb `{Eq BT} `{Eq AT} (t t' : link BT AT) :=
  match t, t' with
  | BF t, BF t' => eqb t t'
  | AF t, AF t' => eqb t t'
  | _, _ => false
  end.

Lemma link_eqb_eq `{Eq BT} `{Eq AT} :
  forall (t t' : link BT AT), link_eqb t t' = true <-> t = t'.
Proof.
  intros.
  destruct t; destruct t'; simpl; split; intros EQ; 
  try rewrite eqb_eq in *;
  try inversion EQ;
  subst; eauto.
Qed.

#[export] Instance link_eq `{Eq BT} `{Eq AT} : Eq (link BT AT) :=
  {
    eqb := link_eqb;
    eqb_eq := link_eqb_eq;
  }.

Fixpoint filter_ctx_bf {BT AT} (C : dy_ctx (link BT AT)) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' =>
    match t with
    | BF t => dy_binde x t (filter_ctx_bf C')
    | AF t => filter_ctx_bf C'
    end
  | dy_bindm M C' C'' => dy_bindm M (filter_ctx_bf C') (filter_ctx_bf C'')
  end.

Fixpoint filter_ctx_af {BT AT} (C : dy_ctx (link BT AT)) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' =>
    match t with
    | AF t => dy_binde x t (filter_ctx_af C')
    | BF t => filter_ctx_af C'
    end
  | dy_bindm M C' C'' => dy_bindm M (filter_ctx_af C') (filter_ctx_af C'')
  end.

Definition filter_v_bf {BT AT} (v : expr_value (link BT AT)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_bf C)
  end.

Definition filter_v_af {BT AT} (v : expr_value (link BT AT)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_af C)
  end.

Fixpoint filter_mem_bf {BT AT} (mem : memory (link BT AT)) :=
  match mem with
  | [] => []
  | (AF _, _) :: tl => filter_mem_bf tl
  | (BF t, v) :: tl => (t, filter_v_bf v) :: filter_mem_bf tl
  end.

Fixpoint filter_mem_af {BT AT} (mem : memory (link BT AT)) :=
  match mem with
  | [] => []
  | (AF t, v) :: tl => (t, filter_v_af v) :: filter_mem_af tl
  | (BF _, _) :: tl => filter_mem_af tl
  end.

Fixpoint lift_ctx_bf {BT AT} C : dy_ctx (link BT AT) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' => dy_binde x (BF t) (lift_ctx_bf C')
  | dy_bindm M C' C'' => dy_bindm M (lift_ctx_bf C') (lift_ctx_bf C'')
  end.

Definition lift_v_bf {BT AT} v : expr_value (link BT AT) :=
  match v with
  | Closure x e C => Closure x e (lift_ctx_bf C)
  end.

Fixpoint lift_mem_bf {BT AT} m : memory (link BT AT) :=
  match m with
  | [] => []
  | (t, v) :: tl => (BF t, lift_v_bf v) :: lift_mem_bf tl
  end.

Fixpoint lift_ctx_af {BT AT} C : dy_ctx (link BT AT) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' => dy_binde x (AF t) (lift_ctx_af C')
  | dy_bindm M C' C'' => dy_bindm M (lift_ctx_af C') (lift_ctx_af C'')
  end.

Definition lift_v_af {BT AT} v : expr_value (link BT AT) :=
  match v with
  | Closure x e C => Closure x e (lift_ctx_af C)
  end.

Fixpoint lift_mem_af {BT AT} m : memory (link BT AT) :=
  match m with
  | [] => []
  | (t, v) :: tl => (AF t, lift_v_af v) :: lift_mem_af tl
  end.

Lemma read_filter_bf `{Eq BT} `{Eq AT} :
  forall (m : memory (link BT AT)) (t : BT) (v : expr_value BT),
    Some v = read (filter_mem_bf m) t <->
    exists v', v = filter_v_bf v' /\ Some v' = read m (BF t).
Proof.
  induction m; ii;
  split; intros READ; ss;
  repeat des_goal; repeat des_hyp; des;
  try rewrite eqb_eq in *;
  try rewrite eqb_neq in *;
  try rewrite link_eqb_eq in *;
  clarify; eauto;
  try rewrite <- aread_in in *;
  first [ rewrite IHm in READ; des; eauto 
        | try right; rewrite IHm; exists v'; eauto
        | ss; rewrite eqb_neq in *; contradict].
Qed.

Lemma aread_filter_bf `{Eq BT} `{Eq AT} :
  forall (m : memory (link BT AT)) (t : BT) (v : expr_value BT),
    In v (aread (filter_mem_bf m) t) <->
    exists v', v = filter_v_bf v' /\ In v' (aread m (BF t)).
Proof.
  induction m; ii; rewrite aread_in in *;
  split; intros READ; ss;
  repeat des_goal; repeat des_hyp; des;
  try rewrite eqb_eq in *; 
  try rewrite link_eqb_eq in *;
  clarify; eauto;
  try rewrite <- aread_in in *;
  first [ rewrite IHm in READ; des; eauto 
        | try right; rewrite IHm; exists v'; eauto
        | ss; rewrite eqb_neq in *; contradict].
Qed.

Lemma read_filter_af `{Eq BT} `{Eq AT} :
  forall (m : memory (link BT AT)) (t : AT) (v : expr_value AT),
    Some v = read (filter_mem_af m) t <->
    exists v', v = filter_v_af v' /\ Some v' = read m (AF t).
Proof.
  induction m; ii;
  split; intros READ; ss;
  repeat des_goal; repeat des_hyp; des;
  try rewrite eqb_eq in *;
  try rewrite eqb_neq in *;
  try rewrite link_eqb_eq in *;
  clarify; eauto;
  try rewrite <- aread_in in *;
  first [ rewrite IHm in READ; des; eauto 
        | try right; rewrite IHm; exists v'; eauto
        | ss; rewrite eqb_neq in *; contradict].
Qed.

Lemma aread_filter_af `{Eq BT} `{Eq AT} :
  forall (m : memory (link BT AT)) (t : AT) (v : expr_value AT),
    In v (aread (filter_mem_af m) t) <->
    exists v', v = filter_v_af v' /\ In v' (aread m (AF t)).
Proof.
  induction m; ii; rewrite aread_in in *;
  split; intros READ; ss;
  repeat des_goal; repeat des_hyp; des;
  try rewrite eqb_eq in *; 
  try rewrite link_eqb_eq in *;
  clarify; eauto;
  try rewrite <- aread_in in *;
  first [ rewrite IHm in READ; des; eauto 
        | try right; rewrite IHm; exists v'; eauto
        | ss; rewrite eqb_neq in *; contradict].
Qed.

Lemma read_delete `{Eq T} eqb :
  forall (m : memory T) (Cout : dy_ctx T) t v,
    Some v = read (delete_ctx_mem eqb Cout m) t <->
    exists v', v = delete_v eqb Cout v' /\ Some v' = read m t.
Proof.
  induction m; intros; ss; split; intros READ;
  des; try contradict; repeat des_hyp; des; ss; 
  try rewrite eqb_eq in *; clarify;
  try rewrite t_refl; ss; eauto;
  first [ rewrite IHm in READ; des; eauto
        | try right; rewrite IHm; exists v'; eauto].
Qed.

Lemma aread_delete `{Eq T} eqb :
  forall (m : memory T) (Cout : dy_ctx T) t v,
    In v (aread (delete_ctx_mem eqb Cout m) t) <->
    exists v', v = delete_v eqb Cout v' /\ In v' (aread m t).
Proof.
  induction m; intros; ss; split; intros READ;
  des; try contradict; repeat des_hyp; des; ss; 
  try rewrite eqb_eq in *; clarify;
  try rewrite t_refl; ss; eauto;
  first [ rewrite IHm in READ; des; eauto
        | try right; rewrite IHm; exists v'; eauto].
Qed.

Definition link_mem `{Eq BT} `{Eq AT}
  (bmem : memory BT) (Cout : dy_ctx BT)
  (amem : memory AT) : (memory (link BT AT)) :=
  (inject_ctx_mem (lift_ctx_bf Cout) (lift_mem_af amem)) ++ 
  (lift_mem_bf bmem).

Lemma filter_lift_eq_af {BT AT} :
  forall (C : dy_ctx AT),
    filter_ctx_af (@lift_ctx_af BT AT C) = C.
Proof.
  induction C; simpl; repeat rw; eauto.
Qed.

Lemma filter_lift_eq_bf {BT AT} :
  forall (C : dy_ctx BT),
    filter_ctx_bf (@lift_ctx_bf BT AT C) = C.
Proof.
  induction C; simpl; repeat rw; eauto.
Qed.

Lemma filter_delete_eq `{Eq BT} `{Eq AT} (Cout : dy_ctx BT) 
  eqb (t_refl : forall t, eqb t t = true) :
  forall bmem amem,
  filter_mem_af
    (delete_ctx_mem eqb (lift_ctx_bf Cout)
    (link_mem bmem Cout amem)) = amem.
Proof.
  induction amem; unfold link_mem;
  ss; repeat des_goal; unfold delete_v;
  ss; repeat des_goal.
  - induction bmem; simpl; eauto.
    des_goal; clarify.
  - destruct e; ss; clarify.
    rewrite delete_inject_eq; eauto.
    rewrite filter_lift_eq_af.
    unfold link_mem in *. rewrite IHamem; eauto.
Qed.

Lemma link_update_m_eq `{Eq BT} `{Eq AT} (Cout : dy_ctx BT):
  forall bmem amem (t : AT) v,
  (AF t !-> inject_v (lift_ctx_bf Cout) (lift_v_af v);
    (link_mem bmem Cout amem)) =
    link_mem bmem Cout (t !-> v; amem).
Proof.
  intros. ss.
Qed.

Lemma lift_addr_x {BT AT} :
  forall (C : @dy_ctx AT) x,
    addr_x (lift_ctx_af C : @dy_ctx (@link BT AT)) x =
      match addr_x C x with
      | Some addr => Some (AF addr)
      | None => None
      end.
Proof.
  induction C; simpl; eauto;
  intros;
  repeat des_goal; repeat des_hyp;
  try rewrite eqb_ID_eq in *; clarify;
  repeat rw; eauto.
Qed.

Lemma lift_ctx_M {BT AT} :
  forall (C : dy_ctx AT) M,
    ctx_M (lift_ctx_af C : dy_ctx (link BT AT)) M =
      match ctx_M C M with
      | Some CM => Some (lift_ctx_af CM)
      | None => None
      end.
Proof.
  induction C; simpl; eauto;
  intros;
  repeat des_goal; repeat des_hyp;
  try rewrite eqb_ID_eq in *; clarify;
  repeat rw; eauto.
Qed.

Definition inject_cf `{Eq BT} `{Eq AT} (Cout : dy_ctx BT) (bmem : memory BT) (cf : config AT) :=
  match cf with
  | Cf e C m t =>
    Cf e ((lift_ctx_af C)[|(lift_ctx_bf Cout)|])
      (link_mem bmem Cout m) (AF t)
  | Rs V m t =>
    let m := link_mem bmem Cout m in
    let t := AF t in
    match V with
    | EVal (Closure x e C) =>
      Rs (EVal (Closure x e ((lift_ctx_af C)[|(lift_ctx_bf Cout)|]))) m t
    | MVal C =>
      Rs (MVal ((lift_ctx_af C)[|(lift_ctx_bf Cout)|])) m t
    end
  end.
