From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Strings.String.
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

Lemma __R__ : forall b, b = false <-> b <> true.
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
  | _ => fail
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
  | _ => fail
  end.

(* Types with decidable equality *)
Class Eq T : Type :=
{
  eqb : T -> T -> bool;
  eqb_eq : forall (t t' : T), eqb t t' = true <-> t = t';
  eqb_neq : forall (t t' : T), eqb t t' = false <-> t <> t'
}.

Lemma eqb_neq_template T eqb 
  (eqb_eq : forall (x x' : T), eqb x x' = true <-> x = x') : 
  forall x x', eqb x x' = false <-> x <> x'.
Proof.
  intros; split; intros contra.
  - red; intros. rewrite <- eqb_eq in *. 
    rewrite H in contra. inversion contra.
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
    destruct (eqb a t); eauto.
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

Notation "t1 '<' t2" := (lt t1 t2).

(** Syntax of our language *)
Definition ID := nat.

Definition eqb_ID := Nat.eqb.

Definition eqb_ID_eq := Nat.eqb_eq.

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

(** Statics *)
Inductive path :=
  | pnil
  | pe (x : ID) (tl : path)
  | pm (M : ID) (tl : path)
.

Inductive value :=
  | v_fn (x : ID) (e : tm)
  | v_ptr (ptr : path -> bool)
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

(* collect all static contexts reachable from the current configuration *)
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
    | Some C_M => (Some C_M, [C])
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
  try apply in_app_iff; try left; eauto;
  repeat match goal with
  | [H : forall _ : st_ctx, In _ (snd (collect_ctx _ ?e)) |- _] =>
    match goal with
    | [RR : collect_ctx ?C e = _ |- _] =>
      specialize (H C); rewrite RR in H
    | _ => fail
    end
  | _ => fail
  end; simpl in *; eauto.
Qed.

(** Dynamics *)
Inductive dy_ctx {time : Type} :=
  | dy_hole
  | dy_binde (x : ID) (tx : time) (C : dy_ctx)
  | dy_bindm (M : ID) (CM : dy_ctx) (C : dy_ctx)
.

Notation "'[|' '|]'" := (dy_hole) (at level 99).

(* Auxiliary operators *)
Fixpoint addr_x {time : Type} (C : @dy_ctx time) (x : ID) :=
  match C with
  | [||] => None
  | dy_binde x' tx' C' =>
    if eqb_ID x x' then (Some tx') else addr_x C' x
  | dy_bindm _ _ C' => addr_x C' x
  end.

Fixpoint ctx_M {time : Type} (C : @dy_ctx time) (M : ID) :=
  match C with
  | [||] => None
  | dy_binde _ _ C' => ctx_M C' M
  | dy_bindm M' CM' C' =>
    if eqb_ID M M' then Some CM' else ctx_M C' M
  end.

(* Auxiliary definition to aid proofs *)
Fixpoint st_level (C : st_ctx) :=
  match C with
  | [[||]] => 0
  | st_binde _ C' => S (st_level C')
  | st_bindm _ C' C'' => S (Nat.max (st_level C') (st_level C''))
  end.

Fixpoint dy_level {T} (C : @dy_ctx T) :=
  match C with
  | [||] => 0
  | dy_binde _ _ C' => S (dy_level C')
  | dy_bindm _ C' C'' => S (Nat.max (dy_level C') (dy_level C''))
  end.

Fixpoint dy_to_st {T} (C : @dy_ctx T) :=
  match C with
  | [||] => [[||]]
  | dy_binde x _ C' => st_binde x (dy_to_st C')
  | dy_bindm M CM C' => st_bindm M (dy_to_st CM) (dy_to_st C')
  end.

Lemma st_dy_level_eq {T} :
  forall (C : @dy_ctx T), dy_level C = st_level (dy_to_st C).
Proof.
  induction C; simpl; eauto.
Qed.

Lemma mod_is_static_none : forall {T} (dC : @dy_ctx T) (M : ID),
  (ctx_M dC M = None <-> st_ctx_M (dy_to_st dC) M = None).
Proof. 
  intros. repeat split; induction dC; simpl; eauto;
  repeat des_goal; eauto;
  match goal with
  | _ => let H := fresh "H" in intro H; inversion H
  | _ => idtac
  end.
Qed.

Lemma mod_is_static_some : forall {T} (dC : @dy_ctx T) (M : ID),
  (forall v, ctx_M dC M = Some v -> st_ctx_M (dy_to_st dC) M = Some (dy_to_st v)) /\
  (forall v, st_ctx_M (dy_to_st dC) M = Some v -> exists dv, dy_to_st dv = v /\ ctx_M dC M = Some dv).
Proof.
  intros; split; induction dC; simpl; intros; eauto;
  match goal with
  | [H : None = Some _ |- _] => inversion H
  | [H : Some _ = None |- _] => inversion H
  | _ => repeat des_goal; eauto;
    match goal with
    | [H : Some _ = Some _ |- _] =>
      inversion H; subst; eauto
    | _ => idtac
    end
  end.
Qed.

(* More semantic domains *)
Inductive expr_value {time : Type} :=
  | Closure (x : ID) (e : tm) (C : @dy_ctx time)
.

Inductive dy_value {time : Type} :=
  | EVal (ev : @expr_value time)
  | MVal (mv : @dy_ctx time)
.

Definition memory {T} := T -> option (@expr_value T).

Definition amemory {T} := T -> list (@expr_value T).

Inductive config {T} :=
  | Cf (e : tm) (C : @dy_ctx T) (m : @memory T) (t : T)
  | Rs (V : @dy_value T) (m : @memory T) (t : T)
.

Inductive aconfig {T} :=
  | ACf (e : tm) (abs_C : @dy_ctx T) (abs_m : @amemory T) (abs_t : T)
  | ARs (abs_V : @dy_value T) (abs_m : @amemory T) (abs_t : T)
.

(* Definitions for the (finite) supports *)
Fixpoint supp_C {T} (C : @dy_ctx T) (t : T) :=
  match C with
  | [||] => False
  | dy_binde _ t' C' => t = t' \/ supp_C C' t
  | dy_bindm _ C' C'' => supp_C C' t \/ supp_C C'' t
  end.

Definition supp_v {T} (v : @expr_value T) :=
  match v with
  | Closure _ _ C => supp_C C
  end.

Definition supp_V {T} (V : @dy_value T) :=
  match V with
  | EVal ev => supp_v ev
  | MVal mv => supp_C mv
  end.

Definition supp_m {T} (m : memory) (t : T) :=
  exists addr v, m addr = Some v /\ (addr = t \/ supp_v v t).

Definition supp_ρ {T} (ρ : config) (t : T) :=
  match ρ with
  | Cf _ C m time => supp_C C t \/ supp_m m t \/ time = t
  | Rs V m time => supp_V V t \/ supp_m m t \/ time = t
  end.

(** Observational equivalence *)
Inductive view {T} :=
  | Ctx (C : @dy_ctx T)
  | Ptr (t : T) (* for imperative extensions *)
  | Opq (* cannot observe more *)
.

Fixpoint obs_view {T : Type}
  (V : @dy_value T) (m : @memory T) (p : path) :=
  match p with
  | pnil =>
    match V with
    | EVal (Closure x e C) => Ctx C
    | MVal C => Ctx C
    end
  | pe x tl =>
    match obs_view V m tl with
    | Ctx C =>
      match addr_x C x with
      | None => Opq
      | Some t =>
        match m t with
        | None => Opq
        | Some (Closure x e C) => Ctx C
        end
      end
    | _ => Opq
    end
  | pm M tl =>
    match obs_view V m tl with
    | Ctx C =>
      match ctx_M C M with
      | None => Opq
      | Some C => Ctx C
      end
    | _ => Opq
    end
  end.

Definition ptr_of_t {T} `{Eq T}
  (V : @dy_value T) (m : @memory T) (t : T) (p : path) :=
  match obs_view V m p with
  | Ptr t' => eqb t t'
  | _ => false
  end.

Fixpoint observe {T} `{Eq T}
  (V : @dy_value T) (m : @memory T) (p : path) :=
  match p with
  | pnil =>
    match V with
    | EVal (Closure x e C) =>
      (Ctx C, [v_fn x e])
    | MVal C => (Ctx C, [])
    end
  | pe x tl =>
    match observe V m tl with
    | (Ctx C, obs) =>
      match addr_x C x with
      | None => (Opq, obs)
      | Some t =>
        match m t with
        | None => (Opq, obs)
        | Some (Closure x e C) =>
          (Ctx C, (v_fn x e) :: obs)
        end
      end
    | (_, obs) => (Opq, obs)
    end
  | pm M tl =>
    match observe V m tl with
    | (Ctx C, obs) =>
      match ctx_M C M with
      | None => (Opq, obs)
      | Some C => (Ctx C, obs)
      end
    | (_, obs) => (Opq, obs)
    end
  end.

Lemma eq_obs_view {T} `{Eq T} :
  forall V m p, fst (observe V m p) = obs_view V m p.
Proof.
  intros.
  induction p; simpl;
  repeat des_goal; simpl in *; clarify; eauto.
Qed.

Definition Observe {T} `{Eq T} 
  (V : @dy_value T) (m : @memory T) (p : path) :=
  snd (observe V m p).

Definition equiv {T T'} `{Eq T} `{Eq T'}
  (V : @dy_value T) (m : @memory T) (V' : @dy_value T') (m' : @memory T') :=
  forall p, Observe V m p = Observe V' m' p.

Notation "'<|' V1 m1 '≃' V2 m2 '|>'" :=
  (equiv V1 m1 V2 m2)
  (at level 10, V1 at next level, m1 at next level, V2 at next level, m2 at next level).

Fixpoint aobs_view {T : Type}
  (V : @dy_value T) (m : @amemory T) (p : path) :=
  match p with
  | pnil =>
    match V with
    | EVal (Closure x e C) => [Ctx C]
    | MVal C => [Ctx C]
    end
  | pe x tl =>
    List.fold_left (fun acc single_view =>
    let new_views := match single_view with
    | Ctx C =>
      match addr_x C x with
      | None => [Opq]
      | Some t =>
        List.fold_left (fun acc v => 
        let new_view := match v with
        | Closure x e C => Ctx C
        end in
        new_view :: acc) (m t) [Opq]
      end
    | _ => [Opq]
    end in
    new_views ++ acc) (aobs_view V m tl) []
  | pm M tl =>
    List.fold_left (fun acc single_view =>
    let new_view := match single_view with
    | Ctx C =>
      match ctx_M C M with
      | None => Opq
      | Some C => Ctx C
      end
    | _ => Opq
    end in
    new_view :: acc) (aobs_view V m tl) []
  end.

Definition aptr_of_t {T} `{Eq T}
  (V : @dy_value T) (m : @amemory T) (t : T) (p : path) :=
  Inb t (List.fold_left (fun acc single_view =>
    match single_view with
    | Ptr t => t :: acc
    | _ => acc
    end) (aobs_view V m p) []).

Fixpoint aobserve {T : Type} 
  (V : @dy_value T) (m : @amemory T) (p : path) :=
  match p with
  | pnil =>
    match V with
    | EVal (Closure x e C) =>
      [(Ctx C, [v_fn x e])]
    | MVal C => [(Ctx C, [])]
    end
  | pe x tl =>
    List.fold_left (fun acc single_trace =>
    let new_traces := match single_trace with
    | (Ctx C, obs) =>
      match addr_x C x with
      | None => [(Opq, obs)]
      | Some t =>
        List.fold_left (fun acc v =>
          let new_trace := match v with
          | Closure x e C =>
            (Ctx C, (v_fn x e) :: obs)
          end in
          new_trace :: acc) (m t) [(Opq, obs)]
      end
    | (_, obs) => [(Opq, obs)]
    end in
    new_traces ++ acc) (aobserve V m tl) []
  | pm M tl =>
    List.fold_left (fun acc single_trace =>
    let new_trace := match single_trace with
    | (Ctx C, obs) =>
      match ctx_M C M with
      | None => (Opq, obs)
      | Some C => (Ctx C, obs)
      end
    | (_, obs) => (Opq, obs)
    end in
    new_trace :: acc) (aobserve V m tl) []
  end.

Lemma union_map_comm A B :
  forall (l acc : list A) (f : A -> B) g g'
    (RR : forall a x, map f (g a x) = g' (map f a) (f x)),
  map f (fold_left g l acc) = fold_left g' (map f l) (map f acc).
Proof.
  induction l; intros; simpl; eauto.
  rewrite <- RR.
  apply IHl. eauto.
Qed.

Lemma fold_map_comm T A B :
  forall (l : list T) (acc : list A) (f : A -> B) g g'
    (RR : forall a x, map f (g a x) = g' (map f a) x),
  map f (fold_left g l acc) = fold_left g' l (map f acc).
Proof.
  induction l; intros; simpl; eauto.
  rewrite <- RR.
  apply IHl. eauto.
Qed.

Lemma app_map_comm A B :
  forall (l1 l2 : list A) (f : A -> B),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  induction l1; simpl; eauto.
  intros. rewrite IHl1. eauto.
Qed.

Lemma cut_tail_app T :
  forall (tl l l' : list T),
    l ++ tl = l' ++ tl <-> l = l'.
Proof.
  assert (forall (ll : list T), ll ++ [] = ll) as RR.
  { induction ll; simpl; eauto. rewrite IHll. eauto. }
  assert (forall (ll ll' : list T) (t : T) (EQ : ll ++ [t] = ll' ++ [t]), ll = ll').
  { 
    induction ll; induction ll'; intros; simpl in *; eauto;
    inversion EQ; subst;
    match goal with
    | [H : [] = _ ++ [?t] |- _] =>
      assert (In t []) as contra;
      try (rewrite H; rewrite in_app_iff; right; simpl; eauto);
      inversion contra
    | [H : _ ++ [?t] = [] |- _] =>
      assert (In t []) as contra;
      try (rewrite <- H; rewrite in_app_iff; right; simpl; eauto);
      inversion contra
    | [H : _ ++ [?t] = _ ++ [?t] |- _] =>
      apply IHll in H; subst; eauto
    end. 
  }
  induction tl.
  - intros. rewrite RR. rewrite RR. eauto.
  - intros.
    replace (a :: tl) with ([a] ++ tl) by reflexivity.
    rewrite app_assoc. rewrite app_assoc.
    rewrite IHtl.
    split; eauto.
    intros; subst; eauto.
Qed.

Lemma eq_aobs_view {T} `{Eq T} :
  forall V m p, List.map fst (aobserve V m p) = @aobs_view T V m p.
Proof.
  intros.
  induction p; simpl;
  repeat des_goal; simpl in *; clarify; eauto;
  rewrite <- IHp; apply union_map_comm;
  induction a; intros; simpl; repeat des_goal; eauto;
  rewrite app_map_comm;
  rewrite cut_tail_app;
  replace [Opq] with (map fst [(@Opq T, l)]) by reflexivity;
  apply fold_map_comm; intros;
  match goal with
  | [l : list _ |- _] => 
    (* most recently introduced *) induction l
  end; repeat des_goal; simpl; eauto.
Qed.

Definition AObserve {T : Type} 
  (V : @dy_value T) (m : @amemory T) (p : path) :=
  List.map snd (aobserve V m p).

Definition aequiv {T T'}
  (V : @dy_value T) (m : @amemory T) (V' : @dy_value T') (m' : @amemory T') :=
  forall (p : path) (vl : list value),
    In vl (AObserve V m p) <-> In vl (AObserve V' m' p).

Notation "'<|' V1 m1 '≃#' V2 m2 '|>'" :=
  (aequiv V1 m1 V2 m2)
  (at level 10, V1 at next level, m1 at next level, V2 at next level, m2 at next level).

(* Translation of timestamps *)
Fixpoint trans_C {T T'} (α : T -> T') (C : @dy_ctx T) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' => dy_binde x (α t) (trans_C α C')
  | dy_bindm M CM C' => dy_bindm M (trans_C α CM) (trans_C α C')
  end.

Definition trans_v {T T'} (α : T -> T') (v : @expr_value T) :=
  match v with
  | Closure x e C => Closure x e (trans_C α C)
  end.

Definition trans_V {T T'} (α : T -> T') (V : @dy_value T) :=
  match V with
  | EVal v => EVal (trans_v α v)
  | MVal C => MVal (trans_C α C)
  end.

Definition trans_m {T T'} (α : T -> T') (m : @memory T) (m' : @memory T') :=
  forall t' v',
    (m' t' = Some v' <->
      exists t v, trans_v α v = v' /\ α t = t' /\ m t = Some v)
.

Definition abstract_m {CT AT} (α : CT -> AT) (m : @memory CT) (am : @amemory AT) :=
  forall abs_t abs_v,
    (In abs_v (am abs_t) <->
      exists t v, trans_v α v = abs_v /\ α t = abs_t /\ m t = Some v)
.

Definition trans_am {AT AT'} (α : AT -> AT') (am : @amemory AT) (am' : @amemory AT') :=
  forall abs_t' abs_v',
    (In abs_v' (am' abs_t') <->
      exists abs_t abs_v, trans_v α abs_v = abs_v' /\ α abs_t = abs_t' /\ In abs_v (am abs_t))
.

Definition trans_ρ {T T'} (α : T -> T') (ρ : @config T) (ρ' : @config T') :=
  match ρ, ρ' with
  | Cf e C m t, Cf e' C' m' t' =>
    e = e' /\ trans_C α C = C' /\ trans_m α m m' /\ α t = t'
  | Rs V m t, Rs V' m' t' =>
    trans_V α V = V' /\ trans_m α m m' /\ α t = t'
  | _, _ => False
  end.

Definition abstract_ρ {CT AT} (α : CT -> AT) (ρ : @config CT) (aρ : @aconfig AT) :=
  match ρ, aρ with
  | Cf e C m t, ACf e' C' m' t' =>
    e = e' /\ trans_C α C = C' /\ abstract_m α m m' /\ α t = t'
  | Rs V m t, ARs V' m' t' =>
    trans_V α V = V' /\ abstract_m α m m' /\ α t = t'
  | _, _ => False
  end.

Definition trans_aρ {T T'} (α : T -> T') (aρ : @aconfig T) (aρ' : @aconfig T') :=
  match aρ, aρ' with
  | ACf e C m t, ACf e' C' m' t' =>
    e = e' /\ trans_C α C = C' /\ trans_am α m m' /\ α t = t'
  | ARs V m t, ARs V' m' t' =>
    trans_V α V = V' /\ trans_am α m m' /\ α t = t'
  | _, _ => False
  end.

(* Lemmas on translation *)
Lemma trans_C_addr :
  forall {CT AT} (α : CT -> AT) C x,
    addr_x (trans_C α C) x = 
      match (addr_x C x) with 
      | None => None 
      | Some addr => Some (α addr) 
      end.
Proof.
  induction C; eauto.
  intros. simpl.
  destruct (eqb_ID x0 x); eauto.
Qed.

Lemma trans_C_ctx_M :
  forall {CT AT} C (α : CT -> AT) abs_C M C_M
        (ACCESS : ctx_M C M = Some C_M)
        (TRANS : trans_C α C = abs_C),
    ctx_M abs_C M = Some (trans_C α C_M).
Proof.
  induction C; intros; simpl in *.
  - inversion ACCESS.
  - rewrite <- TRANS. simpl. apply IHC; eauto.
  - rewrite <- TRANS. simpl.
    destruct (eqb_ID M0 M); eauto.
    inversion ACCESS; eauto.
Qed.

Fixpoint eq_C {T} eqb (C1 C2 : @dy_ctx T) :=
  match C1, C2 with
  | [||], [||] => true
  | dy_binde x1 t1 C1', dy_binde x2 t2 C2' =>
    eqb_ID x1 x2 && eqb t1 t2 && eq_C eqb C1' C2'
  | dy_bindm M1 C1' C1'', dy_bindm M2 C2' C2'' =>
    eqb_ID M1 M2 && eq_C eqb C1' C2' && eq_C eqb C1'' C2''
  | _, _ => false
  end.

Lemma ctx_refl {T} eqb (t_refl : forall t, eqb t t = true) : 
  forall (C : @dy_ctx T), eq_C eqb C C = true.
Proof.
  induction C; simpl; try rewrite ID_refl; try rewrite t_refl;
  try rewrite IHC; try rewrite IHC1; try rewrite IHC2; eauto.
Qed.

Lemma eq_C_st_eq {T} eqb (C1 C2 : @dy_ctx T) :
  eq_C eqb C1 C2 = true -> dy_to_st C1 = dy_to_st C2.
Proof.
  intros EQ. revert C2 EQ.
  induction C1; induction C2; intros; simpl; eauto; try (inversion EQ; fail);
  simpl in EQ.
  destruct (eqb_ID x x0) eqn:EQID; try (inversion EQ; fail);
  destruct (eqb tx tx0) eqn:EQt; try (inversion EQ; fail);
  destruct (eq_C eqb C1 C2) eqn:EQC; try (inversion EQ; fail).
  rewrite IHC1 with (C2 := C2); eauto.
  replace x0 with x; eauto. rewrite <- eqb_ID_eq; eauto.
  destruct (eqb_ID M M0) eqn:EQID; try (inversion EQ; fail);
  destruct (eq_C eqb C1_1 C2_1) eqn:EQC1; try (inversion EQ; fail);
  destruct (eq_C eqb C1_2 C2_2) eqn:EQC2; try (inversion EQ; fail).
  erewrite IHC1_1; eauto. erewrite IHC1_2; eauto.
  replace M0 with M. eauto. rewrite <- eqb_ID_eq; eauto.
Qed.

Lemma eq_C_level_eq {T} eqb (C1 C2 : @dy_ctx T) :
  eq_C eqb C1 C2 = true -> dy_level C1 = dy_level C2.
Proof.
  intros EQ.
  repeat rewrite st_dy_level_eq.
  erewrite eq_C_st_eq; eauto.
Qed.

(* injection, deletion *)

Fixpoint inject {T} (Cout Cin : @dy_ctx T) :=
  match Cin with
  | [||] => Cout
  | dy_binde x t C' =>
    dy_binde x t (inject Cout C')
  | dy_bindm M C' C'' =>
    dy_bindm M (inject Cout C') (inject Cout C'')
  end.

Fixpoint delete {T} eqb (Cout Cin : @dy_ctx T) :=
  if eq_C eqb Cout Cin then [||]
  else match Cin with
  | [||] => [||]
  | dy_binde x t Cin' =>
    dy_binde x t (delete eqb Cout Cin')
  | dy_bindm M Cin' Cin'' =>
    dy_bindm M (delete eqb Cout Cin') (delete eqb Cout Cin'')
  end.

Lemma inject_level_inc {T} (Cout Cin : @dy_ctx T) :
  dy_level Cout <= dy_level (inject Cout Cin).
Proof.
  induction Cin; intros; simpl; nia.
Qed.

Lemma delete_inject_eq {T} eqb (t_refl : forall t, eqb t t = true) :
  forall (Cout Cin : @dy_ctx T),
    delete eqb Cout (inject Cout Cin) = Cin.
Proof.
  intros. revert Cout. induction Cin; simpl.
  - induction Cout; eauto;
    simpl; rewrite ID_refl; try rewrite t_refl; repeat rewrite ctx_refl; eauto.
  - intros. rewrite IHCin.
    destruct (eq_C eqb Cout (dy_binde x tx (inject Cout Cin))) eqn:F; eauto.
    assert (dy_level Cout = dy_level (dy_binde x tx (inject Cout Cin))) as RR.
    { eapply eq_C_level_eq; eauto. }
    simpl in RR.
    pose proof (inject_level_inc Cout Cin) as contra. nia.
  - intros. rewrite IHCin1. rewrite IHCin2.
    destruct (eq_C eqb Cout (dy_bindm M (inject Cout Cin1) (inject Cout Cin2))) eqn:F; eauto.
    assert (dy_level Cout = dy_level (dy_bindm M (inject Cout Cin1) (inject Cout Cin2))) as RR.
    { eapply eq_C_level_eq; eauto. }
    simpl in RR.
    pose proof (inject_level_inc Cout Cin1) as contra1.
    pose proof (inject_level_inc Cout Cin2) as contra2. nia.
Qed.
  
Notation "Cin '[|' Cout '|]'" := (inject Cout Cin)
                              (at level 99, Cout at next level, right associativity).

Definition inject_v {T} `{Eq T} (Cout : @dy_ctx T) (v : @expr_value T) :=
  match v with
  | Closure x t C => Closure x t (Cout [|C|])
  end.

Definition delete_v {T} eqb (Cout : @dy_ctx T) (v : @expr_value T) :=
  match v with
  | Closure x t C => Closure x t (delete eqb Cout C)
  end.

Lemma inject_ctx_M :
  forall {T} `{Eq T} M (Cout Cin : @dy_ctx T),
    ctx_M (Cin [| Cout |]) M =
    match ctx_M Cin M with
    | Some CM => Some (CM [| Cout |])
    | None => ctx_M Cout M
    end.
Proof.
  intros. revert Cout.
  induction Cin; intros; simpl; eauto.
  rewrite IHCin2.
  destruct (eqb_ID M M0); eauto.
Qed.

Lemma inject_addr_x :
  forall {T} `{Eq T} x (Cout Cin : @dy_ctx T),
    addr_x (Cin [| Cout |]) x =
    match addr_x Cin x with
    | Some t => Some t
    | None => addr_x Cout x
    end.
Proof.
  intros. revert Cout.
  induction Cin; intros; simpl; eauto.
  rewrite IHCin.
  destruct (eqb_ID x x0); eauto.
Qed.

(* lemmas for trans_C *)
Lemma trans_C_id_eq {T} :
  forall (C : @dy_ctx T), trans_C id C = C.
Proof.
  induction C; simpl; try rewrite IHC; eauto.
  rewrite IHC1. rewrite IHC2. reflexivity.
Qed.

Lemma eq_C_eq {T} `{Eq T} :
  forall (C C' : @dy_ctx T),
  eq_C eqb C C' = true <-> C = C'.
Proof.
  induction C; destruct C'; simpl;
  try (split; intros contra; inversion contra; eauto; fail).
  - split; intros EQ.
    + destruct (eqb_ID x x0) eqn:EQid; try (inversion EQ; fail);
      destruct (eqb tx tx0) eqn:EQt; try (inversion EQ; fail).
      simpl in EQ.
      rewrite IHC in EQ. rewrite eqb_ID_eq in EQid. rewrite eqb_eq in EQt.
      subst; eauto.
    + inversion EQ. subst. rewrite ID_refl. rewrite t_refl. simpl.
      apply IHC. eauto.
  - split; intros EQ.
    + destruct (eqb_ID M M0) eqn:EQid; try (inversion EQ; fail);
      destruct (eq_C eqb C1 C'1) eqn:EQC1; try (inversion EQ; fail).
      simpl in EQ.
      rewrite IHC2 in EQ. rewrite eqb_ID_eq in EQid. rewrite IHC1 in EQC1.
      subst; eauto.
    + inversion EQ. subst. rewrite ID_refl. simpl.
      replace (eq_C eqb C'1 C'1) with true. simpl.
      apply IHC2. eauto. symmetry. apply IHC1. eauto.
Qed.

Lemma trans_C_eq_C {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall C C',
    let eqb' t t' := eqb (α t) (α t') in
    eq_C eqb' C C' = true <->
    trans_C α C = trans_C α C'.
Proof.
  induction C; induction C'; simpl;
  try (split; intros contra; inversion contra; eauto; fail).
  - split; intros EQ.
    + destruct (eqb_ID x x0) eqn:EQid;
      try (inversion EQ; fail).
      destruct (eqb (α tx) (α tx0)) eqn:EQt;
      try (inversion EQ; fail).
      destruct (eq_C (fun t t' : CT => eqb (α t) (α t')) C C') eqn:EQC;
      try (inversion EQ; fail).
      rewrite eqb_ID_eq in EQid. rewrite eqb_eq in EQt.
      specialize (IHC C').
      rewrite EQid. rewrite EQt. 
      replace (trans_C α C') with (trans_C α C). reflexivity. 
      apply IHC. eauto.
    + inversion EQ; subst. rewrite ID_refl. simpl.
      rewrite t_refl. simpl.
      rewrite IHC. eauto.
  - split; intros EQ.
    + destruct (eqb_ID M M0) eqn:EQid;
      try (inversion EQ; fail).
      destruct (eq_C (fun t t' : CT => eqb (α t) (α t')) C1 C'1) eqn:EQC1;
      try (inversion EQ; fail).
      destruct (eq_C (fun t t' : CT => eqb (α t) (α t')) C2 C'2) eqn:EQC2;
      try (inversion EQ; fail).
      rewrite eqb_ID_eq in EQid.
      specialize (IHC1 C'1). specialize (IHC2 C'2).
      rewrite EQid.
      replace (trans_C α C'1) with (trans_C α C1).
      replace (trans_C α C'2) with (trans_C α C2). reflexivity.
      rewrite <- IHC2. eauto. rewrite <- IHC1. eauto.
    + inversion EQ; subst. rewrite ID_refl. simpl.
      replace (eq_C (fun t t' : CT => eqb (α t) (α t')) C1 C'1) with true. simpl.
      rewrite IHC2. eauto. symmetry. rewrite IHC1. eauto.
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
  induction C; intros; simpl; rewrite RR; simpl.
  - destruct (eq_C eqb (trans_C α Cout) ([||])); eauto.
  - destruct (eq_C eqb (trans_C α Cout) (dy_binde x (α tx) (trans_C α C))); eauto.
    simpl. rewrite IHC. eauto.
  - destruct (eq_C eqb (trans_C α Cout)
      (dy_bindm M (trans_C α C1) (trans_C α C2))); eauto.
    simpl. rewrite IHC1. rewrite IHC2. eauto.
Qed.
