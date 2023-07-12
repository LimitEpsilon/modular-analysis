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

Definition eq_eid id1 id2 :=
  match id1, id2 with
  | eid x1, eid x2 => x1 =? x2
  end.

Definition eq_mid id1 id2 :=
  match id1, id2 with
  | mid M1, mid M2 => M1 =? M2
  end.

Lemma eq_eid_eq : forall x x',
  eq_eid x x' = true <-> x = x'.
Proof.
  intros. destruct x. destruct x'.
  simpl. split; intros. 
  rewrite Nat.eqb_eq in H.
  rewrite H. eauto.
  inversion H; subst. rewrite Nat.eqb_eq. eauto.
Qed.

Lemma eq_eid_neq : forall x x',
  eq_eid x x' = false <-> x <> x'.
Proof.
  intros. destruct x. destruct x'.
  simpl. split; intros.
  unfold not. intros.
  rewrite Nat.eqb_neq in H. apply H. inversion H0. eauto.
  rewrite Nat.eqb_neq. unfold not. intros. apply H. subst; eauto.
Qed.

Lemma eq_mid_eq : forall M M',
  eq_mid M M' = true <-> M = M'.
Proof.
  intros. destruct M. destruct M'.
  simpl. split; intros. 
  rewrite Nat.eqb_eq in H.
  rewrite H. eauto.
  inversion H; subst. rewrite Nat.eqb_eq. eauto.
Qed.

Lemma eq_mid_neq : forall M M',
  eq_eid M M' = false <-> M <> M'.
Proof.
  intros. destruct M. destruct M'.
  simpl. split; intros.
  unfold not. intros.
  rewrite Nat.eqb_neq in H. apply H. inversion H0. eauto.
  rewrite Nat.eqb_neq. unfold not. intros. apply H. subst; eauto.
Qed.

Inductive tm :=
  | e_var (x : expr_id)
  | e_lam (x : expr_id) (e : tm)
  | e_app (e1 : tm) (e2 : tm)
  | e_link (m : tm) (e : tm)
  | m_empty
  | m_var (M : mod_id)
  | m_lete (x : expr_id) (e : tm) (m : tm)
  | m_letm (M : mod_id) (m1 : tm) (m2 : tm)
.

Fixpoint eq_tm e e' :=
  match e, e' with
  | e_var x, e_var x' => eq_eid x x'
  | e_lam x e, e_lam x' e' => eq_eid x x' && eq_tm e e'
  | e_app e1 e2, e_app e1' e2' => eq_tm e1 e1' && eq_tm e2 e2'
  | e_link m e, e_link m' e' => eq_tm m m' && eq_tm e e'
  | m_empty, m_empty => true
  | m_var M, m_var M' => eq_mid M M'
  | m_lete x e m, m_lete x' e' m' => eq_eid x x' && eq_tm e e' && eq_tm m m'
  | m_letm M m1 m2, m_letm M' m1' m2' => eq_mid M M' && eq_tm m1 m1' && eq_tm m2 m2'
  | _, _ => false
  end.

Lemma eq_tm_eq : forall e e', eq_tm e e' = true <-> e = e'.
Proof.
  induction e; intros; split; intros EQ; simpl in *;
  destruct e'; try (inversion EQ; fail);
  try destruct (eq_eid x x0) eqn:EIDEQ;
  try destruct (eq_mid M M0) eqn:MIDEQ;
  try destruct (eq_tm e e') eqn:TMEQ;
  try destruct (eq_tm e1 e'1) eqn:TMEQ1;
  try destruct (eq_tm e2 e'2) eqn:TMEQ2;
  inversion EQ;
  try rewrite IHe in TMEQ;
  try rewrite IHe1 in TMEQ1;
  try rewrite IHe2 in TMEQ2;
  try rewrite eq_eid_eq in *;
  try rewrite eq_mid_eq in *;
  subst; simpl;
  try reflexivity;
  try (rewrite <- EIDEQ; rewrite eq_eid_eq; reflexivity);
  try (rewrite <- MIDEQ; rewrite eq_mid_eq; reflexivity);
  try (rewrite <- TMEQ; rewrite IHe; reflexivity);
  try (rewrite <- TMEQ1; rewrite IHe1; reflexivity);
  try (rewrite <- TMEQ2; rewrite IHe2; reflexivity).
Qed.

Inductive value : tm -> Prop :=
  | v_fn x e : value (e_lam x e)
.

Inductive st_ctx :=
  | st_c_hole
  | st_c_lam (x : expr_id) (C : st_ctx)
  | st_c_lete (x : expr_id) (C : st_ctx)
  | st_c_letm (M : mod_id) (CM : st_ctx) (C : st_ctx)
.

Fixpoint st_level (C : st_ctx) : nat :=
  match C with
  | st_c_hole => 0
  | st_c_lam _ C'
  | st_c_lete _ C' => S (st_level C')
  | st_c_letm _ _ C' => st_level C'
  end.

Fixpoint st_ctx_M (C : st_ctx) (M : mod_id) :=
  match C with
  | st_c_hole => None
  | st_c_lam _ C'
  | st_c_lete _ C' => st_ctx_M C' M
  | st_c_letm M' CM' C' =>
    match st_ctx_M C' M with
    | Some CM => Some CM
    | None => if eq_mid M M' then Some CM' else None
    end
  end.

Fixpoint st_c_plugin (Cout : st_ctx) (Cin : st_ctx) :=
  match Cout with
  | st_c_hole => Cin
  | st_c_lam x C' => st_c_lam x (st_c_plugin C' Cin)
  | st_c_lete x C' => st_c_lete x (st_c_plugin C' Cin)
  | st_c_letm M' CM' C' => st_c_letm M' CM' (st_c_plugin C' Cin)
  end.

Lemma st_c_plugin_assoc : forall C1 C2 C3,
  st_c_plugin (st_c_plugin C1 C2) C3 =
  st_c_plugin C1 (st_c_plugin C2 C3). 
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
  rewrite IHC1_2. eauto.
Qed.

Lemma st_c_plugin_add_level :
  forall C1 C2, st_level (st_c_plugin C1 C2) = st_level C1 + st_level C2.
Proof.
  induction C1; induction C2; intros; simpl; eauto.
  - assert (RR : st_level (st_c_letm M C2_1 C2_2) = st_level C2_2); eauto.
    specialize (IHC1 (st_c_letm M C2_1 C2_2)).
    rewrite IHC1. rewrite RR. eauto.
  - assert (RR : st_level (st_c_letm M C2_1 C2_2) = st_level C2_2); eauto.
    specialize (IHC1 (st_c_letm M C2_1 C2_2)).
    rewrite IHC1. rewrite RR. eauto.
  - assert (RR : st_level (st_c_letm M0 C2_1 C2_2) = st_level C2_2); eauto.
    specialize (IHC1_2 (st_c_letm M0 C2_1 C2_2)).
    rewrite IHC1_2. rewrite RR. eauto.
Qed.

Notation "Cout '[[|' Cin '|]]'" := (st_c_plugin Cout Cin)
                              (at level 100, Cin at next level, right associativity).

Notation "'[[||]]'" := (st_c_hole) (at level 100).

(* collect all static contexts reachable from the current configuration *)
Fixpoint collect_ctx C e :=
  match e with
  | e_var x => (None, [C])
  | e_lam x e' => 
    let ctx_body := snd (collect_ctx (C [[|st_c_lam x ([[||]])|]]) e') in
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
    let (ctx_o, ctxs_m) := collect_ctx 
                           (C [[|st_c_lete x ([[||]])|]]) m' in
    (ctx_o, ctxs_e ++ ctxs_m)
  | m_letm M m1 m2 =>
    match collect_ctx C m1 with
    | (Some C_M, ctxs_m1) => 
      let (ctx_o, ctxs_m2) := collect_ctx
                              (C [[|st_c_letm M C_M ([[||]])|]]) m2 in
      (ctx_o, ctxs_m1 ++ ctxs_m2)
    | (None, ctxs_m1) => (None, ctxs_m1)
    end
  end.

Lemma st_ctx_M_plugin :
  forall Cout Cin M,
    st_ctx_M (st_c_plugin Cout Cin) M =
      match st_ctx_M Cin M with
      | Some CM => Some CM
      | None =>
        match st_ctx_M Cout M with
        | Some CM => Some CM
        | None => None
        end
      end.
Proof.
  induction Cout; intros; simpl; eauto.
  - destruct (st_ctx_M Cin M); eauto.
  - specialize (IHCout2 Cin M0). 
    destruct (st_ctx_M Cin M0). 
    rewrite IHCout2. eauto. 
    rewrite IHCout2.
    destruct (st_ctx_M Cout2 M0). eauto.
    assert (RR : forall Cout0 Cin0, 
    st_ctx_M (st_c_plugin Cout0 Cin0) M0 = None -> st_ctx_M Cin0 M0 = None).
    { induction Cout0; intros; simpl; eauto. 
      simpl in H. apply IHCout0_2.
      destruct (st_ctx_M (st_c_plugin Cout0_2 Cin0) M0).
      inversion H. eauto. }
    specialize (IHCout1 Cin M0).
    rewrite (RR Cout2 Cin IHCout2) in IHCout1.
    destruct (eq_mid M0 M).
    eauto. eauto.
Qed.

Lemma collect_ctx_refl : forall e C, In C (snd (collect_ctx C e)).
Proof.
  induction e; intros; simpl; eauto.
  - apply in_app_iff. left. eauto.
  - remember (collect_ctx C e1) as ol. destruct ol as [o l].
    specialize (IHe1 C). rewrite <- Heqol in IHe1.
    destruct o; eauto. simpl in *.
    destruct (collect_ctx C e2); simpl in *.
    destruct (collect_ctx s e2); simpl in *. 
    apply in_app_iff. left. eauto.
  - destruct (st_ctx_M C M); simpl; left; eauto.
  - destruct (collect_ctx (C [[|st_c_lete x ([[||]])|]]) e2).
    apply in_app_iff. left. eauto.
  - remember (collect_ctx C e1) as ol.
    destruct ol as [o l]. specialize (IHe1 C). rewrite <- Heqol in IHe1.
    destruct o; eauto.
    destruct (collect_ctx (C [[|st_c_letm M s ([[||]])|]]) e2).
    apply in_app_iff. left. eauto.
Qed.

(* dynamic context *)
Inductive dy_ctx {time : Type} :=
  | dy_c_hole
  | dy_c_lam (x: expr_id) (tx : time) (C : dy_ctx)
  | dy_c_lete (x : expr_id) (tx : time) (C : dy_ctx)
  | dy_c_letm (M : mod_id) (CM : dy_ctx) (C : dy_ctx)
.

Fixpoint dy_plugin_c {time : Type} (Cout : @dy_ctx time) (Cin : @dy_ctx time) :=
  match Cout with
  | dy_c_hole => Cin
  | dy_c_lam x tx C' => dy_c_lam x tx (dy_plugin_c C' Cin)
  | dy_c_lete x tx C' => dy_c_lete x tx (dy_plugin_c C' Cin)
  | dy_c_letm M CM C' => dy_c_letm M CM (dy_plugin_c C' Cin)
  end.

Fixpoint addr_x {time : Type} (C : @dy_ctx time) (x : expr_id) :=
  match C with
  | dy_c_hole => None
  | dy_c_lam x' tx' C'
  | dy_c_lete x' tx' C' =>
    match addr_x C' x with
    | None => if eq_eid x x' then (Some tx') else None
    | addr => addr
    end
  | dy_c_letm _ _ C' => addr_x C' x
  end.

Fixpoint ctx_M {time : Type} (C : @dy_ctx time) (M : mod_id) :=
  match C with
  | dy_c_hole => None
  | dy_c_lam _ _ C'
  | dy_c_lete _ _ C' => ctx_M C' M
  | dy_c_letm M' CM' C' =>
    match ctx_M C' M with
    | Some CM => Some CM
    | None => if eq_mid M M' then Some CM' else None
    end
  end.

(* a term, a context *)
Inductive expr_value {time : Type} :=
  | Closure (x : expr_id) (e : tm) (C : @dy_ctx time)
.

Inductive dy_value {time : Type} :=
  | EVal (ev : @expr_value time)
  | MVal (mv : @dy_ctx time)
.

Notation "Cout '[|' Cin '|]'" := (dy_plugin_c Cout Cin)
                              (at level 100, Cin at next level, right associativity).
Notation "'[||]'" := (dy_c_hole) (at level 100).

Fixpoint In_ctx {T} (t : T) (C : @dy_ctx T) :=
  match C with
  | [||] => False
  | dy_c_lam _ t' C'
  | dy_c_lete _ t' C' => t = t' \/ In_ctx t C'
  | dy_c_letm _ C' C'' => In_ctx t C' \/ In_ctx t C''
  end.

Fixpoint dy_level {T} (C : @dy_ctx T) :=
  match C with
  | [||] => 0
  | dy_c_lam _ _ C'
  | dy_c_lete _ _ C' => S (dy_level C')
  | dy_c_letm _ C' C'' => S (Nat.max (dy_level C') (dy_level C''))
  end.

Lemma c_plugin_assoc : forall {T} (C1 : @dy_ctx T) C2 C3, C1[| C2[| C3 |] |] = ((C1[|C2|])[|C3|]).
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
  rewrite IHC1_2. eauto.
Qed.

Fixpoint dy_to_st {T} (C : @dy_ctx T) :=
  match C with
  | ([||]) => st_c_hole
  | dy_c_lam x _ C' => st_c_lam x (dy_to_st C')
  | dy_c_lete x _ C' => st_c_lete x (dy_to_st C')
  | dy_c_letm M CM C' => st_c_letm M (dy_to_st CM) (dy_to_st C')
  end.

Lemma in_plugin_iff :
  forall {T} (t : T) (Cout Cin : @dy_ctx T),
    In_ctx t (Cout[|Cin|]) <-> (In_ctx t Cout \/ In_ctx t Cin).
Proof.
  intros. revert Cin.
  induction Cout; intros; split; simpl; intros H; 
  try rewrite IHCout in H;
  try rewrite IHCout2 in H;
  try rewrite IHCout;
  try rewrite IHCout2;
  try destruct H as [? | [? | ?]];
  try destruct H as [[? | ?] | ?];
  eauto.
  destruct H; try assumption; inversion H. 
Qed.

Lemma dy_to_st_plugin :
  forall {T} (Cout : @dy_ctx T) Cin,
    dy_to_st (Cout[|Cin|]) = st_c_plugin (dy_to_st Cout) (dy_to_st Cin).
Proof.
  induction Cout; intros; simpl; try rewrite IHCout; eauto.
  rewrite IHCout2. eauto.
Qed. 

Lemma mod_is_static_none : forall {T} (dC : @dy_ctx T) (M : mod_id),
  (ctx_M dC M = None <-> st_ctx_M (dy_to_st dC) M = None).
Proof. 
  intros. repeat split. 
  - induction dC; simpl; eauto.
    destruct (ctx_M dC2 M). intros H; inversion H.
    specialize (IHdC2 eq_refl). rewrite IHdC2.
    destruct (eq_mid M M0). intros H; inversion H. eauto.
  - induction dC; simpl; eauto.
    destruct (st_ctx_M (dy_to_st dC2) M). intros H; inversion H.
    specialize (IHdC2 eq_refl). rewrite IHdC2.
    destruct (eq_mid M M0). intros H; inversion H. eauto.
Qed.

Lemma mod_is_static_some : forall {T} (dC : @dy_ctx T) (M : mod_id),
  (forall v, ctx_M dC M = Some v -> st_ctx_M (dy_to_st dC) M = Some (dy_to_st v)) /\
  (forall v, st_ctx_M (dy_to_st dC) M = Some v -> exists dv, dy_to_st dv = v /\ ctx_M dC M = Some dv).
Proof.
  intros; split. 
  - induction dC; simpl; intros; eauto.
    + inversion H.
    + remember (ctx_M dC2 M) as v2. destruct v2.
      specialize (IHdC2 v H). rewrite IHdC2. eauto.
      symmetry in Heqv2. rewrite mod_is_static_none in Heqv2.
      rewrite Heqv2. destruct (eq_mid M M0); inversion H; eauto.
  - induction dC; simpl; intros; eauto.
    + inversion H.
    + remember (st_ctx_M (dy_to_st dC2) M) as v2. destruct v2.
      specialize (IHdC2 v H). inversion IHdC2. exists x.
      destruct H0. split. assumption. rewrite H1. eauto.
      remember (ctx_M dC2 M) as v2. destruct v2;
      symmetry in Heqv2; rewrite <- mod_is_static_none in Heqv2.
      rewrite Heqv2 in Heqv0. inversion Heqv0.
      destruct (eq_mid M M0). inversion H.
      exists dC1. eauto. inversion H.
Qed.

Fixpoint trans_ctx {CT AT} (α : CT -> AT) (C : @dy_ctx CT) :=
  match C with
  | [||] => [||]
  | dy_c_lam x t C' => dy_c_lam x (α t) (trans_ctx α C')
  | dy_c_lete x t C' => dy_c_lete x (α t) (trans_ctx α C')
  | dy_c_letm M CM C' => dy_c_letm M (trans_ctx α CM) (trans_ctx α C')
  end.

Definition trans_v {CT AT} (α : CT -> AT) (v : @expr_value CT) :=
  match v with
  | Closure x e C => Closure x e (trans_ctx α C)
  end.

Definition trans_V {CT AT} (α : CT -> AT) (V : @dy_value CT) :=
  match V with
  | EVal v => EVal (trans_v α v)
  | MVal C => MVal (trans_ctx α C)
  end.

Definition trans_mem {CT AT} (α : CT -> AT) (mem : CT -> option (@expr_value CT)) (abs_mem : AT -> list (@expr_value AT)) :=
  forall abs_t abs_v,
    (In abs_v (abs_mem abs_t) <->
      exists t v, trans_v α v = abs_v /\ α t = abs_t /\ mem t = Some v)
.

Lemma trans_ctx_addr :
  forall {CT AT} (α : CT -> AT) C x,
    addr_x (trans_ctx α C) x = 
      match (addr_x C x) with 
      | None => None 
      | Some addr => Some (α addr) 
      end.
Proof.
  induction C; eauto.
  - intros. specialize (IHC x0).
    simpl. rewrite IHC.
    destruct (addr_x C x0); simpl; eauto.
    destruct (eq_eid x0 x); eauto.
  - intros. specialize (IHC x0).
    simpl. rewrite IHC.
    destruct (addr_x C x0); simpl; eauto.
    destruct (eq_eid x0 x); eauto.
Qed.

Lemma trans_ctx_ctx_M :
  forall {CT AT} C (α : CT -> AT) abs_C M C_M
        (ACCESS : ctx_M C M = Some C_M)
        (TRANS : trans_ctx α C = abs_C),
    ctx_M abs_C M = Some (trans_ctx α C_M).
Proof.
  assert (forall {CT AT} C (α : CT -> AT) M,
    match ctx_M (trans_ctx α C) M with
    | Some _ => 
      match ctx_M C M with
      | Some _ => True
      | None => False
      end
    | None =>
      match ctx_M C M with
      | Some _ => False
      | None => True
      end
    end) as A.
  {
    induction C; intros; simpl; eauto; try apply IHC.
    destruct (eq_mid M0 M); 
    remember (ctx_M (trans_ctx α C2) M0) as ctx';
    destruct ctx';
    specialize (IHC2 α M0);
    rewrite <- Heqctx' in IHC2;
    destruct (ctx_M C2 M0);
    try inversion IHC2; eauto.
  }
  intros. revert C α abs_C M C_M ACCESS TRANS. 
  induction C; intros; simpl in *; eauto.
  - inversion ACCESS.
  - rewrite <- TRANS. simpl. apply IHC; eauto.
  - rewrite <- TRANS. simpl. apply IHC; eauto. 
  - rewrite <- TRANS. simpl.
    remember (ctx_M (trans_ctx α C2) M0) as ctx1.
    destruct ctx1; try (inversion ACCESS; fail).
    + specialize (A CT AT C2 α M0).
      rewrite <- Heqctx1 in A.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion A; inversion ACCESS; subst.
      rewrite Heqctx1. apply IHC2; eauto.
    + specialize (A CT AT C2 α M0).
      rewrite <- Heqctx1 in A.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion A; destruct (eq_mid M0 M);
      inversion ACCESS; subst; eauto.
Qed.

Lemma plugin_trans_ctx :
  forall {CT AT} Cout Cin (α : CT -> AT),
    trans_ctx α (Cout[|Cin|]) = (trans_ctx α Cout [|trans_ctx α Cin|]).
Proof.
  induction Cout; intros; simpl; 
  try rewrite IHCout; try rewrite IHCout1; try rewrite IHCout2;
  eauto.
Qed.

Class Eq T : Type :=
{
  eqb : T -> T -> bool;
  eqb_eq : forall (t t' : T), eqb t t' = true <-> t = t';
  eqb_neq : forall (t t' : T), eqb t t' = false <-> t <> t'
}.

Fixpoint eq_ctx {T} eqb (C1 : @dy_ctx T) (C2 : @dy_ctx T) :=
  match C1, C2 with
  | [||], [||] => true
  | dy_c_lam x1 t1 C1', dy_c_lam x2 t2 C2'
  | dy_c_lete x1 t1 C1', dy_c_lete x2 t2 C2' =>
    eq_eid x1 x2 && eqb t1 t2 && eq_ctx eqb C1' C2'
  | dy_c_letm M1 C1' C1'', dy_c_letm M2 C2' C2'' =>
    eq_mid M1 M2 && eq_ctx eqb C1' C2' && eq_ctx eqb C1'' C2''
  | _, _ => false
  end.

Lemma eid_refl : forall x, eq_eid x x = true.
Proof. intros; apply eq_eid_eq; eauto. Qed.

Lemma mid_refl : forall M, eq_mid M M = true.
Proof. intros; apply eq_mid_eq; eauto. Qed.

Lemma t_refl {T} `{Eq T} : forall t, eqb t t = true.
Proof. intros; apply eqb_eq; eauto. Qed.

Lemma ctx_refl {T} eqb (t_refl : forall t, eqb t t = true) : 
  forall (C : @dy_ctx T),
    eq_ctx eqb C C = true.
Proof.
  induction C; simpl; try rewrite eid_refl; try rewrite mid_refl;
  try rewrite t_refl; try rewrite IHC; try rewrite IHC1; try rewrite IHC2; eauto.
Qed.

(* injection, deletion *)

Fixpoint map_inject {T} (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  match Cin with
  | [||] => [||]
  | dy_c_lam x t C' =>
    dy_c_lam x t (map_inject Cout C')
  | dy_c_lete x t C' =>
    dy_c_lete x t (map_inject Cout C')
  | dy_c_letm M C' C'' =>
    dy_c_letm M (Cout[|map_inject Cout C'|]) (map_inject Cout C'')
  end.

Definition inject_ctx {T} (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  Cout[|map_inject Cout Cin|].

Fixpoint delete_prefix {T} eqb 
  (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  match Cout, Cin with
  | [||], Cin => Cin
  | dy_c_lam x t Cout', dy_c_lam x' t' Cin'
  | dy_c_lete x t Cout', dy_c_lete x' t' Cin' =>
    if eq_eid x x' && eqb t t' then
      delete_prefix eqb Cout' Cin'
    else Cin
  | dy_c_letm M Cout' Cout'', dy_c_letm M' Cin' Cin'' =>
    if eq_mid M M' && eq_ctx eqb Cout' Cin' then
      delete_prefix eqb Cout'' Cin''
    else Cin
  | _, _ => Cin
  end.

Lemma delete_prefix_eq {T} eqb (t_refl : forall t, eqb t t = true) :
  forall (Cout Cin : @dy_ctx T),
    delete_prefix eqb Cout (Cout[|Cin|]) = Cin.
Proof.
  intros. revert Cin.
  induction Cout; simpl; eauto;    
    try rewrite eid_refl; try rewrite mid_refl; try rewrite t_refl; try rewrite ctx_refl;
    simpl; eauto.
Qed.

Lemma delete_prefix_dec {T} eqb :
  forall (Cout Cin : @dy_ctx T),
    dy_level (delete_prefix eqb Cout Cin) <= dy_level Cin.
Proof.
  intros. revert Cout. 
  induction Cin; intros; destruct Cout; simpl; eauto;
  try destruct (eq_eid x0 x); try destruct (eqb tx0 tx);
  try destruct (eq_mid M0 M); try destruct (eq_ctx eqb Cout1 Cin1);
  simpl; try nia.
  etransitivity; try apply IHCin; eauto.
  etransitivity; try apply IHCin; eauto.
  etransitivity; try apply IHCin2; nia.
Qed.

Require Import Program.

Program Fixpoint delete_map {T} eqb
  (Cout Cin : @dy_ctx T) {measure (dy_level Cin)} :=
  match Cin with
  | [||] => [||]
  | dy_c_lam x t C' =>
    dy_c_lam x t (delete_map eqb Cout C')
  | dy_c_lete x t C' =>
    dy_c_lete x t (delete_map eqb Cout C')
  | dy_c_letm M C' C'' =>
    dy_c_letm M (delete_map eqb Cout (delete_prefix eqb Cout C'))
                (delete_map eqb Cout C'')
  end.

Next Obligation.
  simpl.
  pose proof (delete_prefix_dec eqb0 Cout C').
  nia.
Defined.
Next Obligation.
  simpl.
  pose proof (delete_prefix_dec eqb0 Cout C'').
  nia.
Defined.

(* reduction lemmas *)
Lemma delete_map_red_lam {T} (eqb : T -> T -> bool) :
  forall Cout x t C',
    delete_map eqb Cout (dy_c_lam x t C') =
      dy_c_lam x t (delete_map eqb Cout C').
Proof.
  intros. unfold delete_map. unfold delete_map_func.
  rewrite fix_sub_eq; simpl; try reflexivity.
  intros x' f g Heq.
  specialize (functional_extensionality_dep f g Heq).
  intros RR. rewrite RR. reflexivity.
Qed.

Lemma delete_map_red_lete {T} (eqb : T -> T -> bool) :
  forall Cout x t C',
    delete_map eqb Cout (dy_c_lete x t C') =
      dy_c_lete x t (delete_map eqb Cout C').
Proof.
  intros. unfold delete_map. unfold delete_map_func.
  rewrite fix_sub_eq; simpl; try reflexivity.
  intros x' f g Heq.
  specialize (functional_extensionality_dep f g Heq).
  intros RR. rewrite RR. reflexivity.
Qed.

Lemma delete_map_red_letm {T} (eqb : T -> T -> bool) :
  forall Cout M C' C'',
    delete_map eqb Cout (dy_c_letm M C' C'') =
      dy_c_letm M (delete_map eqb Cout (delete_prefix eqb Cout C'))
                  (delete_map eqb Cout C'').
Proof.
  intros. unfold delete_map. unfold delete_map_func.
  rewrite fix_sub_eq; simpl; try reflexivity.
  intros x' f g Heq.
  specialize (functional_extensionality_dep f g Heq).
  intros RR. rewrite RR. reflexivity.
Qed.

Ltac simpl_delete :=
  simpl;
  try rewrite delete_map_red_lam;
  try rewrite delete_map_red_lete;
  try rewrite delete_map_red_letm.

Lemma delete_map_eq {T} eqb (t_refl : forall t, eqb t t = true) :
  forall (Cout Cin : @dy_ctx T),
    delete_map eqb Cout (map_inject Cout Cin) = Cin.
Proof.
  intros. revert Cout.
  induction Cin; intros; simpl_delete; 
  try rewrite IHCin; eauto.
  rewrite delete_prefix_eq. 
  rewrite IHCin1. rewrite IHCin2. eauto. eauto.
Qed.

Definition delete_ctx {T} eqb (Cout Cin : @dy_ctx T) :=
  delete_map eqb Cout (delete_prefix eqb Cout Cin).

Lemma delete_inject_eq {T} eqb (t_refl : forall t, eqb t t = true) :
  forall (Cout Cin : @dy_ctx T),
    delete_ctx eqb Cout (inject_ctx Cout Cin) = Cin.
Proof.
  intros. unfold delete_ctx. unfold inject_ctx.
  rewrite delete_prefix_eq; eauto.
  rewrite delete_map_eq; eauto.
Qed.
  
Notation "Cout '<|' Cin '|>'" := (inject_ctx Cout Cin)
                              (at level 100, Cin at next level, right associativity).

Definition inject_ctx_v {T} `{Eq T} (Cout : @dy_ctx T) (v : @expr_value T) :=
  match v with
  | Closure x t C => Closure x t (Cout <|C|>)
  end.

Definition delete_ctx_v {T} eqb (Cout : @dy_ctx T) (v : @expr_value T) :=
  match v with
  | Closure x t C => Closure x t (delete_ctx eqb Cout C)
  end.

Lemma plugin_map_assoc :
  forall {T} `{Eq T} (Cout C C' : @dy_ctx T),
    (map_inject Cout C) [|map_inject Cout C'|] = (map_inject Cout (C [|C'|])).
Proof.
  intros. revert Cout C'. induction C; intros; simpl; eauto; try rewrite IHC; try rewrite IHC2; eauto.
Qed.

Lemma plugin_inject_assoc :
  forall {T} `{Eq T} (Cout C C' : @dy_ctx T),
    (Cout <| C |>)[| map_inject Cout C' |] = (Cout <|C[|C'|]|>).
Proof.
  intros. unfold inject_ctx. rewrite <- c_plugin_assoc.
  rewrite plugin_map_assoc. eauto.
Qed.

Lemma map_inject_addr_x :
  forall {T} `{Eq T} x (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    addr_x (map_inject Cout Cin) x = addr_x Cin x.
Proof.
  intros. revert Cout. 
  induction Cin; intros; simpl; eauto;
  destruct (addr_x Cin x) eqn:ADDR;
  rewrite IHCin; eauto.
Qed.

Lemma map_inject_ctx_M :
  forall {T} `{Eq T} M (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    ctx_M (map_inject Cout Cin) M =
    match ctx_M Cin M with
    | Some CM => Some (Cout <| CM |>)
    | None => None
    end.
Proof.
  intros. revert Cout.
  induction Cin; intros; simpl; eauto.
  rewrite IHCin2. destruct (ctx_M Cin2 M); eauto.
  destruct (eq_mid M M0); eauto.
Qed.

Lemma plugin_ctx_addr_x :
  forall {T} `{Eq T} x (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match addr_x Cin x with
    | Some t => addr_x (Cout[|Cin|]) x = Some t
    | None => True
    end.
Proof.
  intros. revert Cin.
  induction Cout; intros; 
  destruct (addr_x Cin x) eqn:ADDR; simpl; eauto;
  try (specialize (IHCout Cin); rewrite ADDR in IHCout;
      rewrite IHCout; eauto).
  specialize (IHCout2 Cin); rewrite ADDR in IHCout2; rewrite IHCout2; eauto.
Qed.

Lemma plugin_ctx_ctx_M :
  forall {T} `{Eq T} M (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match ctx_M Cin M with
    | Some CM => ctx_M (Cout[|Cin|]) M = Some CM
    | None => True
    end.
Proof.
  intros. revert Cin.
  induction Cout; intros;
  destruct (ctx_M Cin M) eqn:CTX; simpl; eauto;
  try (specialize (IHCout Cin); rewrite CTX in IHCout;
      rewrite IHCout; eauto).
  specialize (IHCout2 Cin); rewrite CTX in IHCout2; rewrite IHCout2; eauto.
Qed.

Lemma inject_ctx_addr_x :
  forall {T} `{Eq T} x (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match addr_x Cin x with
    | Some t => addr_x (Cout<|Cin|>) x = Some t
    | None => True
    end.
Proof.
  intros. destruct (addr_x Cin x) eqn:ADDR; eauto.
  rewrite <- map_inject_addr_x with (Cout := Cout) in ADDR.
  rewrite <- ADDR. 
  pose proof plugin_ctx_addr_x.
  specialize (H0 x Cout (map_inject Cout Cin)).
  rewrite ADDR in H0. rewrite <- H0 in ADDR.
  eauto.
Qed.

Lemma inject_ctx_ctx_M :
  forall {T} `{Eq T} M (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match ctx_M Cin M with
    | Some CM => ctx_M (Cout<|Cin|>) M = Some (Cout <|CM|>)
    | None => True
    end.
Proof.
  intros. destruct (ctx_M Cin M) eqn:CTX; eauto.
  pose proof (map_inject_ctx_M M Cout Cin).
  rewrite CTX in H0.
  pose proof (plugin_ctx_ctx_M M Cout (map_inject Cout Cin)).
  rewrite H0 in H1. eauto.
Qed.

Lemma trans_ctx_id_eq {T} :
  forall (C : @dy_ctx T), trans_ctx id C = C.
Proof.
  induction C; simpl; try rewrite IHC; eauto.
  rewrite IHC1. rewrite IHC2. reflexivity.
Qed.

Lemma eq_ctx_eq {T} `{Eq T} :
  forall (C C' : @dy_ctx T),
  eq_ctx eqb C C' = true <-> C = C'.
Proof.
  induction C; destruct C'; simpl;
  try (split; intros contra; inversion contra; eauto; fail).
  - split; intros EQ.
    + destruct (eq_eid x x0) eqn:EQid; try (inversion EQ; fail);
      destruct (eqb tx tx0) eqn:EQt; try (inversion EQ; fail).
      simpl in EQ.
      rewrite IHC in EQ. rewrite eq_eid_eq in EQid. rewrite eqb_eq in EQt.
      subst; eauto.
    + inversion EQ. subst. rewrite eid_refl. rewrite t_refl. simpl.
      apply IHC. eauto.
  - split; intros EQ.
    + destruct (eq_eid x x0) eqn:EQid; try (inversion EQ; fail);
      destruct (eqb tx tx0) eqn:EQt; try (inversion EQ; fail).
      simpl in EQ.
      rewrite IHC in EQ. rewrite eq_eid_eq in EQid. rewrite eqb_eq in EQt.
      subst; eauto.
    + inversion EQ. subst. rewrite eid_refl. rewrite t_refl. simpl.
      apply IHC. eauto.
  - split; intros EQ.
    + destruct (eq_mid M M0) eqn:EQid; try (inversion EQ; fail);
      destruct (eq_ctx eqb C1 C'1) eqn:EQC1; try (inversion EQ; fail).
      simpl in EQ.
      rewrite IHC2 in EQ. rewrite eq_mid_eq in EQid. rewrite IHC1 in EQC1.
      subst; eauto.
    + inversion EQ. subst. rewrite mid_refl. simpl.
      replace (eq_ctx eqb C'1 C'1) with true. simpl.
      apply IHC2. eauto. symmetry. apply IHC1. eauto.
Qed.

Lemma trans_ctx_eq_ctx {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall C C',
    let eqb' t t' := eqb (α t) (α t') in
    eq_ctx eqb' C C' = true <->
    trans_ctx α C = trans_ctx α C'.
Proof.
  induction C; induction C'; simpl; try (split; intros contra; inversion contra; eauto; fail).
  - split; intros EQ.
    + destruct (eq_eid x x0) eqn:EQid;
      try (inversion EQ; fail).
      destruct (eqb (α tx) (α tx0)) eqn:EQt;
      try (inversion EQ; fail).
      destruct (eq_ctx (fun t t' : CT => eqb (α t) (α t')) C C') eqn:EQC;
      try (inversion EQ; fail).
      rewrite eq_eid_eq in EQid. rewrite eqb_eq in EQt.
      specialize (IHC C').
      rewrite EQid. rewrite EQt. 
      replace (trans_ctx α C') with (trans_ctx α C). reflexivity. 
      apply IHC. eauto.
    + inversion EQ; subst. rewrite eid_refl. simpl.
      rewrite t_refl. simpl.
      rewrite IHC. eauto.
  - split; intros EQ.
    + destruct (eq_eid x x0) eqn:EQid;
      try (inversion EQ; fail).
      destruct (eqb (α tx) (α tx0)) eqn:EQt;
      try (inversion EQ; fail).
      destruct (eq_ctx (fun t t' : CT => eqb (α t) (α t')) C C') eqn:EQC;
      try (inversion EQ; fail).
      rewrite eq_eid_eq in EQid. rewrite eqb_eq in EQt.
      specialize (IHC C').
      rewrite EQid. rewrite EQt. 
      replace (trans_ctx α C') with (trans_ctx α C). reflexivity. 
      apply IHC. eauto.
    + inversion EQ; subst. rewrite eid_refl. simpl.
      rewrite t_refl. simpl.
      rewrite IHC. eauto.
  - split; intros EQ.
    + destruct (eq_mid M M0) eqn:EQid;
      try (inversion EQ; fail).
      destruct (eq_ctx (fun t t' : CT => eqb (α t) (α t')) C1 C'1) eqn:EQC1;
      try (inversion EQ; fail).
      destruct (eq_ctx (fun t t' : CT => eqb (α t) (α t')) C2 C'2) eqn:EQC2;
      try (inversion EQ; fail).
      rewrite eq_mid_eq in EQid.
      specialize (IHC1 C'1). specialize (IHC2 C'2).
      rewrite EQid.
      replace (trans_ctx α C'1) with (trans_ctx α C1).
      replace (trans_ctx α C'2) with (trans_ctx α C2). reflexivity.
      rewrite <- IHC2. eauto. rewrite <- IHC1. eauto.
    + inversion EQ; subst. rewrite mid_refl. simpl.
      replace (eq_ctx (fun t t' : CT => eqb (α t) (α t')) C1 C'1) with true. simpl.
      rewrite IHC2. eauto. symmetry. rewrite IHC1. eauto.
Qed.

Lemma trans_ctx_prefix {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall Cout C,
    let eqb' t t' := eqb (α t) (α t') in
    trans_ctx α (delete_prefix eqb' Cout C) = 
    delete_prefix eqb (trans_ctx α Cout) (trans_ctx α C).
Proof.
  induction Cout; intros; eauto.
  - simpl. destruct C; eauto.
    simpl in IHCout. subst eqb'. simpl.
    destruct (eq_eid x x0) eqn:EQid; destruct (eqb (α tx) (α tx0)) eqn:EQt;
    simpl; eauto.
  - simpl. destruct C; eauto.
    simpl in IHCout. subst eqb'. simpl.
    destruct (eq_eid x x0) eqn:EQid; destruct (eqb (α tx) (α tx0)) eqn:EQt;
    simpl; eauto.
  - simpl. destruct C; eauto.
    destruct (eq_mid M M0) eqn:EQid; destruct (eq_ctx eqb' Cout1 C1) eqn:EQC;
    simpl; rewrite EQid; simpl; eauto.
    apply trans_ctx_eq_ctx in EQC. rewrite EQC.
    rewrite ctx_refl. eauto. intros. rewrite eqb_eq. eauto.
    replace (eq_ctx eqb (trans_ctx α Cout1) (trans_ctx α C1)) with false.
    reflexivity.
    symmetry. subst eqb'.
    destruct (eq_ctx eqb (trans_ctx α Cout1) (trans_ctx α C1)) eqn:EQctx; try reflexivity.
    rewrite trans_ctx_eq_ctx in EQctx. repeat rewrite trans_ctx_id_eq in EQctx.
    rewrite <- trans_ctx_eq_ctx in EQctx. rewrite EQctx in EQC. inversion EQC.
Qed.

Lemma trans_ctx_map_aux {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall n C Cout (LE : dy_level C <= n),
    let eqb' t t' := eqb (α t) (α t') in
    trans_ctx α (delete_map eqb' Cout C) = delete_map eqb (trans_ctx α Cout) (trans_ctx α C).
Proof.
  induction n; intros; induction C; try reflexivity; try (inversion LE; fail).
  - rewrite delete_map_red_lam. simpl. rewrite IHn.
    rewrite delete_map_red_lam. reflexivity. simpl in LE. nia.
  - rewrite delete_map_red_lete. simpl. rewrite IHn.
    rewrite delete_map_red_lete. reflexivity. simpl in LE. nia.
  - rewrite delete_map_red_letm. simpl. rewrite IHn.
    rewrite delete_map_red_letm. rewrite IHC2. 
    subst eqb'. rewrite trans_ctx_prefix. reflexivity.
    simpl in LE. nia.
    etransitivity. apply delete_prefix_dec.
    simpl in LE. nia.
Qed.

Lemma trans_ctx_map {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall Cout C,
    let eqb' t t' := eqb (α t) (α t') in
    trans_ctx α (delete_map eqb' Cout C) = delete_map eqb (trans_ctx α Cout) (trans_ctx α C).
Proof.
  intros.
  apply trans_ctx_map_aux with (n := dy_level C).
  eauto.
Qed.

Lemma trans_ctx_delete {CT AT} `{ECT : Eq CT} `{EAT : Eq AT} (α : CT -> AT) :
  forall Cout C,
    let eqb' t t' := eqb (α t) (α t') in
    trans_ctx α (delete_ctx eqb' Cout C) = delete_ctx eqb (trans_ctx α Cout) (trans_ctx α C).
Proof.
  intros.
  unfold delete_ctx. subst eqb'.
  rewrite trans_ctx_map. rewrite trans_ctx_prefix.
  reflexivity.
Qed.

(* Typeclass for concrete times *)
Class OrderT (T : Type) `{Eq T} : Type :=
{
  leb : T -> T -> bool;
  leb_refl : forall t, leb t t = true;
  leb_trans : forall t t' t'' (LE : leb t t' = true) (LE' : leb t' t'' = true), leb t t'' = true;
  leb_sym : forall t t' (LE : leb t t' = true) (LE' : leb t' t = true), t = t';
  leb_or : forall t t', leb t t' || leb t' t = true
}.

Definition lt {T} `{OrderT T} (t1 t2 : T) :=
  leb t1 t2 = true /\ eqb t1 t2 = false.

Notation "t1 '<' t2" := (lt t1 t2).

Ltac contradict :=
  let contra := fresh "contra" in
  assert False as contra; eauto 3; inversion contra.

Lemma __R__ : forall b, b = false <-> ~ b = true.
Proof. 
  intros; destruct b; unfold "<>"; split; 
  intros; try inversion H; try inversion H0; try contradict; eauto.
Qed.

Ltac refl_bool :=
  match goal with
  | |- _ = false => rewrite __R__; unfold "<>"
  | |- _ <> true => rewrite <- __R__
  | _ => idtac
  end.
