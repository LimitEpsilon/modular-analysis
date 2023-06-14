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
      let ctxs_e := snd (collect_ctx C_m e') in
      (None, ctxs_m ++ ctxs_e)
    | (None, ctxs_m) => (None, ctxs_m)
    end
  | m_empty => (Some ([[||]]), [C])
  | m_var M =>
    match st_ctx_M C M with
    | Some C_M => (Some C_M, [C])
    | None => (None, [C])
    end
  | m_lete x e m' =>
    let ctxs_e := snd (collect_ctx C e) in
    let (ctx_o, ctxs_m) := collect_ctx 
                           (C [[|st_c_lete x ([[||]])|]]) m' in
    match ctx_o with
    | Some C_m => (Some (st_c_lete x C_m), ctxs_e ++ ctxs_m)
    | None => (None, ctxs_e ++ ctxs_m)
    end
  | m_letm M m1 m2 =>
    match collect_ctx C m1 with
    | (Some C_M, ctxs_m1) => 
      let (ctx_o, ctxs_m2) := collect_ctx
                              (C [[|st_c_letm M C_M ([[||]])|]]) m2 in
      match ctx_o with
      | Some C_m => (Some (st_c_letm M C_M C_m), ctxs_m1 ++ ctxs_m2)
      | None => (None, ctxs_m1 ++ ctxs_m2)
      end
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
    destruct o; eauto. apply in_app_iff. left. eauto.
  - destruct (st_ctx_M C M); simpl; left; eauto.
  - destruct (collect_ctx (C [[|st_c_lete x ([[||]])|]]) e2).
    destruct o; apply in_app_iff; left; eauto.
  - remember (collect_ctx C e1) as ol.
    destruct ol as [o l]. specialize (IHe1 C). rewrite <- Heqol in IHe1.
    destruct o; eauto.
    destruct (collect_ctx (C [[|st_c_letm M s ([[||]])|]]) e2).
    destruct o; apply in_app_iff; left; eauto.
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

Class OrderT T : Type :=
{
  leb : T -> T -> bool;
  leb_refl : forall t, leb t t = true;
  leb_trans : forall t t' t'' (LE : leb t t' = true) (LE' : leb t' t'' = true), leb t t'' = true;
  leb_sym : forall t t' (LE : leb t t' = true) (LE' : leb t' t = true), t = t';
  eqb : T -> T -> bool;
  eqb_eq : forall (t t' : T), eqb t t' = true <-> t = t';
  eqb_neq : forall (t t' : T), eqb t t' = false <-> t <> t'
}.
