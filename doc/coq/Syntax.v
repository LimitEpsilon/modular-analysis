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

Scheme expr_ind_mut := Induction for expr_tm Sort Prop
with mod_ind_mut := Induction for mod_tm Sort Prop.

Inductive value : expr_tm -> Prop :=
  | v_fn (x : expr_id) (e : expr_tm) : value (e_lam x e)
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
Fixpoint collect_ctx_expr C e :=
  match e with
  | e_var x => [C]
  | e_lam x e' => C :: collect_ctx_expr
                       (C [[|st_c_lam x ([[||]]) |]]) e'
  | e_app e1 e2 =>
    let ctxs1 := collect_ctx_expr C e1 in
    let ctxs2 := collect_ctx_expr C e2 in
    ctxs1 ++ ctxs2
  | e_link m e' =>
    match collect_ctx_mod C m with
    | (Some C_m, ctxs_m) => 
      let ctxs_e := collect_ctx_expr C_m e' in
      ctxs_m ++ ctxs_e
    | (None, ctxs_m) => ctxs_m
    end
  end

with collect_ctx_mod C m :=
  match m with
  | m_empty => (Some C, [C])
  | m_var M =>
    match st_ctx_M C M with
    | Some C_M => (Some C_M, [C ; C_M])
    | None => (None, [C])
    end
  | m_lete x e m' =>
    let ctxs_e := collect_ctx_expr C e in
    let (ctx_o, ctxs_m) := collect_ctx_mod 
                           (C [[| st_c_lete x ([[||]]) |]]) m' in
    (ctx_o, ctxs_e ++ ctxs_m)
  | m_letm M m1 m2 =>
    match collect_ctx_mod C m1 with
    | (Some C_M, ctxs_m1) => 
      let (ctx_o, ctxs_m2) := collect_ctx_mod
                              (C [[| st_c_letm M C_M ([[||]]) |]]) m2 in
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