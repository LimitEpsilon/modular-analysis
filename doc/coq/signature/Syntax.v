From Basics Require Export Basics.

(** Syntax of our language *)
Definition ID := String.string.

Definition eqb_ID := String.eqb.

Definition eqb_ID_eq := String.eqb_eq.

#[export] Instance EqID : Eq ID := { eqb:= eqb_ID; eqb_eq := eqb_ID_eq; }.

Definition eqb_ID_neq := String.eqb_neq.

Lemma ID_refl : forall x, eqb_ID x x = true.
Proof. intros; apply eqb_ID_eq; eauto. Qed.

Inductive st_ctx :=
  | st_hole
  | st_binde (x : ID) (C : st_ctx)
  | st_bindm (M : ID) (CM : st_ctx) (C : st_ctx)
.

Notation "'[[|' '|]]'" := (st_hole) (at level 99).

Inductive tm :=
  | e_var (x : ID)
  | e_lam (x : ID) (e : tm)
  | e_app (e1 : tm) (e2 : tm)
  | e_link (m : tm) (e : tm)
  | m_empty
  | m_var (M : ID)
  | m_lam (M : ID) (s : st_ctx) (e : tm)
  | m_app (e1 : tm) (e2 : tm) (s : st_ctx)
.

Fixpoint eqb_st s s' :=
  match s, s' with
  | ([[||]]), ([[||]]) => true
  | st_binde x s, st_binde x' s' =>
    eqb_ID x x' && eqb_st s s'
  | st_bindm M sM s, st_bindm M' sM' s' =>
    eqb_ID M M' && eqb_st sM sM' && eqb_st s s'
  | _, _ => false
  end.

Lemma eqb_st_eq : forall s s', eqb_st s s' = true <-> s = s'.
Proof.
  induction s; ii; ss;
  repeat des_goal; repeat des_hyp; ss;
  try rewrite eqb_ID_eq in *;
  try rewrite eqb_ID_neq in *;
  split; ii; clarify;
  try rewrite IHs in *;
  try rewrite IHs1 in *;
  try rewrite IHs2 in *;
  clarify.
  rrw. rw. eauto.
Qed.

#[export] Instance Eqst : Eq st_ctx := { eqb:= eqb_st; eqb_eq := eqb_st_eq; }.

Ltac solve_eqb eqb_mine :=
  assert (eqb_mine = eqb); eauto; rw.

Lemma eqb_st_neq : forall s s', eqb_st s s' = false <-> s <> s'.
Proof. solve_eqb eqb_st. exact eqb_neq. Qed.

Lemma st_refl : forall s, eqb_st s s = true.
Proof. solve_eqb eqb_st. exact t_refl. Qed.

Fixpoint eqb_tm e e' :=
  match e, e' with
  | e_var x, e_var x' => eqb_ID x x'
  | e_lam x e, e_lam x' e' => eqb_ID x x' && eqb_tm e e'
  | e_app e1 e2, e_app e1' e2' => eqb_tm e1 e1' && eqb_tm e2 e2'
  | e_link m e, e_link m' e' => eqb_tm m m' && eqb_tm e e'
  | m_empty, m_empty => true
  | m_var M, m_var M' => eqb_ID M M'
  | m_lam M s e, m_lam M' s' e' =>
    eqb_ID M M' && eqb_st s s' && eqb_tm e e'
  | m_app e1 e2 s, m_app e1' e2' s' =>
    eqb_tm e1 e1' && eqb_tm e2 e2' && eqb_st s s'
  | _, _ => false
  end.

Lemma eqb_tm_eq : forall e e', eqb_tm e e' = true <-> e = e'.
Proof.
  induction e; intros; split; intros EQ; simpl in *;
  destruct e'; try (inversion EQ; fail);
  repeat des_hyp;
  repeat match goal with
  | [H : eqb_ID _ _ = true |- _] =>
    rewrite eqb_ID_eq in H
  | [H : eqb_st _ _ = true |- _] =>
    rewrite eqb_st_eq in H
  | [H : eqb_tm _ _ = true |- _] =>
    repeat match goal with
    | [RR : context [eqb_tm _ _ = true <-> _] |- _] =>
      rewrite RR in H
    end
  | _ => idtac
  end; subst; try reflexivity;
  inversion EQ; subst;
  try rewrite ID_refl; 
  try rewrite st_refl; simpl; try reflexivity;
  repeat match goal with
  | [H : context [eqb_tm ?e _ = _] |- _] =>
    match goal with
    | [_ : eqb_tm e e = true |- _] => fail
    | _ =>
      let RR := fresh "RR" in
      assert (eqb_tm e e = true) as RR;
      try apply H; eauto; rewrite RR
    end
  | _ => fail
  end.
Qed.

#[export] Instance Eqtm : Eq tm := { eqb := eqb_tm; eqb_eq := eqb_tm_eq; }.

(** Statics *)
Inductive value : tm -> Prop :=
  | v_fn x e : value (e_lam x e)
  | v_ft M s e : value (m_lam M s e)
.

Fixpoint st_ctx_M (C : st_ctx) (M : ID) :=
  match C with
  | [[||]] => None
  | st_binde _ C' => st_ctx_M C' M
  | st_bindm M' CM' C' =>
    if eqb_ID M M' then Some CM' else st_ctx_M C' M
  end.

Fixpoint st_plugin (Cout : st_ctx) (Cin : st_ctx) :=
  match Cout with
  | st_hole => Cin
  | st_binde x C' => st_binde x (st_plugin C' Cin)
  | st_bindm M' CM' C' => st_bindm M' CM' (st_plugin C' Cin)
  end.

Notation "Cout '[[|' Cin '|]]'" := (st_plugin Cout Cin)
  (at level 100, Cin at next level, right associativity).

Lemma st_plugin_assoc : forall C1 C2 C3,
  C1 [[| C2 |]] [[| C3 |]] =
    (C1 [[| C2 [[| C3 |]] |]]).
Proof.
  induction C1; eauto; ii; ss; repeat rw; eauto.
Qed.

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
    | Some C_M => (Some (C_M[[|C|]]), C_M[[|C|]] :: [C])
    | None => (None, [C])
    end
  | m_lam M s e =>
    let ctx_body := snd (collect_ctx (st_bindm M s C) e) in
    (None, C :: ctx_body)
  | m_app e1 e2 s =>
    let ctxs1 := snd (collect_ctx C e1) in
    let ctxs2 := snd (collect_ctx C e2) in
    (Some (s[[|C|]]), s[[|C|]] :: ctxs1 ++ ctxs2)
  end.

Lemma collect_ctx_refl : forall e C, In C (snd (collect_ctx C e)).
Proof.
  induction e; intros; simpl; eauto;
  repeat des_goal;
  try rewrite in_app_iff; first [left; eauto; fail | right; eauto; fail | eauto];
  repeat match goal with
  | [H : forall _ : st_ctx, In _ (snd (collect_ctx _ ?e)) |- _] =>
    match goal with
    | [RR : collect_ctx ?C e = _ |- _] =>
      specialize (H C); rewrite RR in H
    end
  end; simpl in *; eauto.
Qed.

Lemma st_ctx_M_plugin :
  forall Cout Cin M,
    st_ctx_M (Cout[[|Cin|]]) M =
      match st_ctx_M Cout M with
      | Some CM => Some CM
      | None =>
        match st_ctx_M Cin M with
        | Some CM => Some CM
        | None => None
        end
      end.
Proof.
  induction Cout; ii; ss; des_goal; eauto.
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

(* ctx inject *)
Fixpoint inject {T} (C' C : dy_ctx T) :=
  match C with
  | [||] => C'
  | dy_binde x tx C =>
    dy_binde x tx (inject C' C)
  | dy_bindm M CM C =>
    dy_bindm M CM (inject C' C)
  end.

Notation "C1 '[|' C2 '|]'" := (inject C2 C1)
  (at level 100, C2 at next level, right associativity).

Lemma inject_assoc {T} : forall (c1 c2 c3 : dy_ctx T),
  c1 [| c2 |] [| c3 |] = (c1 [|c2 [|c3|]|]).
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

Lemma inject_addr_x {T} : forall x (Cout Cin : dy_ctx T),
  addr_x (Cin [| Cout |]) x =
  match addr_x Cin x with
  | Some t => Some t
  | None => addr_x Cout x
  end.
Proof.
  induction Cin; ii; ss. des_goal; eauto.
Qed.

Lemma inject_ctx_M {T} : forall M (Cout Cin : dy_ctx T),
  ctx_M (Cin [| Cout |]) M =
  match ctx_M Cin M with
  | Some CM => Some CM
  | None => ctx_M Cout M
  end.
Proof.
  induction Cin; ii; ss. des_goal; eauto.
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

Lemma dy_to_st_inject {T} (Cout : dy_ctx T) :
  forall Cin, dy_to_st (Cin [|Cout|]) = (dy_to_st Cin [[|dy_to_st Cout|]]).
Proof.
  induction Cin; ss; rw; eauto.
Qed.

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
  | Fun (x : ID) (e : tm) (C : dy_ctx T)
  | Func (M : ID) (s : st_ctx) (e : tm) (C : dy_ctx T)
.

Arguments Fun {T}.
Arguments Func {T}.

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

Lemma read_top {T }`{Eq T} :
  forall a b t,
  read (a ++ b) t = 
  match read a t with
  | None => read b t
  | Some _ => read a t
  end.
Proof.
  induction a; ii; ss;
  repeat des_goal; repeat des_hyp; clarify;
  repeat rw; reflexivity.
Qed.

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
  | Fun _ _ C
  | Func _ _ _ C => supp_C C
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

(* Translation of timestamps *)
Fixpoint trans_C {T T'} (α : T -> T') (C : dy_ctx T) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' => dy_binde x (α t) (trans_C α C')
  | dy_bindm M CM C' => dy_bindm M (trans_C α CM) (trans_C α C')
  end.

Definition trans_v {T T'} (α : T -> T') (v : expr_value T) :=
  match v with
  | Fun x e C => Fun x e (trans_C α C)
  | Func M s e C => Func M s e (trans_C α C)
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
Lemma trans_C_inject {T TT} (α : T -> TT) :
  forall (C1 C2 : dy_ctx T),
    trans_C α (C1 [|C2|]) = (trans_C α C1 [|trans_C α C2|]).
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

(* deletion *)

Fixpoint delete {T} eqb (Cout Cin : dy_ctx T) :=
  if eq_C eqb Cout Cin then [||]
  else match Cin with
  | [||] => [||]
  | dy_binde x t Cin' =>
    dy_binde x t (delete eqb Cout Cin')
  | dy_bindm M Cin' Cin'' =>
    dy_bindm M Cin' (delete eqb Cout Cin'')
  end.

Definition inject_v {T} `{Eq T} (Cout : dy_ctx T) (v : expr_value T) :=
  match v with
  | Fun x t C => Fun x t (C [|Cout|])
  | Func M s t C => Func M s t (C [|Cout|])
  end.

Definition delete_v {T} eqb (Cout : dy_ctx T) (v : expr_value T) :=
  match v with
  | Fun x t C => Fun x t (delete eqb Cout C)
  | Func M s t C => Func M s t (delete eqb Cout C)
  end.

Lemma inject_level_inc {T} (Cout Cin : dy_ctx T) :
  dy_level Cout <= dy_level (Cin [| Cout |]).
Proof.
  induction Cin; intros; simpl; nia.
Qed.

Lemma delete_inject_eq {T} eqb (t_refl : forall t, eqb t t = true) :
  forall (Cout Cin : dy_ctx T),
    delete eqb Cout (Cin [|Cout|]) = Cin.
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
  destruct e; simpl;
  pose proof (@delete_inject_eq T eqb) as RR;
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
  | Fun x e C => Fun x e (filter_ctx_bf C)
  | Func M s e C => Func M s e (filter_ctx_bf C)
  end.

Definition filter_v_af {BT AT} (v : expr_value (link BT AT)) :=
  match v with
  | Fun x e C => Fun x e (filter_ctx_af C)
  | Func M s e C => Func M s e (filter_ctx_af C)
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
  | Fun x e C => Fun x e (lift_ctx_bf C)
  | Func M s e C => Func M s e (lift_ctx_bf C)
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
  | Fun x e C => Fun x e (lift_ctx_af C)
  | Func M s e C => Func M s e (lift_ctx_af C)
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

Fixpoint map_m {T1 T2} (f : T1 -> T2) (m : memory T1) :=
  match m with
  | [] => []
  | (t, Fun x e C) :: tl =>
    (f t, Fun x e (trans_C f C)) :: map_m f tl
  | (t, Func M s e C) :: tl =>
    (f t, Func M s e (trans_C f C)) :: map_m f tl
  end.

Lemma inject_ctx_mem_app `{Eq T} :
  forall a b (C : dy_ctx T),
  inject_ctx_mem C (a ++ b) = inject_ctx_mem C a ++ inject_ctx_mem C b.
Proof.
  induction a; ii; ss. des_goal. rw. eauto.
Qed.

Lemma lift_mem_bf_app `{Eq BT} `{Eq AT} :
  forall a b,
  (lift_mem_bf (a ++ b) : memory (link BT AT)) =
  lift_mem_bf a ++ lift_mem_bf b.
Proof.
  induction a; ii; ss. des_goal. rw. eauto.
Qed.

Lemma lift_mem_af_app `{Eq BT} `{Eq AT} :
  forall a b,
  (lift_mem_af (a ++ b) : memory (link BT AT)) =
  lift_mem_af a ++ lift_mem_af b.
Proof.
  induction a; ii; ss. des_goal. rw. eauto.
Qed.

Lemma lift_twice `{Eq T1} `{Eq T2} `{Eq T3} :
  forall C,
  let f (t : link T1 (link T2 T3)) : link (link T1 T2) T3 :=
    match t with
    | BF t1 => BF (BF t1)
    | AF (BF t2) => BF (AF t2)
    | AF (AF t3) => AF t3
    end in
  trans_C f (lift_ctx_af (lift_ctx_af C)) = lift_ctx_af C.
Proof.
  induction C; ii; ss; subst f; repeat rw; eauto.
Qed.

Lemma lift_once `{Eq T1} `{Eq T2} `{Eq T3} :
  forall C,
  let f (t : link T1 (link T2 T3)) : link (link T1 T2) T3 :=
    match t with
    | BF t1 => BF (BF t1)
    | AF (BF t2) => BF (AF t2)
    | AF (AF t3) => AF t3
    end in
  trans_C f (lift_ctx_af (lift_ctx_bf C)) = lift_ctx_bf (lift_ctx_af C).
Proof.
  induction C; ii; ss; subst f; repeat rw; eauto.
Qed.

Lemma link_ctx_assoc `{Eq T1} `{Eq T2} `{Eq T3} :
  forall C3 C2 C1,
  let f (t : link T1 (link T2 T3)) : link (link T1 T2) T3 :=
    match t with
    | BF t1 => BF (BF t1)
    | AF (BF t2) => BF (AF t2)
    | AF (AF t3) => AF t3
    end in
  trans_C f
    (lift_ctx_af (lift_ctx_af C3 [|lift_ctx_bf C2|]) [|lift_ctx_bf C1|]) =
  (lift_ctx_af C3 [|lift_ctx_bf (lift_ctx_af C2 [|lift_ctx_bf C1|])|]).
Proof.
  induction C3; ii; ss; repeat rw;
  first [f_equal; apply lift_twice | idtac].
  revert C2 C1.
  induction C2; ii; ss; repeat rw;
  first [f_equal; apply lift_once | idtac].
  induction C1; ii; ss; repeat rw; eauto.
Qed.

Ltac des_v :=
  match goal with
  | v : expr_value _ |- _ => destruct v; ss; clarify
  end.

Lemma link_mem_assoc `{Eq T1} `{Eq T2} `{Eq T3} :
  forall m1 C1 m2 C2 m3,
  let f (t : link T1 (link T2 T3)) : link (link T1 T2) T3 :=
    match t with
    | BF t1 => BF (BF t1)
    | AF (BF t2) => BF (AF t2)
    | AF (AF t3) => AF t3
    end in
  map_m f (link_mem m1 C1 (link_mem m2 C2 m3)) =
  link_mem (link_mem m1 C1 m2) ((lift_ctx_af C2)[|lift_ctx_bf C1|]) m3.
Proof.
  ii.
  unfold link_mem.
  repeat (rewrite lift_mem_af_app 
  || rewrite inject_ctx_mem_app 
  || rewrite lift_mem_bf_app
  || rewrite <- app_assoc).
  revert m3 m2 C2 m1 C1.
  induction m3; ii; ss.
  revert m2 m1 C1.
  induction m2; ii; ss.
  - induction m1; ii; ss.
    repeat des_goal; clarify; des_v;
    rw; repeat f_equal;
    subst f;
    pose proof (@link_ctx_assoc T1 _ T2 _ T3 _ ([||]) ([||]) C0); ss.
  - repeat des_goal; clarify; des_v;
    rw; repeat f_equal;
    subst f; pose proof (link_ctx_assoc ([||]) C0 C1); ss.
  - repeat des_goal; clarify; des_v;
    rw; repeat f_equal;
    subst f; rewrite link_ctx_assoc; eauto.
Qed.

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
  ss; repeat des_goal; try des_v.
  - induction bmem; simpl; eauto.
    des_goal; clarify.
  - rewrite delete_inject_eq; eauto.
    rewrite filter_lift_eq_af.
    unfold link_mem in *. rewrite IHamem; eauto.
  - rewrite delete_inject_eq; eauto.
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
    | EVal (Fun x e C) =>
      Rs (EVal (Fun x e ((lift_ctx_af C)[|(lift_ctx_bf Cout)|]))) m t
    | EVal (Func M s e C) =>
      Rs (EVal (Func M s e ((lift_ctx_af C)[|(lift_ctx_bf Cout)|]))) m t  
    | MVal C =>
      Rs (MVal ((lift_ctx_af C)[|(lift_ctx_bf Cout)|])) m t
    end
  end.

(* projection *)

Fixpoint project {T} (d : dy_ctx T) (s : st_ctx) :=
  match s with
  | [[||]] => Some ([||])
  | st_binde x C =>
    match addr_x d x with
    | Some t =>
      match project d C with
      | Some C' => Some (dy_binde x t C')
      | None => None
      end
    | None => None
    end
  | st_bindm M CM C =>
    match ctx_M d M with
    | Some CM' =>
      match project CM' CM with
      | Some C' =>
        match project d C with
        | Some C'' => Some (dy_bindm M C' C'')
        | None => None
        end
      | None => None
      end
    | None => None
    end
  end.

Lemma plugin_project_eq {T} {ET : Eq T} 
  (Cout Cin p : @dy_ctx T) (s : st_ctx)
  (PROJECT : project Cin s = Some p) :
  project (Cin[|Cout|]) s = Some p.
Proof.
  revert Cout Cin p PROJECT.
  induction s; simpl; eauto.
  - intros.
    destruct (addr_x Cin x) eqn:ACCESS; try (inversion PROJECT; fail).
    pose proof (inject_addr_x x Cout Cin) as ADDR.
    rewrite ACCESS in ADDR. rewrite ADDR.
    destruct (project Cin s) eqn:PROJ; try (inversion PROJECT; fail).
    erewrite IHs; eauto.
  - intros.
    destruct (ctx_M Cin M) eqn:ACCESS; try (inversion PROJECT; fail).
    pose proof (inject_ctx_M M Cout Cin) as CTX.
    rewrite ACCESS in CTX. rewrite CTX.
    destruct (project d s1) eqn:PROJ1; try (inversion PROJECT; fail).
    destruct (project Cin s2) eqn:PROJ2; try (inversion PROJECT; fail).
    erewrite IHs2; eauto.
Qed.

Lemma project_st_eq {T} {ET : Eq T}
  (d ds : @dy_ctx T) (s : st_ctx)
  (PROJECT : project d s = Some ds) : dy_to_st ds = s.
Proof.
  revert d ds PROJECT.
  induction s; ii; ss; repeat des_hyp; clarify;
  s; f_equal; eauto.
Qed.
