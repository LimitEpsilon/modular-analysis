From Signature Require Export Syntax.

Generalizable Variables T.

Class time `{Eq T} :=
{
  tick : dy_ctx T -> memory T -> T -> ID -> expr_value T -> T;
  (* functional extensionality *)
  tick_ext : forall C m m' t x v (EQ : asame m m'), tick C m t x v = tick C m' t x v;
}.

Inductive step `{time T} : (config T) -> (config T) -> Prop :=
  | ExprID x C m t v addr
    (ADDR : addr_x C x = Some addr)
    (ACCESS : In v (aread m addr))
    : step (Cf (e_var x) C m t) (Rs (EVal v) m t)

  | Fn x e C m t
    : step (Cf (e_lam x e) C m t) (Rs (EVal (Closure (v_fn x e) C)) m t)
  
  | EAppL e1 e2 C m t
    : step (Cf (e_app e1 e2) C m t) (Cf e1 C m t)

  | FnEAppR e1 e2 C m t x e C_f m_f t_f
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_fn x e) C_f)) m_f t_f))
    : step (Cf (e_app e1 e2) C m t) (Cf e2 C m_f t_f)

  | FtEAppR e1 e2 C m t M s_M e C_f m_f t_f
    (FT : step (Cf e1 C m t) (Rs (EVal (Closure (v_ft M s_M e) C_f)) m_f t_f))
    : step (Cf (e_app e1 e2) C m t) (Cf e2 C m_f t_f)
  
  | FnEAppBody e1 e2 C m t x e C_f m_f t_f v m_a t_a
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_fn x e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    : step (Cf (e_app e1 e2) C m t) (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v))

  | FtEAppBody e1 e2 C m t M s_M e C_f m_f t_f C_v m_a t_a C_M
    (FT : step (Cf e1 C m t) (Rs (EVal (Closure (v_ft M s_M e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    : step (Cf (e_app e1 e2) C m t) (Cf e (dy_bindm M C_M C_f) m_a t_a)
  
  | FnEApp e1 e2 C m t x e C_f m_f t_f v m_a t_a v' m' t'
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_fn x e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    (BODY : step (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v)) (Rs (EVal v') m' t'))
    : step (Cf (e_app e1 e2) C m t) (Rs (EVal v') m' t')
  
  | FtEApp e1 e2 C m t M s_M e C_f m_f t_f C_v m_a t_a C_M v' m' t'
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_ft M s_M e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    (BODY : step (Cf e (dy_bindm M C_M C_f) m_a t_a) (Rs (EVal v') m' t'))
    : step (Cf (e_app e1 e2) C m t) (Rs (EVal v') m' t')
  
  | LinkL e1 e2 C m t
    : step (Cf (e_link e1 e2) C m t) (Cf e1 C m t)
  
  | LinkR e1 e2 C m t C' m' t'
    (MOD : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    : step (Cf (e_link e1 e2) C m t) (Cf e2 C' m' t')
  
  | Link e1 e2 C m t C' m' t' V m'' t''
    (MOD : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    (LINK : step (Cf e2 C' m' t') (Rs V m'' t''))
    : step (Cf (e_link e1 e2) C m t) (Rs V m'' t'')
  
  | Empty C m t
    : step (Cf m_empty C m t) (Rs (MVal C) m t)
  
  | ModID M C m t C_M
    (ACCESS : ctx_M C M = Some C_M)
    : step (Cf (m_var M) C m t) (Rs (MVal (C_M[|C|])) m t)
  
  | Ft M e s_M C m t
    : step (Cf (m_lam M s_M e) C m t) (Rs (EVal (Closure (v_ft M s_M e) C)) m t)

  | MAppL e1 e2 s C m t
    : step (Cf (m_app e1 e2 s) C m t) (Cf e1 C m t)

  | FnMAppR e1 e2 s C m t x e C_f m_f t_f
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_fn x e) C_f)) m_f t_f))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e2 C m_f t_f)

  | FtMAppR e1 e2 s C m t M s_M e C_f m_f t_f
    (FT : step (Cf e1 C m t) (Rs (EVal (Closure (v_ft M s_M e) C_f)) m_f t_f))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e2 C m_f t_f)
  
  | FnMAppBody e1 e2 s C m t x e C_f m_f t_f v m_a t_a
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_fn x e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v))

  | FtMAppBody e1 e2 s C m t M s_M e C_f m_f t_f C_v m_a t_a C_M
    (FT : step (Cf e1 C m t) (Rs (EVal (Closure (v_ft M s_M e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    : step (Cf (m_app e1 e2 s) C m t) (Cf e (dy_bindm M C_M C_f) m_a t_a)
  
  | FnMApp e1 e2 s C m t x e C_f m_f t_f v m_a t_a C' m' t' C_s
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_fn x e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    (BODY : step (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v)) (Rs (MVal C') m' t'))
    (PROJs : project C' s = Some C_s)
    : step (Cf (m_app e1 e2 s) C m t) (Rs (MVal (C_s[|C|])) m' t')
  
  | FtMApp e1 e2 s C m t M s_M e C_f m_f t_f C_v m_a t_a C_M C' m' t' C_s
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure (v_ft M s_M e) C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    (BODY : step (Cf e (dy_bindm M C_M C_f) m_a t_a) (Rs (MVal C') m' t'))
    (PROJs : project C' s = Some C_s)
    : step (Cf (m_app e1 e2 s) C m t) (Rs (MVal (C_s[|C|])) m' t')
.

#[export] Hint Constructors step : core.

Inductive multi_step `{time T} : (@config T) -> (@config T) -> Prop :=
  | Refl cf : multi_step cf cf
  | Trans cf cf' cf''
    (REACHl : step cf cf')
    (REACHr : multi_step cf' cf'')
    : multi_step cf cf''
.

#[export] Hint Constructors multi_step : core.

Notation "'{|' ll '~#>' rr '|}'" := 
  (step ll rr) 
  (at level 10, ll at next level, rr at next level).

Notation "'{|' ll '~#>*' rr '|}'" := 
  (multi_step ll rr) 
  (at level 10, ll at next level, rr at next level).

Lemma Meval_then_collect `{time T} :
  forall e C m t mv m' t'       
        (EVAL : {|(Cf e C m t) ~#> (Rs (MVal mv) m' t')|}),
        match collect_ctx (dy_to_st C) e with
        | (Some mv', _) => mv' = dy_to_st mv
        | (None, _) => False
        end.
Proof.
  intros.
  remember (Cf e C m t) as acf eqn:INIT.
  remember (Rs (MVal mv) m' t') as ars eqn:MVAL.
  ginduction EVAL; intros; simpl; try inversion MVAL; subst; eauto;
  repeat match goal with
  | H : forall e C m t mv m' t',
    Cf ?e' ?C' ?m'' ?t'' = Cf _ _ _ _ ->
    Rs (MVal ?mv') ?m''' ?t''' = Rs _ _ _ -> _ |- _ =>
    specialize (H e' C' m'' t'' mv' m''' t''' eq_refl eq_refl)
  end;
  repeat des_hyp; clarify; simpl in *;
  repeat match goal with
  | RR : collect_ctx ?C ?e = _ |- context [collect_ctx ?C ?e] =>
    rewrite RR
  end; try rewrite dy_to_st_inject; eauto.
  match goal with
  | H : ctx_M ?C ?M = Some ?mv |- _ =>
    let RR := fresh "RR" in
    assert (st_ctx_M (dy_to_st C) M = Some (dy_to_st mv)) as RR;
    try (apply mod_is_static_some; assumption);
    rewrite RR; eauto
  end.
  all:apply project_st_eq in PROJs; rw; eauto.
Qed.

Definition ctx_bound_m `{Eq T} ub (m : memory T) :=
  forall t v (INvl : In v (aread m t)),
    match v with
    | Closure (v_fn x e) C_v =>
      forall sC (IN : In sC (snd (collect_ctx (dy_to_st C_v) (e_lam x e)))),
        In sC ub
    | Closure (v_ft M s e) C_v =>
      forall sC (IN : In sC (snd (collect_ctx (dy_to_st C_v) (m_lam M s e)))),
        In sC ub
    end.

Definition ctx_bound_cf `{Eq T} ub (cf : config T) :=
  match cf with
  | Cf e C m t =>
    ctx_bound_m ub m /\
    forall sC (IN : In sC (snd (collect_ctx (dy_to_st C) e))), In sC ub
  | Rs (EVal (Closure (v_fn x e) C)) m t =>
    ctx_bound_m ub m /\
    forall sC (IN : In sC (snd (collect_ctx (dy_to_st C) (e_lam x e)))), In sC ub
  | Rs (EVal (Closure (v_ft M s e) C)) m t =>
    ctx_bound_m ub m /\
    forall sC (IN : In sC (snd (collect_ctx (dy_to_st C) (m_lam M s e)))), In sC ub
  | Rs (MVal C) m t =>
    ctx_bound_m ub m /\ In (dy_to_st C) ub
  end.

Lemma step_ctx_bound `{time T} :
  forall ub e (C : dy_ctx T) m t cf'
         (INIT : ctx_bound_cf ub (Cf e C m t))
         (STEP : {|(Cf e C m t) ~#> cf'|}),
    ctx_bound_cf ub cf'.
Proof.
  intros. remember (Cf e C m t) as cf eqn:CF.
  ginduction STEP; intros; clarify; destruct INIT as [BOUNDm BOUNDe];
  simpl; repeat des_goal;
  try (eauto; split; fail);
  repeat match goal with
  | IH : forall _ e C m t, _ -> _ -> _ |- _ =>
    specialize (IH ub)
  | IH : forall e C m t, _ -> _ -> ?P |- _ =>
    let BD := fresh "BD" in
    assert P as BD;
    [eapply IH; eauto; split; eauto; intros;
    match goal with
    | H : _ |- _ => apply H; fail
    | H : _ |- _ => 
      apply H; simpl; repeat des_goal;
      try rewrite in_app_iff;
      first [try left; eauto; fail | try right; eauto; fail]
    end | clear IH]
  end;
  match goal with
  | H : _ |- _ => eapply H; eauto; clear H
  | _ => idtac
  end;
  split; eauto;
  repeat match goal with
  | H : {|_ ~#> (Rs (MVal _) _ _)|} |- _ =>
    apply Meval_then_collect in H
  end; intros;
  try match goal with
  | H : _ |- _ => apply H; simpl; eauto; fail
  | H : ctx_M ?C ?M = Some ?C_M |- _ =>
    let RR := fresh "RR" in
    apply BOUNDe;
    pose proof (mod_is_static_some C M) as [RR ?];
    simpl; erewrite RR; simpl; eauto
  | H : _ |- _ => apply H;
    simpl; repeat des_goal; clarify;
    repeat match goal with
    | RR : ?E = _ |- _ => rewrite RR in *; clear RR
    end;
    simpl in *; repeat des_hyp; clarify;
    rewrite in_app_iff; 
    first [right; eauto; fail | left; eauto; fail]
  | |- ctx_bound_m ub (?t !-> ?v; ?m) =>
    red; unfold update_m;
    intros; simpl in *; 
    repeat des_hyp;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    end; clarify; simpl in *;
    match goal with
    | H : _ |- _ => apply H; eauto; fail
    | H : _ /\ _ |- _ =>
      destruct H as [H ?];
      red in H; eapply H; simpl; eauto; fail
    end
  end;
  repeat match goal with
  | PROJ : project _ ?s = Some ?C |- _ =>
    let RR := fresh "RR" in
    lazymatch goal with
    | _ : dy_to_st C = s |- _ => fail
    | _ => apply project_st_eq in PROJ as RR
    end
  end;
  ss; repeat des_hyp; des; clarify;
  try match goal with
  | ACCESS : In ?v (aread ?m ?addr) |- _ =>
    specialize (BOUNDm addr v ACCESS); ss;
    apply BOUNDm; eauto
  end.
  all: try match goal with
  | IN : In ?sC ?l, BD : context [?l] |- _ =>
    solve [apply BD; right; eauto]
  end.
  all:try solve [rewrite dy_to_st_inject; eauto].
  all:eapply IHSTEP3; eauto.
  all:split; eauto.
  all:match goal with
  | |- ctx_bound_m ?ub (?t !-> ?v; ?m) =>
    red; unfold update_m; ss; ii;
    des_v; ii; repeat des_hyp; des; clarify;
    match goal with
    | _ => solve [eauto]
    | BOUNDm : ctx_bound_m _ ?m,
      ACCESS : In ?v (aread ?m ?addr) |- _ =>
      specialize (BOUNDm addr v ACCESS); ss;
      apply BOUNDm; eauto
    end
  | _ => rrw; eauto
  end.
Qed.

Ltac inv_rs :=
  match goal with
  | H : {|(Rs _ _ _) ~#> _|} |- _ => inversion H
  end.

Lemma reach_ctx_bound `{time T} :
  forall ub e (C : dy_ctx T) m t cf'
         (INIT : ctx_bound_cf ub (Cf e C m t))
         (REACH : {| (Cf e C m t) ~#>* cf' |}),
    ctx_bound_cf ub cf'.
Proof.
  intros.
  remember (Cf e C m t) as cf.
  ginduction REACH; eauto; intros.
  destruct cf; try inv_rs.
  eapply step_ctx_bound in REACHl; eauto.
  destruct cf'; try (eapply IHREACH; eauto; fail).
  inversion REACH; eauto.
  inv_rs.
Qed.

Definition collect_ctx_val `{time T} (v : expr_value T) :=
  match v with
  | Closure (v_fn x e) C => snd (collect_ctx (dy_to_st C) (e_lam x e))
  | Closure (v_ft M s e) C => snd (collect_ctx (dy_to_st C) (m_lam M s e))
  end.

Fixpoint collect_ctx_mem `{time T} (m : memory T) :=
  match m with
  | [] => []
  | (_, v) :: tl => (collect_ctx_val v) ++ (collect_ctx_mem tl)
  end.

Lemma finite_m_then_ctx_bound `{time T} :
  forall (m : memory T),
    ctx_bound_m (collect_ctx_mem m) m.
Proof.
  induction m; intros; simpl; red; intros.
  - des_goal; ss; ii; eauto.
  - repeat des_goal; ss; ii;
    repeat des_hyp; try destruct INvl; try destruct IN; subst;
    rewrite in_app_iff;
    match goal with
    | _ => left; simpl; eauto; fail
    | _ => right; simpl; eauto; fail
    | ACCESS : In ?v (aread ?m ?t) |- _ =>
      right; specialize (IHm t v ACCESS); ss; eauto
    end.
Qed.

(* Finite state space *)
Lemma expr_ctx_bound `{time T} :
  forall e C m t cf'
         (REACH : {|(Cf e C m t) ~#>* cf'|}),
  ctx_bound_cf ((snd (collect_ctx (dy_to_st C) e)) ++ (collect_ctx_mem m)) cf'.
Proof.
  intros.
  eapply reach_ctx_bound; eauto.
  split; simpl; eauto.
  red. intros addr [[x body | M s body] Cv] INvl sC IN;
  rewrite in_app_iff; right;
  assert (ctx_bound_m (collect_ctx_mem m) m) as HINT;
  try (apply finite_m_then_ctx_bound; eauto);
  match goal with
  | ACCESS : In ?v (aread ?m ?t) |- _ =>
    specialize (HINT t v ACCESS); ss; eauto
  end.
  intros. rewrite in_app_iff. eauto.
Qed.

Theorem abstract_sig_finite `{time T} e C m t:
  exists X,
    forall cf (REACH : {|(Cf e C m t) ~#>* cf|}),
    match cf with
    | Cf _ C m _ 
    | Rs (EVal (Closure _ C)) m _
    | Rs (MVal C) m _ =>
      (forall t v (IN : In v (aread m t)),
        match v with
        | Closure _ C => In (dy_to_st C) X
        end) /\
      In (dy_to_st C) X
    end.
Proof.
  exists ((snd (collect_ctx (dy_to_st C) e)) ++ (collect_ctx_mem m)).
  ii. exploit expr_ctx_bound; eauto. unfold ctx_bound_cf. unfold ctx_bound_m.
  intros BOUND.
  repeat des_hyp; des; clarify; split; ii;
  try match goal with
  | ACCESS : In ?v (aread ?m ?t), BOUND : context [aread] |- _ =>
    specialize (BOUND t v ACCESS); repeat des_hyp
  end; eauto using collect_ctx_refl.
Qed.

Fixpoint collect_expr (e : tm) :=
  match e with
  | e_var _
  | m_var _
  | m_empty => [e]
  | m_lam _ _ body
  | e_lam _ body => e :: collect_expr body
  | e_app e1 e2
  | m_app e1 e2 _
  | e_link e1 e2 => e :: collect_expr e1 ++ collect_expr e2
  end.

Definition expr_bound_m `{Eq T} ub (m : memory T) :=
  forall t v (INvl : In v (aread m t)) ee
    (IN : match v with
    | Closure (v_fn x e) _ => In ee (collect_expr (e_lam x e))
    | Closure (v_ft M s e) _ => In ee (collect_expr (m_lam M s e))
    end),
  In ee ub.

Definition expr_bound_cf `{Eq T} ub (cf : config T) :=
  match cf with
  | Cf e C m t =>
    expr_bound_m ub m /\
    forall ee (IN : In ee (collect_expr e)), In ee ub
  | Rs (EVal (Closure (v_fn x e) C)) m t =>
    expr_bound_m ub m /\
    forall ee (IN : In ee (collect_expr (e_lam x e))), In ee ub
  | Rs (EVal (Closure (v_ft M s e) C)) m t =>
    expr_bound_m ub m /\
    forall ee (IN : In ee (collect_expr (m_lam M s e))), In ee ub 
  | Rs (MVal C) m t =>
    expr_bound_m ub m
  end.

Lemma step_expr_bound `{time T} :
  forall ub e (C : dy_ctx T) m t cf'
         (INIT : expr_bound_cf ub (Cf e C m t))
         (STEP : {|(Cf e C m t) ~#> cf'|}),
    expr_bound_cf ub cf'.
Proof.
  intros. remember (Cf e C m t) as cf eqn:CF.
  ginduction STEP; ii; ss; clarify;
  repeat des_goal; des; clarify; eauto;
  try (split; ii; eauto);
  repeat match goal with
  | IH : forall _ e C m t, _ -> _ -> _ |- _ =>
    specialize (IH ub)
  | IH : forall e C m t, _ -> _ -> ?P |- _ =>
    let BD := fresh "BD" in
    assert P as BD;
    [eapply IH; eauto; split; eauto; intros;
    match goal with
    | H : _ |- _ => apply H; fail
    | H : _ |- _ => 
      apply H; simpl; repeat des_goal;
      try rewrite in_app_iff;
      first [try left; eauto; fail | try right; eauto; fail]
    end | clear IH]
  end; des; eauto.
  all:try exploit IHSTEP3; eauto; ii; des; try (split; eauto).
  all:try solve [apply INIT0; rewrite in_app_iff; eauto].
  all:(unfold update_m in *; ss; repeat des_hyp; ss; des; clarify).
  all:eauto.
  all:repeat match goal with
  | |- expr_bound_m _ _ =>
    ii; ss; repeat des_hyp; des; clarify; eauto
  | ACCESS : In ?v (aread ?m ?t), BOUND : expr_bound_m _ ?m |- _ =>
    specialize (BOUND t v ACCESS); ss; eauto
  end.
Qed.

Fixpoint collect_expr_mem `{time T} (m : memory T) :=
  match m with
  | [] => []
  | (_, Closure (v_fn x e) _) :: tl =>
    (collect_expr (e_lam x e)) ++ (collect_expr_mem tl)
  | (_, Closure (v_ft M s e) _) :: tl =>
    (collect_expr (m_lam M s e)) ++ (collect_expr_mem tl)
  end.

Lemma finite_m_then_expr_bound `{time T} :
  forall (m : memory T),
    expr_bound_m (collect_expr_mem m) m.
Proof.
  induction m; intros; simpl; ss.
  repeat des_goal; ss; clarify;
  ii; ss; repeat des_hyp; des; clarify; eauto;
  rewrite in_app_iff; eauto;
  repeat right; eapply IHm; eauto; s; eauto.
Qed.

Lemma reach_expr_bound `{time T} :
  forall ub e (C : dy_ctx T) m t cf'
         (INIT : expr_bound_cf ub (Cf e C m t))
         (REACH : {| (Cf e C m t) ~#>* cf' |}),
    expr_bound_cf ub cf'.
Proof.
  intros.
  remember (Cf e C m t) as cf.
  ginduction REACH; eauto; intros.
  destruct cf; try inv_rs.
  eapply step_expr_bound in REACHl; eauto.
  destruct cf'; try (eapply IHREACH; eauto; fail).
  inversion REACH; eauto.
  inv_rs.
Qed.

(* Finite state space *)
Lemma expr_expr_bound `{time T} :
  forall e C m t cf'
         (REACH : {|(Cf e C m t) ~#>* cf'|}),
  expr_bound_cf (collect_expr e ++ collect_expr_mem m) cf'.
Proof.
  intros.
  eapply reach_expr_bound; eauto.
  split; simpl; eauto.
  red. intros addr [[x body | M s body] Cv] INvl sC IN;
  rewrite in_app_iff; right;
  assert (expr_bound_m (collect_expr_mem m) m) as HINT;
  try (apply finite_m_then_expr_bound; eauto);
  match goal with
  | ACCESS : In ?v (aread ?m ?t) |- _ =>
    specialize (HINT t v ACCESS); ss; eauto
  end.
  intros. rewrite in_app_iff. eauto.
Qed.

Lemma collect_expr_refl e : In e (collect_expr e).
Proof.
  destruct e; ss; eauto.
Qed.

Theorem abstract_expr_finite `{time T} e C m t:
  exists X,
    forall cf (REACH : {|(Cf e C m t) ~#>* cf|}),
    let m := match cf with
    | Cf _ _ m _
    | Rs _ m _ => m
    end in
    (forall t v (IN : In v (aread m t)),
      match v with
      | Closure (v_fn x e) _ => In (e_lam x e) X
      | Closure (v_ft M s e) _ => In (m_lam M s e) X
      end) /\
    match cf with
    | Cf e _ _ _ => In e X
    | Rs (EVal (Closure (v_fn x e) _)) _ _ => In (e_lam x e) X
    | Rs (EVal (Closure (v_ft M s e) _)) _ _ => In (m_lam M s e) X
    | Rs (MVal C) m _ => True
    end.
Proof.
  exists (collect_expr e ++ collect_expr_mem m).
  ii. exploit expr_expr_bound; eauto. unfold expr_bound_cf. unfold expr_bound_m.
  intros BOUND.
  repeat des_hyp; des; clarify; split; ii;
  try match goal with
  | ACCESS : In ?v (aread ?m ?t), BOUND : context [aread] |- _ =>
    specialize (BOUND t v ACCESS); repeat des_hyp
  end; eauto using collect_expr_refl.
Qed.
