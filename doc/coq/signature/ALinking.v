From Signature Require Export Abstract.
Require Export Coq.Logic.FunctionalExtensionality.

Generalizable Variables T BT AT.

Definition plugin_ctx_mem `{Eq T} (Cout : @dy_ctx T) (mem : T -> list expr_value) :=
  fun t => map (plugin_ctx_v Cout) (mem t).

Definition delete_ctx_mem `{Eq T} (Cout : @dy_ctx T) (mem : T -> list expr_value) :=
  fun t => map (delete_ctx_v Cout) (mem t).

Lemma delete_ctx_mem_eq :
  forall `{Eq T} (Cout : @dy_ctx T) (mem : T -> list expr_value),
         delete_ctx_mem Cout (plugin_ctx_mem Cout mem) = mem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold plugin_ctx_mem. unfold delete_ctx_mem.
  remember (mem x) as l. clear Heql x mem. revert Cout.
  induction l; try reflexivity. intros.
  destruct a; simpl;
  rewrite delete_eq;
  rewrite IHl; reflexivity.
Qed.

Inductive link {BT AT} :=
  | BF (t : BT)
  | AF (t : AT)
.

Definition link_eqb `{Eq BT} `{Eq AT} (t t' : @link BT AT) :=
  match t, t' with
  | BF t, BF t' => eqb t t'
  | AF t, AF t' => eqb t t'
  | _, _ => false
  end.

Lemma link_eqb_eq `{Eq BT} `{Eq AT} :
  forall (t t' : @link BT AT), link_eqb t t' = true <-> t = t'.
Proof.
  intros.
  destruct t; destruct t'; simpl; split; intros EQ; 
  try rewrite eqb_eq in *;
  try inversion EQ;
  subst; eauto.
Qed.

Lemma link_eqb_neq `{Eq BT} `{Eq AT} :
  forall (t t' : @link BT AT), link_eqb t t' = false <-> t <> t'.
Proof.
  intros. split; intros NEQ.
  - red. intros contra. rewrite <- link_eqb_eq in contra.
    rewrite NEQ in contra. inversion contra.
  - refl_bool. intros contra. rewrite link_eqb_eq in contra.
    apply NEQ. eauto.
Qed.

#[export] Instance link_eq `{Eq BT} `{Eq AT} : Eq (@link BT AT) :=
  {
    eqb := link_eqb;
    eqb_eq := link_eqb_eq;
    eqb_neq := link_eqb_neq
  }.

Fixpoint filter_ctx_bf {BT AT} (C : @dy_ctx (@link BT AT)) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' =>
    match t with
    | BF t => dy_binde x t (filter_ctx_bf C')
    | AF t => filter_ctx_bf C'
    end
  | dy_bindm M C' C'' => dy_bindm M (filter_ctx_bf C') (filter_ctx_bf C'')
  end.

Fixpoint filter_ctx_af {BT AT} (C : @dy_ctx (@link BT AT)) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' =>
    match t with
    | AF t => dy_binde x t (filter_ctx_af C')
    | BF t => filter_ctx_af C'
    end
  | dy_bindm M C' C'' => dy_bindm M (filter_ctx_af C') (filter_ctx_af C'')
  end.

Definition filter_v_bf {BT AT} (v : @expr_value (@link BT AT)) :=
  match v with
  | Fun x e C => Fun x e (filter_ctx_bf C)
  | Func M s e C => Func M s e (filter_ctx_bf C)
  end.

Definition filter_v_af {BT AT} (v : @expr_value (@link BT AT)) :=
  match v with
  | Fun x e C => Fun x e (filter_ctx_af C)
  | Func M s e C => Func M s e (filter_ctx_af C)
  end.

Definition filter_mem_bf {BT AT} (mem : (@link BT AT) -> list (@expr_value (@link BT AT))) :=
  fun t => map filter_v_bf (mem (BF t))
.

Definition filter_mem_af {BT AT} (mem : (@link BT AT) -> list (@expr_value (@link BT AT))) :=
  fun t => map filter_v_af (mem (AF t))
.

Fixpoint lift_ctx_bf {BT AT} C : @dy_ctx (@link BT AT) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' => dy_binde x (BF t) (lift_ctx_bf C')
  | dy_bindm M C' C'' => dy_bindm M (lift_ctx_bf C') (lift_ctx_bf C'')
  end.

Definition lift_v_bf {BT AT} v : @expr_value (@link BT AT) :=
  match v with
  | Fun x e C => Fun x e (lift_ctx_bf C)
  | Func M s e C => Func M s e (lift_ctx_bf C)
  end.

Fixpoint lift_ctx_af {BT AT} C : @dy_ctx (@link BT AT) :=
  match C with
  | [||] => [||]
  | dy_binde x t C' => dy_binde x (AF t) (lift_ctx_af C')
  | dy_bindm M C' C'' => dy_bindm M (lift_ctx_af C') (lift_ctx_af C'')
  end.

Definition lift_v_af {BT AT} v : @expr_value (@link BT AT) :=
  match v with
  | Fun x e C => Fun x e (lift_ctx_af C)
  | Func M s e C => Func M s e (lift_ctx_af C)
  end.

Definition link_tick `{Eq BT} `{time AT} (Cout : @dy_ctx BT) :=
  fun C st x v =>
    match st with
    | ST mem t =>
      match t with
      | BF t => BF t
      | AF t =>
        let Cout := lift_ctx_bf Cout in
        AF
        (tick (filter_ctx_af (delete Cout C))
                (ST (filter_mem_af (delete_ctx_mem Cout mem)) t)
                x (filter_v_af (delete_ctx_v Cout v)))
      end
    end.

#[export] Instance link_time `{Eq BT} `{time AT} (Cout : @dy_ctx BT) : (@time (@link BT AT) (@link_eq BT _ AT _)) :=
  {
    tick := link_tick Cout
  }.

Definition link_mem `{Eq BT} `{Eq AT}
  (bmem : BT -> list (@expr_value BT)) (Cout : @dy_ctx BT)
  (amem : AT -> list (@expr_value AT)) : (@link BT AT) -> list (@expr_value (@link BT AT)):=
  fun t =>
    match t with
    | BF t => map lift_v_bf (bmem t)
    | AF t => map (plugin_ctx_v (lift_ctx_bf Cout)) (map (lift_v_af) (amem t))
    end.

Lemma filter_lift_eq_af {BT AT} :
  forall (C : @dy_ctx AT),
    filter_ctx_af (@lift_ctx_af BT AT C) = C.
Proof.
  induction C; simpl; try rewrite IHC; eauto.
  rewrite IHC2. rewrite IHC1. eauto.
Qed.

Lemma filter_lift_eq_bf {BT AT} :
  forall (C : @dy_ctx BT),
    filter_ctx_bf (@lift_ctx_bf BT AT C) = C.
Proof.
  induction C; simpl; try rewrite IHC; eauto.
  rewrite IHC2. rewrite IHC1. eauto.
Qed.

Lemma filter_delete_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT):
  forall bmem amem,
  filter_mem_af
    (delete_ctx_mem (lift_ctx_bf Cout)
    (link_mem bmem Cout amem)) = amem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold filter_mem_af.
  unfold delete_ctx_mem. simpl.
  remember (lift_ctx_bf Cout) as vout eqn:E. clear E.
  remember (amem x) as l eqn:E. clear E.
  induction l; simpl; eauto.
  rewrite IHl; destruct a; simpl;
  rewrite delete_eq; rewrite filter_lift_eq_af; reflexivity.
Qed.

Lemma link_tick_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT) :
  forall bmem C amem t x v,
    link_tick Cout ((lift_ctx_bf Cout)[|(lift_ctx_af C)|])
                (ST (link_mem bmem Cout amem) (AF t)) x 
                (plugin_ctx_v (lift_ctx_bf Cout) (lift_v_af v)) =
    AF (tick C (ST amem t) x v).
Proof.
  intros. destruct v; unfold plugin_ctx_v; simpl;
  rewrite delete_eq;
  rewrite delete_eq;
  rewrite filter_delete_eq;
  rewrite filter_lift_eq_af; rewrite filter_lift_eq_af;
  reflexivity.
Qed.

Lemma link_update_m_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT):
  forall bmem amem t v,
  (AF t !#-> plugin_ctx_v (lift_ctx_bf Cout) (lift_v_af v);
    (link_mem bmem Cout amem)) =
    link_mem bmem Cout (t !#-> v; amem).
Proof.
  intros. apply functional_extensionality.
  intros. unfold update_m. destruct v; simpl;
  destruct x; simpl; eauto;
  destruct (eqb t0 t); eauto.
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
  destruct (eq_eid x0 x); rewrite IHC;
  destruct (addr_x C x0); eauto.
Qed.

Lemma lift_ctx_M {BT AT} :
  forall (C : @dy_ctx AT) M,
    ctx_M (lift_ctx_af C : @dy_ctx (@link BT AT)) M =
      match ctx_M C M with
      | Some CM => Some (lift_ctx_af CM)
      | None => None
      end.
Proof.
  induction C; simpl; eauto;
  intros.
  destruct (eq_mid M0 M); rewrite IHC2;
  destruct (ctx_M C2 M0); eauto.
Qed.

Lemma lift_plugin_af {BT AT} :
  forall (C C' : @dy_ctx AT),
    @lift_ctx_af BT AT (C[|C'|]) = (lift_ctx_af C [|lift_ctx_af C'|]).
Proof.
  induction C; simpl; intros; try rewrite IHC; eauto.
  rewrite IHC2. eauto.
Qed.

Lemma project_lift {BT AT} :
  forall (s : st_ctx) (C CM : @dy_ctx AT) (PROJ : Some CM = project C s),
    Some (lift_ctx_af CM : @dy_ctx (@link BT AT)) = project (lift_ctx_af C) s.
Proof.
  intros s. induction s; intros; inversion PROJ; subst; eauto.
  - simpl. destruct (addr_x C x) eqn:ADDR; inversion H0.
    pose proof (@lift_addr_x BT AT C x) as RR. rewrite ADDR in RR.
    rewrite RR.
    destruct (project C s) eqn:PROJs; inversion H0.
    erewrite <- IHs; eauto. simpl. eauto.
  - simpl. destruct (ctx_M C M) eqn:CTX; inversion H0.
    pose proof (@lift_ctx_M BT AT C M) as RR. rewrite CTX in RR.
    rewrite RR.
    destruct (project d s1) eqn:PROJs1; inversion H0.
    destruct (project C s2) eqn:PROJs2; inversion H2.
    erewrite <- IHs1; eauto.
    erewrite <- IHs2; eauto. simpl. eauto.
Qed.

Lemma link_eval_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT) :
  forall bmem C st e v st'
         (EVAL : @EvalR AT _ _ C st e v st'),
    let inject_C := (lift_ctx_bf Cout) [|(lift_ctx_af C)|] in
    let inject_v :=
      match v with
      | EVal ev => EVal (plugin_ctx_v (lift_ctx_bf Cout) (lift_v_af ev))
      | MVal C_v => MVal ((lift_ctx_bf Cout)[|(lift_ctx_af C_v)|])
      end in
    let inject_st :=
      match st with
      | ST amem t => ST (link_mem bmem Cout amem) (AF t)
      end in
    let inject_st' :=
      match st' with
      | ST amem' t' => ST (link_mem bmem Cout amem') (AF t')
      end in
    @EvalR (@link BT AT) _ (link_time Cout)
      inject_C inject_st e inject_v inject_st'.
Proof.
  intros. induction EVAL;
  try destruct st; try destruct st'; try destruct st'';
  try (destruct inject_v eqn:INJv; inversion INJv; subst);
  try (destruct inject_st eqn:INJst; inversion INJst; subst);
  try (destruct inject_st' eqn:INJst'; inversion INJst'; subst); eauto.
  - inversion STATE; subst.
    eapply Eval_e_var; eauto.
    pose proof (plugin_ctx_addr_x x (lift_ctx_bf Cout) (lift_ctx_af C)) as RR.
    rewrite lift_addr_x in RR.
    rewrite <- ADDR in RR. symmetry. apply RR.
    unfold link_mem. 
    remember (mem0 addr) as l.
    clear Heql inject_C C mem0 x addr t0 inject_st' INJst' STATE inject_st INJst ADDR inject_v INJv.
    induction l; simpl; intros; eauto.
    destruct ACCESS as [L | R].
    left. rewrite L. eauto.
    right. apply IHl. eauto.
  - destruct st_v.
    eapply Eval_e_app_fn; try apply IHEVAL1; try apply IHEVAL2.
    pose proof (link_tick_eq Cout bmem C mem t x arg) as RR.
    simpl in *. subst inject_C.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq Cout bmem mem t arg) as RR. simpl in RR.
    rewrite RR. clear RR.
    rewrite <- dy_plugin_assoc. rewrite lift_plugin_af in IHEVAL3. eauto.
  - destruct st_v. destruct st_arg.
    eapply Eval_e_app_ft with (CM := lift_ctx_af CM);
    try apply IHEVAL1; try apply IHEVAL2;
    try (rewrite <- dy_plugin_assoc; rewrite lift_plugin_af in IHEVAL3; eauto).
    pose proof (@project_lift BT AT) as RR.
    specialize (RR s_lam arg CM PROJ).
    rewrite RR. erewrite plugin_project_eq; eauto. 
  - pose proof (plugin_ctx_ctx_M M (lift_ctx_bf Cout) (lift_ctx_af C)) as RR.
    rewrite lift_ctx_M in RR.
    rewrite <- ACCESS in RR. subst inject_C.
    rewrite lift_plugin_af. rewrite dy_plugin_assoc.
    eapply Eval_m_var; eauto.
  - destruct st_v.
    pose proof (@project_lift BT AT s v proj_v PROJv) as HINT.
    assert ((lift_ctx_bf Cout [|lift_ctx_af (C [|proj_v|])|]) = 
            ((lift_ctx_bf Cout [|lift_ctx_af C|]) [|lift_ctx_af proj_v|])) as RR.
    { rewrite lift_plugin_af. rewrite dy_plugin_assoc. eauto. }
    rewrite RR. clear RR.
    eapply Eval_m_app_fn with (v := lift_ctx_bf Cout [|lift_ctx_af v|]);
    try apply IHEVAL1; try apply IHEVAL2; eauto.
    pose proof (link_tick_eq Cout bmem C mem t x arg) as RR.
    simpl in *. subst inject_C.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq Cout bmem mem t arg) as RR. simpl in RR.
    rewrite RR. clear RR.
    rewrite <- dy_plugin_assoc. rewrite lift_plugin_af in IHEVAL3. eauto.
    erewrite plugin_project_eq; eauto.
  - destruct st_v. destruct st_arg.
    pose proof (@project_lift BT AT s_lam arg CM PROJ) as HINT.
    pose proof (@project_lift BT AT s v proj_v PROJv) as HINTv.
    assert ((lift_ctx_bf Cout [|lift_ctx_af (C [|proj_v|])|]) = 
            ((lift_ctx_bf Cout [|lift_ctx_af C|]) [|lift_ctx_af proj_v|])) as RR.
    { rewrite lift_plugin_af. rewrite dy_plugin_assoc. eauto. }
    rewrite RR. clear RR.
    eapply Eval_m_app_ft with 
      (v := lift_ctx_bf Cout [|lift_ctx_af v|])
      (CM := lift_ctx_af CM);
    try apply IHEVAL1; try apply IHEVAL2; eauto;
    try (erewrite plugin_project_eq; eauto).
    rewrite <- dy_plugin_assoc. rewrite lift_plugin_af in IHEVAL3. eauto.
Qed.
