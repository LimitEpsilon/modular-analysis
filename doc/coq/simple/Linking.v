From Simple Require Export Sound.
Require Export Coq.Logic.FunctionalExtensionality.

Generalizable Variables T BT AT.

Definition inject_ctx_mem `{Eq T} (Cout : @dy_ctx T) (mem : T -> option expr_value) :=
  fun t => match mem t with None => None | Some v => Some (inject_ctx_v Cout v) end.

Definition delete_ctx_mem `{Eq T} (Cout : @dy_ctx T) (mem : T -> option expr_value) :=
  fun t => match mem t with None => None | Some v => Some (delete_ctx_v Cout v) end.

Lemma delete_ctx_mem_eq :
  forall `{Eq T} (Cout : @dy_ctx T) (mem : T -> option expr_value),
         delete_ctx_mem Cout (inject_ctx_mem Cout mem) = mem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold inject_ctx_mem. unfold delete_ctx_mem.
  destruct (mem x); eauto.
  simpl. destruct e; simpl; rewrite delete_inject_eq.
  eauto.
Qed.

Inductive link `{Eq BT} `{Eq AT} :=
  | L (bf : BT) (af : AT)
.

Definition link_eqb `{EB : Eq BT} `{EA : Eq AT} 
  (t1 : @link BT EB AT EA) (t2 : @link BT EB AT EA) :=
  match t1, t2 with
  | L bf af, L bf' af' =>
    eqb bf bf' && eqb af af'
  end.

Definition link_leb `{EB : Eq BT} `{@OrderT BT EB} `{EA : Eq AT} `{@OrderT AT EA} 
  (t1 : @link BT EB AT EA) (t2 : @link BT EB AT EA) :=
  match t1, t2 with
  | L bf af, L bf' af' =>
    if leb bf bf' then
      if eqb bf bf' then
        leb af af'
      else true
    else false
  end.

Lemma link_leb_refl : 
  forall 
    `{EB : Eq BT} `{EA : Eq AT}
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA} t,
  @link_leb BT EB OB AT EA OA t t = true.
Proof.
  intros. destruct t. simpl. rewrite leb_refl. 
  replace (eqb bf bf) with true.
  apply leb_refl.
  symmetry. apply eqb_eq. eauto.
Qed.

Lemma link_leb_trans :
  forall 
    `{EB : Eq BT} `{EA : Eq AT}
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
    t t' t''
    (LE : @link_leb BT EB OB AT EA OA t t' = true)
    (LE' : @link_leb BT EB OB AT EA OA t' t'' = true),
  link_leb t t'' = true.
Proof.
  intros.
  destruct t as [bf af]; destruct t' as [bf' af'];
  destruct t'' as [bf'' af'']; simpl in *.
  destruct (leb bf bf') eqn:LEbf;
  destruct (leb bf' bf'') eqn:LEbf';
  try (inversion LE; fail);
  try (inversion LE'; fail).
  - destruct (eqb bf bf') eqn:EQbf;
    destruct (eqb bf' bf'') eqn:EQbf';
    try rewrite eqb_eq in *;
    try rewrite eqb_neq in *;
    replace (leb bf bf'') with true;
    try (symmetry; apply leb_trans with (t' := bf'); eauto).
    replace (eqb bf bf'') with true.
    apply leb_trans with (t' := af'); eauto.
    symmetry. apply eqb_eq; subst; eauto.
    replace (eqb bf bf'') with false. eauto.
    symmetry. apply eqb_neq. red. intros. subst.
    apply EQbf'. eauto.
    replace (eqb bf bf'') with false. eauto.
    symmetry. apply eqb_neq. red. intros. subst.
    apply EQbf. eauto.
    replace (eqb bf bf'') with false. eauto.
    symmetry. apply eqb_neq. red. intros. subst.
    apply EQbf. apply leb_sym; eauto.
Qed.

Lemma link_leb_sym :
  forall 
    `{EB : Eq BT} `{EA : Eq AT}
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA} t t'
    (LE : @link_leb BT EB OB AT EA OA t t' = true)
    (LE' : @link_leb BT EB OB AT EA OA t' t = true),
  t = t'.
Proof.
  intros.
  destruct t as [bf af]; destruct t' as [bf' af'];
  simpl in *;
  destruct (leb bf bf') eqn:LEbf;
  destruct (leb bf' bf) eqn:LEbf';
  try (inversion LE; fail);
  try (inversion LE'; fail).
  assert (bf' = bf) as RR.
  apply leb_sym; eauto.
  rewrite RR in *.
  replace (eqb bf bf) with true in *.
  assert (af = af').
  apply leb_sym; eauto. subst; eauto.
  symmetry. apply eqb_eq. eauto.
Qed.

Lemma link_eqb_eq :
  forall `{EB : Eq BT} `{EA : Eq AT} t t',
  @link_eqb BT EB AT EA t t' = true <-> t = t'.
Proof.
  intros.
  destruct t as [bf af]; destruct t' as [bf' af'];
  simpl in *;
  split; intro EQ.
  destruct (eqb bf bf') eqn:EQbf;
  destruct (eqb af af') eqn:EQaf;
  try (inversion EQ; fail).
  rewrite eqb_eq in EQbf.
  rewrite eqb_eq in EQaf. subst; eauto.
  inversion EQ; subst.
  replace (eqb bf' bf') with true;
  try replace (eqb af' af') with true;
  eauto; symmetry; apply eqb_eq; eauto.
Qed.

Lemma link_eqb_neq :
  forall `{EB : Eq BT} `{EA : Eq AT} t t',
  @link_eqb BT EB AT EA t t' = false <-> t <> t'.
Proof.
  intros.
  split; intro NEQ.
  red. intros EQ.
  assert (link_eqb t t' = true) as RR. apply link_eqb_eq. eauto.
  rewrite RR in NEQ. inversion NEQ.
  refl_bool. intros contra. rewrite link_eqb_eq in contra.
  apply NEQ; eauto.
Qed.

#[export] Instance LinkEq `{EB : Eq BT} `{EA : Eq AT} :
  Eq (@link BT EB AT EA) :=
{
  eqb := link_eqb;
  eqb_eq := link_eqb_eq;
  eqb_neq := link_eqb_neq
}.

#[export] Instance LinkOrderT `{EB : Eq BT} `{EA : Eq AT} `{OB : @OrderT BT EB} `{OA : @OrderT AT EA} :
  @OrderT (@link BT EB AT EA) LinkEq :=
  {
    leb := link_leb;
    leb_refl := link_leb_refl;
    leb_trans := link_leb_trans;
    leb_sym := link_leb_sym
  }.

Fixpoint filter_ctx_bf
  `{OrderT BT} `{EA : Eq AT} (final : BT)
  (C : @dy_ctx (@link BT _ AT EA)) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x (L bf af) C' =>
    let filtered := filter_ctx_bf final C' in
    if leb final bf then filtered else dy_c_lam x bf filtered
  | dy_c_lete x (L bf af) C' =>
    let filtered := filter_ctx_bf final C' in
    if leb final bf then filtered else dy_c_lete x bf filtered
  | dy_c_letm M C' C'' =>
    dy_c_letm M (filter_ctx_bf final C') (filter_ctx_bf final C'')
  end.

Fixpoint filter_ctx_af
  `{OrderT BT} `{EA : Eq AT} (final : BT)
  (C : @dy_ctx (@link BT _ AT EA)) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x (L bf af) C' =>
    let filtered := filter_ctx_af final C' in
    if leb final bf then dy_c_lam x af filtered else filtered
  | dy_c_lete x (L bf af) C' =>
    let filtered := filter_ctx_af final C' in
    if leb final bf then dy_c_lete x af filtered else filtered
  | dy_c_letm M C' C'' =>
    dy_c_letm M (filter_ctx_af final C') (filter_ctx_af final C'')
  end.

Definition filter_v_bf 
  `{OrderT BT} `{EA : Eq AT} (final : BT)
  (v : @expr_value (@link BT _ AT EA)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_bf final C)
  end.

Definition filter_v_af
  `{OrderT BT} `{EA : Eq AT} (final : BT)
  (v : @expr_value (@link BT _ AT EA)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_af final C)
  end.

Definition filter_mem_bf
  `{OrderT BT} `{EA : Eq AT} (final : BT) (init : AT)
  (mem : (@link BT _ AT EA) -> option (@expr_value (@link BT _ AT EA))) :=
  fun t =>
    match mem (L t init) with
    | Some v => Some (filter_v_bf final v)
    | None => None
    end.

Definition filter_mem_af
  `{OrderT BT} `{EA : Eq AT} (final : BT)
  (mem : (@link BT _ AT EA) -> option (@expr_value (@link BT _ AT EA))) :=
  fun t =>
    match mem (L final t) with
    | Some v => Some (filter_v_af final v)
    | None => None
    end.

Fixpoint lift_ctx_bf `{EB : Eq BT} `{EA : Eq AT} (init : AT) (C : @dy_ctx BT)
  : @dy_ctx (@link BT EB AT EA) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (L t init) (lift_ctx_bf init C')
  | dy_c_lete x t C' => dy_c_lete x (L t init) (lift_ctx_bf init C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_bf init C') (lift_ctx_bf init C'')
  end.

Fixpoint lift_ctx_af `{EB : Eq BT} `{EA : Eq AT} (final : BT) (C : @dy_ctx AT)
  : @dy_ctx (@link BT EB AT EA) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (L final t) (lift_ctx_af final C')
  | dy_c_lete x t C' => dy_c_lete x (L final t) (lift_ctx_af final C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_af final C') (lift_ctx_af final C'')
  end.

Definition lift_v_af `{EB : Eq BT} `{EA : Eq AT} (final : BT) (v : @expr_value AT)
  : @expr_value (@link BT EB AT EA) :=
  match v with
  | Closure x e C => Closure x e (lift_ctx_af final C)
  end.

Definition link_tick `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT)
  C st x v :=
  match st with
  | ST mem (L bf af) =>
    if leb final bf then
      let Cout := lift_ctx_bf init Cout in
      L bf
        (tick (filter_ctx_af final (delete_ctx Cout C))
              (ST (filter_mem_af final (delete_ctx_mem Cout mem)) af)
              x (filter_v_af final (delete_ctx_v Cout v)))
    else
      L (tick (filter_ctx_bf final C)
              (ST (filter_mem_bf final init mem) bf)
              x (filter_v_bf final v)) af
  end.

Lemma link_tick_lt `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT):
  forall C mem t x v, t < link_tick final init Cout C (ST mem t) x v.
Proof.
  destruct t; unfold "<"; simpl.
  intro_refl.
  destruct (leb final bf) eqn:LE; simpl;
  try rewrite leb_refl; try rewrite t_refl; simpl.
  - intros. split; try apply tick_lt.
  - intros. 
    replace (leb bf
    (tick (filter_ctx_bf final C) (ST (filter_mem_bf final init mem) bf)
       x (filter_v_bf final v))) with true; try (symmetry; apply tick_lt).
    replace (eqb bf
    (tick (filter_ctx_bf final C) (ST (filter_mem_bf final init mem) bf)
       x (filter_v_bf final v))) with false; try (symmetry; apply tick_lt).
    eauto.
Qed.

#[export] Instance link_time `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) : (@time (@link BT _ AT _) _ _) :=
  {
    tick := link_tick final init Cout;
    tick_lt := link_tick_lt final init Cout
  }.

Definition link_mem `{OrderT BT} `{Eq AT}
  (bmem : BT -> option (@expr_value BT)) (final : BT) (init : AT) (Cout : @dy_ctx BT)
  (amem : AT -> option (@expr_value AT)) : (@link BT _ AT _) -> option expr_value :=
  fun t =>
    match t with
    | L bf af =>
      if eqb final bf then
        let Cout := lift_ctx_bf init Cout in
        match amem af with
        | Some (Closure x e C) => Some (Closure x e (Cout<|lift_ctx_af final C|>))
        | None => None
        end
      else if leb bf final then
        match bmem bf with
        | Some (Closure x e C) => Some (Closure x e (lift_ctx_bf init C))
        | None => None
        end
      else None
    end.

Lemma filter_lift_eq_af `{time BT} `{time AT} (final : BT):
  forall (C : @dy_ctx AT),
    filter_ctx_af final (lift_ctx_af final C) = C.
Proof.
  induction C; simpl; try rewrite IHC; try rewrite leb_refl; eauto.
  rewrite IHC2. rewrite IHC1. eauto.
Qed.

Lemma filter_lift_eq_bf `{time BT} `{time AT} (final : BT) (init : AT) :
  forall (C : @dy_ctx BT) (BOUND : dy_ctx_bound C final),
    filter_ctx_bf final (lift_ctx_bf init C) = C.
Proof.
  induction C; intros; simpl in *;
  try rewrite IHC; try apply BOUND; 
  try replace (leb final tx) with false; eauto;
  try destruct BOUND as [[LE NEQ] BOUND];
  try (symmetry; refl_bool; intros contra;
      assert (final = tx); try apply leb_sym; try apply contra; try apply LE;
      subst; intro_refl; rewrite t_refl in NEQ; inversion NEQ).
  rewrite IHC2; try rewrite IHC1; eauto; apply BOUND.
Qed.

Lemma filter_delete_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT):
  forall bmem amem,
  filter_mem_af final
    (delete_ctx_mem (lift_ctx_bf init Cout)
    (link_mem bmem final init Cout amem)) = amem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold filter_mem_af.
  unfold delete_ctx_mem. simpl. intro_refl. rewrite t_refl.
  remember (lift_ctx_bf init Cout) as vout eqn:E. clear E.
  remember (amem x) as o eqn:E. clear E.
  destruct o; eauto. destruct e. simpl.
  rewrite delete_inject_eq. rewrite filter_lift_eq_af. eauto.
Qed.

Lemma link_tick_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) :
  forall bmem C amem t x v,
    link_tick final init Cout ((lift_ctx_bf init Cout)<|(lift_ctx_af final C)|>)
                (ST (link_mem bmem final init Cout amem) (L final t)) x 
                (inject_ctx_v (lift_ctx_bf init Cout) (lift_v_af final v)) =
    L final (tick C (ST amem t) x v).
Proof.
  intros. destruct v. unfold inject_ctx_v. simpl.
  rewrite delete_inject_eq.
  rewrite delete_inject_eq.
  rewrite filter_delete_eq.
  rewrite filter_lift_eq_af. rewrite filter_lift_eq_af.
  rewrite leb_refl.
  reflexivity.
Qed.

Lemma link_update_m_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT):
  forall bmem amem t v (BOUND : time_bound Cout (ST bmem final)),
  (L final t !-> inject_ctx_v (lift_ctx_bf init Cout) (lift_v_af final v);
    (link_mem bmem final init Cout amem)) =
    link_mem bmem final init Cout (t !-> v; amem).
Proof.
  intros. apply functional_extensionality.
  intros. unfold update_m. destruct v. simpl.
  destruct x; simpl; eauto.
  destruct (eqb bf final) eqn:EQb; destruct (eqb af t) eqn:EQa; simpl; eauto.
  rewrite eqb_eq in EQb. rewrite eqb_eq in EQa.
  subst. intro_refl. rewrite t_refl. eauto.
  destruct (eqb final bf) eqn:EQb'; eauto.
  rewrite eqb_eq in EQb'. subst.
  rewrite eqb_neq in EQb. contradict.
Qed.

Lemma lift_addr_x `{time BT} `{time AT} (final : BT) :
  forall (C : @dy_ctx AT) x,
    addr_x (lift_ctx_af final C) x =
      match addr_x C x with
      | Some addr => Some (L final addr)
      | None => None
      end.
Proof.
  induction C; simpl; eauto;
  intros;
  destruct (eq_eid x0 x); rewrite IHC;
  destruct (addr_x C x0); eauto.
Qed.

Lemma lift_ctx_M `{time BT} `{time AT} (final : BT) :
  forall (C : @dy_ctx AT) M,
    ctx_M (lift_ctx_af final C) M =
      match ctx_M C M with
      | Some CM => Some (lift_ctx_af final CM)
      | None => None
      end.
Proof.
  induction C; simpl; eauto;
  intros.
  destruct (eq_mid M0 M); rewrite IHC2;
  destruct (ctx_M C2 M0); eauto.
Qed.

Lemma lift_plugin_af `{time BT} `{time AT} (final : BT) :
  forall (C C' : @dy_ctx AT),
    lift_ctx_af final (C[|C'|]) = (lift_ctx_af final C [|lift_ctx_af final C'|]).
Proof.
  induction C; simpl; intros; try rewrite IHC; eauto.
  rewrite IHC2. eauto.
Qed.

Lemma link_eval_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) :
  forall bmem (BOUND : time_bound Cout (ST bmem final))
         C st e v st'
         (EVAL : @EvalR AT _ _ _ C st e v st'),
    let inject_C := (lift_ctx_bf init Cout) <|(lift_ctx_af final C)|> in
    let inject_v :=
      match v with
      | EVal ev => EVal (inject_ctx_v (lift_ctx_bf init Cout) (lift_v_af final ev))
      | MVal C_v => MVal ((lift_ctx_bf init Cout)<|(lift_ctx_af final C_v)|>)
      end in
    let inject_st :=
      match st with
      | ST amem t => ST (link_mem bmem final init Cout amem) (L final t)
      end in
    let inject_st' :=
      match st' with
      | ST amem' t' => ST (link_mem bmem final init Cout amem') (L final t')
      end in
    @EvalR (@link BT _ AT _) _ _ (link_time final init Cout)
      inject_C inject_st e inject_v inject_st'.
Proof.
  intros. induction EVAL;
  try destruct v; try destruct st; try destruct st'; try destruct st'';
  try (destruct inject_v eqn:INJv; inversion INJv; subst);
  try (destruct inject_st eqn:INJst; inversion INJst; subst);
  try (destruct inject_st' eqn:INJst'; inversion INJst'; subst); eauto.
  - inversion STATE; subst.
    eapply Eval_var_e; eauto.
    pose proof (inject_ctx_addr_x x (lift_ctx_bf init Cout) (lift_ctx_af final C)) as RR.
    rewrite lift_addr_x in RR.
    rewrite <- ADDR in RR. symmetry. apply RR.
    unfold link_mem. intro_refl. rewrite t_refl.
    rewrite <- ACCESS. eauto.
  - destruct st_v. destruct arg.
    eapply Eval_app. apply IHEVAL1. apply IHEVAL2.
    pose proof (link_tick_eq final init Cout bmem C mem t x (Closure x1 e3 C1)) as RR.
    simpl in *. subst inject_C.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq final init Cout bmem mem t (Closure x1 e3 C1) BOUND) as RR. simpl in RR.
    rewrite RR. clear RR.
    replace (dy_c_lam x (L final t) ([||])) with (map_inject (lift_ctx_bf init Cout) (dy_c_lam x (L final t) ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. rewrite lift_plugin_af in IHEVAL3. eauto.
  - pose proof (inject_ctx_ctx_M M (lift_ctx_bf init Cout) (lift_ctx_af final C)) as RR.
    rewrite lift_ctx_M in RR.
    rewrite <- ACCESS in RR.
    eapply Eval_var_m; eauto.
  - eapply Eval_lete; eauto.
    pose proof (link_tick_eq final init Cout bmem C mem t x (Closure x0 e0 C0)) as RR.
    simpl in *. subst inject_C.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq final init Cout bmem mem t (Closure x0 e0 C0) BOUND) as RR. simpl in RR.
    rewrite RR. clear RR.
    replace (dy_c_lete x (L final t) ([||])) with (map_inject (lift_ctx_bf init Cout) (dy_c_lete x (L final t) ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. rewrite lift_plugin_af in IHEVAL2. eauto.
  - eapply Eval_letm; eauto.
    assert (inject_C [|dy_c_letm M (lift_ctx_bf init Cout <| lift_ctx_af final C' |>) ([||])|] =
            (lift_ctx_bf init Cout <| lift_ctx_af final (C [|dy_c_letm M C' ([||])|]) |>)) as RR. 
    { subst inject_C. rewrite lift_plugin_af.
      rewrite <- plugin_inject_assoc. simpl. eauto. } 
    rewrite RR. clear RR. simpl in *. exact IHEVAL2.
Qed.

Lemma link_reach_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) :
  forall bmem (BOUND : time_bound Cout (ST bmem final))
         C st e C' st' e'
         (REACH : @one_reach AT _ _ _ C st e C' st' e'),
    let inject_C := (lift_ctx_bf init Cout) <|(lift_ctx_af final C)|> in
    let inject_C' := (lift_ctx_bf init Cout) <|(lift_ctx_af final C')|> in
    let inject_st :=
      match st with
      | ST amem t => ST (link_mem bmem final init Cout amem) (L final t)
      end in
    let inject_st' :=
      match st' with
      | ST amem' t' => ST (link_mem bmem final init Cout amem') (L final t')
      end in
    @one_reach (@link BT _ AT _) _ _ (link_time final init Cout)
      inject_C inject_st e inject_C' inject_st' e'.
Proof.
  intros. destruct REACH; try destruct st.
  - apply one_appl.
  - destruct st_lam.
    eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in FN; eauto.
    eapply one_appr; simpl in *; eauto.
  - eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in FN; eauto.
    eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in ARG; eauto.
    destruct st_lam. subst inject_C inject_st inject_C' inject_st'.
    rewrite <- link_update_m_eq; eauto. rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    replace (L final (tick C (ST mem t) x arg)) with 
      (link_tick final init Cout (lift_ctx_bf init Cout <| lift_ctx_af final C |>)
        (ST (link_mem bmem final init Cout mem) (L final t)) x (inject_ctx_v (lift_ctx_bf init Cout) (lift_v_af final arg))).
    apply (@one_appbody (@link BT _ AT _) _ _ (link_time final init Cout) 
                        (lift_ctx_bf init Cout <| lift_ctx_af final C |>)
                        (ST (link_mem bmem final init Cout mem0) (L final t0))
                        e1 e2 x e (lift_ctx_bf init Cout <| lift_ctx_af final C_lam |>)
                        (ST (link_mem bmem final init Cout mem1) (L final t1))
                        (inject_ctx_v (lift_ctx_bf init Cout) (lift_v_af final arg))
                        (link_mem bmem final init Cout mem) (L final t)). eauto. eauto.
    destruct arg. simpl. rewrite leb_refl.
    repeat rewrite delete_inject_eq. repeat rewrite filter_delete_eq. repeat rewrite filter_lift_eq_af. eauto.
  - apply one_linkl.
  - destruct st_m.
    eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in MOD; eauto.
    eapply one_linkr; simpl in *; eauto.
  - apply one_letel.
  - eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in EVALx; eauto.
    subst inject_C inject_st inject_C' inject_st'.
    rewrite <- link_update_m_eq; eauto. rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    replace (L final (tick C (ST mem t) x v)) with 
      (link_tick final init Cout (lift_ctx_bf init Cout <| lift_ctx_af final C |>)
        (ST (link_mem bmem final init Cout mem) (L final t)) x (inject_ctx_v (lift_ctx_bf init Cout) (lift_v_af final v))).
    apply (@one_leter (@link BT _ AT _) _ _ (link_time final init Cout) 
                      (lift_ctx_bf init Cout <| lift_ctx_af final C |>)
                      (ST (link_mem bmem final init Cout mem0) (L final t0))
                      x e m 
                      (inject_ctx_v (lift_ctx_bf init Cout) (lift_v_af final v))
                      (link_mem bmem final init Cout mem) (L final t)). eauto.
    destruct v. simpl. rewrite leb_refl.
    repeat rewrite delete_inject_eq. repeat rewrite filter_delete_eq. repeat rewrite filter_lift_eq_af. eauto.
  - apply one_letml.
  - destruct st_M.
    eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in EVALM; eauto.
    subst inject_C inject_st inject_C' inject_st'.
    rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    eapply one_letmr; simpl in *; eauto.
Qed.
