From Simple Require Export Concrete.
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
  `{EB : Eq BT} `{EA : Eq AT}
  (C : @dy_ctx (@link BT EB AT EA)) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' =>
    match t with
    | L bf af => dy_c_lam x bf (filter_ctx_bf C')
    end
  | dy_c_lete x t C' =>
    match t with
    | L bf af => dy_c_lete x bf (filter_ctx_bf C')
    end
  | dy_c_letm M C' C'' =>
    dy_c_letm M (filter_ctx_bf C') (filter_ctx_bf C'')
  end.

Fixpoint filter_ctx_af
  `{EB : Eq BT} `{EA : Eq AT}
  (C : @dy_ctx (@link BT EB AT EA)) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' =>
    match t with
    | L bf af => dy_c_lam x af (filter_ctx_af C')
    end
  | dy_c_lete x t C' =>
    match t with
    | L bf af => dy_c_lete x af (filter_ctx_af C')
    end
  | dy_c_letm M C' C'' =>
    dy_c_letm M (filter_ctx_af C') (filter_ctx_af C'')
  end.

Definition filter_mem_bf
  `{EB : Eq BT} `{EA : Eq AT} (init : AT)
  (mem : (@link BT EB AT EA) -> option (@expr_value (@link BT EB AT EA))) :=
  fun t =>
    match mem (L t init) with
    | Some (Closure x e C) => Some (Closure x e (filter_ctx_bf C))
    | None => None
    end.

Definition filter_mem_af
  `{EB : Eq BT} `{EA : Eq AT} (final : BT)
  (mem : (@link BT EB AT EA) -> option (@expr_value (@link BT EB AT EA))) :=
  fun t =>
    match mem (L final t) with
    | Some (Closure x e C) => Some (Closure x e (filter_ctx_af C))
    | None => None
    end.

Definition filter_v_bf 
  `{EB : Eq BT} `{EA : Eq AT}
  (v : @expr_value (@link BT EB AT EA)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_bf C)
  end.

Definition filter_v_af
  `{EB : Eq BT} `{EA : Eq AT}
  (v : @expr_value (@link BT EB AT EA)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_af C)
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

(*
Definition link_tick `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT)
  C st x v :=
  match st with
  | ST mem t =>
    match t with
    | L bt t =>
      if leb final bt then
        L bt (tick )
      else if 

        let Cout := lift_ctx_bf Cout in
        AF
        (tick (filter_ctx_af (delete_ctx Cout C))
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
    | AF t => map (inject_ctx_v (lift_ctx_bf Cout)) (map (lift_v_af) (amem t))
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
  rewrite IHl. destruct a. simpl.
  rewrite delete_inject_eq. rewrite filter_lift_eq_af. eauto.
Qed.

Lemma link_tick_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT) :
  forall bmem C amem t x v,
    link_tick Cout ((lift_ctx_bf Cout)<|(lift_ctx_af C)|>)
                (ST (link_mem bmem Cout amem) (AF t)) x 
                (inject_ctx_v (lift_ctx_bf Cout) (lift_v_af v)) =
    AF (tick C (ST amem t) x v).
Proof.
  intros. destruct v. unfold inject_ctx_v. simpl.
  rewrite delete_inject_eq.
  rewrite delete_inject_eq.
  rewrite filter_delete_eq.
  rewrite filter_lift_eq_af. rewrite filter_lift_eq_af.
  reflexivity.
Qed.

Lemma link_update_m_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT):
  forall bmem amem t v,
  (AF t !#-> inject_ctx_v (lift_ctx_bf Cout) (lift_v_af v);
    (link_mem bmem Cout amem)) =
    link_mem bmem Cout (t !#-> v; amem).
Proof.
  intros. apply functional_extensionality.
  intros. unfold update_m. destruct v. simpl.
  destruct x; simpl; eauto.
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

Lemma link_eval_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT) :
  forall bmem C st e v st'
         (EVAL : @EvalR AT _ _ C st e v st'),
    let inject_C := (lift_ctx_bf Cout) <|(lift_ctx_af C)|> in
    let inject_v :=
      match v with
      | EVal ev => EVal (inject_ctx_v (lift_ctx_bf Cout) (lift_v_af ev))
      | MVal C_v => MVal ((lift_ctx_bf Cout)<|(lift_ctx_af C_v)|>)
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
  try destruct v; try destruct st; try destruct st'; try destruct st'';
  try (destruct inject_v eqn:INJv; inversion INJv; subst);
  try (destruct inject_st eqn:INJst; inversion INJst; subst);
  try (destruct inject_st' eqn:INJst'; inversion INJst'; subst); eauto.
  - inversion STATE; subst.
    eapply Eval_var_e; eauto.
    pose proof (inject_ctx_addr_x x (lift_ctx_bf Cout) (lift_ctx_af C)) as RR.
    rewrite lift_addr_x in RR.
    rewrite <- ADDR in RR. symmetry. apply RR.
    unfold link_mem. 
    remember (mem0 addr) as l.
    clear Heql inject_C C mem0 x addr t0 inject_st' INJst' STATE inject_st INJst ADDR inject_v INJv.
    revert Cout x0 e C0 ACCESS. induction l; simpl; intros; eauto.
    destruct ACCESS as [L | R].
    left. rewrite L. simpl. eauto.
    right. apply IHl. eauto.
  - destruct st_v. destruct arg.
    eapply Eval_app. apply IHEVAL1. apply IHEVAL2.
    pose proof (link_tick_eq Cout bmem C mem t x (Closure x1 e3 C1)) as RR.
    simpl in *. subst inject_C.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq Cout bmem mem t (Closure x1 e3 C1)) as RR. simpl in RR.
    rewrite RR. clear RR.
    replace (dy_c_lam x (AF t) ([||])) with (map_inject (lift_ctx_bf Cout) (dy_c_lam x (AF t) ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. rewrite lift_plugin_af in IHEVAL3. eauto.
  - pose proof (inject_ctx_ctx_M M (lift_ctx_bf Cout) (lift_ctx_af C)) as RR.
    rewrite lift_ctx_M in RR.
    rewrite <- ACCESS in RR.
    eapply Eval_var_m; eauto.
  - eapply Eval_lete; eauto.
    pose proof (link_tick_eq Cout bmem C mem t x (Closure x0 e0 C0)) as RR.
    simpl in *. replace inject_C with (lift_ctx_bf Cout <| lift_ctx_af C |>) by reflexivity.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq Cout bmem mem t (Closure x0 e0 C0)) as RR. simpl in RR.
    rewrite RR. clear RR.
    replace (dy_c_lete x (AF t) ([||])) with (map_inject (lift_ctx_bf Cout) (dy_c_lete x (AF t) ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. rewrite lift_plugin_af in IHEVAL2. eauto.
  - eapply Eval_letm; eauto.
    assert (inject_C [|dy_c_letm M (lift_ctx_bf Cout <| lift_ctx_af C' |>) ([||])|] =
            (lift_ctx_bf Cout <| lift_ctx_af (C [|dy_c_letm M C' ([||])|]) |>)) as RR. 
    { subst inject_C. rewrite lift_plugin_af.
      rewrite <- plugin_inject_assoc. simpl. eauto. } 
    rewrite RR. clear RR. simpl in *. exact IHEVAL2.
Qed.

Lemma link_reach_eq `{Eq BT} `{time AT} (Cout : @dy_ctx BT) :
  forall bmem C st e C' st' e'
         (REACH : @one_reach AT _ _ C st e C' st' e'),
    let inject_C := (lift_ctx_bf Cout) <|(lift_ctx_af C)|> in
    let inject_C' := (lift_ctx_bf Cout) <|(lift_ctx_af C')|> in
    let inject_st :=
      match st with
      | ST amem t => ST (link_mem bmem Cout amem) (AF t)
      end in
    let inject_st' :=
      match st' with
      | ST amem' t' => ST (link_mem bmem Cout amem') (AF t')
      end in
    @one_reach (@link BT AT) _ (link_time Cout)
      inject_C inject_st e inject_C' inject_st' e'.
Proof.
  intros. destruct REACH; try destruct st.
  - apply one_appl.
  - destruct st_lam.
    apply link_eval_eq with (Cout := Cout) (bmem := bmem) in FN.
    eapply one_appr; simpl in *; eauto.
  - apply link_eval_eq with (Cout := Cout) (bmem := bmem) in FN.
    apply link_eval_eq with (Cout := Cout) (bmem := bmem) in ARG.
    destruct st_lam. subst inject_C inject_st inject_C' inject_st'.
    rewrite <- link_update_m_eq. rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    replace (AF (tick C (ST mem t) x arg)) with 
      (link_tick Cout (lift_ctx_bf Cout <| lift_ctx_af C |>)
        (ST (link_mem bmem Cout mem) (AF t)) x (inject_ctx_v (lift_ctx_bf Cout) (lift_v_af arg))).
    apply (@one_appbody (@link BT AT) _ (link_time Cout) 
                        (lift_ctx_bf Cout <| lift_ctx_af C |>)
                        (ST (link_mem bmem Cout mem0) (AF t0))
                        e1 e2 x e (lift_ctx_bf Cout <| lift_ctx_af C_lam |>)
                        (ST (link_mem bmem Cout mem1) (AF t1))
                        (inject_ctx_v (lift_ctx_bf Cout) (lift_v_af arg))
                        (link_mem bmem Cout mem) (AF t)). eauto. eauto.
    destruct arg. simpl.
    repeat rewrite delete_inject_eq. repeat rewrite filter_delete_eq. repeat rewrite filter_lift_eq_af. eauto.
  - apply one_linkl.
  - destruct st_m.
    apply link_eval_eq with (Cout := Cout) (bmem := bmem) in MOD.
    eapply one_linkr; simpl in *; eauto.
  - apply one_letel.
  - apply link_eval_eq with (Cout := Cout) (bmem := bmem) in EVALx.
    subst inject_C inject_st inject_C' inject_st'.
    rewrite <- link_update_m_eq. rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    replace (AF (tick C (ST mem t) x v)) with 
      (link_tick Cout (lift_ctx_bf Cout <| lift_ctx_af C |>)
        (ST (link_mem bmem Cout mem) (AF t)) x (inject_ctx_v (lift_ctx_bf Cout) (lift_v_af v))).
    apply (@one_leter (@link BT AT) _ (link_time Cout) 
                      (lift_ctx_bf Cout <| lift_ctx_af C |>)
                      (ST (link_mem bmem Cout mem0) (AF t0))
                      x e m 
                      (inject_ctx_v (lift_ctx_bf Cout) (lift_v_af v))
                      (link_mem bmem Cout mem) (AF t)). eauto.
    destruct v. simpl.
    repeat rewrite delete_inject_eq. repeat rewrite filter_delete_eq. repeat rewrite filter_lift_eq_af. eauto.
  - apply one_letml.
  - destruct st_M.
    apply link_eval_eq with (Cout := Cout) (bmem := bmem) in EVALM.
    subst inject_C inject_st inject_C' inject_st'.
    rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    eapply one_letmr; simpl in *; eauto.
Qed.
*)