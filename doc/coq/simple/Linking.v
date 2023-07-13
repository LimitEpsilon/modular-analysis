From Simple Require Export Sound.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

Generalizable Variables T BT AT.

Definition inject_ctx_mem `{Eq T} (Cout : @dy_ctx T) (mem : T -> option expr_value) :=
  fun t => match mem t with None => None | Some v => Some (inject_ctx_v Cout v) end.

Definition delete_ctx_mem `{Eq T} `{Eq AT} (α : T -> AT) (Cout : @dy_ctx T) (mem : T -> option expr_value) :=
  let eqb' t t' := eqb (α t) (α t') in
  fun t => match mem t with None => None | Some v => Some (delete_ctx_v eqb' Cout v) end.

Lemma delete_ctx_mem_eq `{Eq T} `{Eq AT} (α : T -> AT) :
  forall (Cout : @dy_ctx T) (mem : T -> option expr_value),
         delete_ctx_mem α Cout (inject_ctx_mem Cout mem) = mem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold inject_ctx_mem. unfold delete_ctx_mem.
  destruct (mem x); eauto.
  simpl. destruct e; simpl; rewrite delete_inject_eq.
  eauto. intros. rewrite eqb_eq. eauto.
Qed.

Inductive link {BT AT} (final : BT) (init : AT) :=
  | L (bf : BT) (af : AT)
. 

Definition link_eqb `{Eq BT} `{Eq AT} (final : BT) (init : AT)
  (t1 : link final init) (t2 : link final init) :=
  match t1, t2 with
  | L _ _ bf af, L _ _ bf' af' =>
    eqb bf bf' && eqb af af'
  end.

Definition link_leb `{OrderT BT} `{OrderT AT} (final : BT) (init : AT) 
  (t1 : link final init) (t2 : link final init) :=
  match t1, t2 with
  | L _ _ bf af, L _ _ bf' af' =>
    if leb bf bf' then
      if eqb bf bf' then
        leb af af'
      else true
    else false
  end.

Lemma link_leb_refl `{OrderT BT} `{OrderT AT} (final : BT) (init : AT) : 
  forall t, link_leb final init t t = true.
Proof.
  intros. destruct t. simpl. rewrite leb_refl. 
  replace (eqb bf bf) with true.
  apply leb_refl.
  symmetry. apply eqb_eq. eauto.
Qed.

Lemma link_leb_trans `{OrderT BT} `{OrderT AT} (final : BT) (init : AT) :
  forall t t' t''
    (LE : link_leb final init t t' = true)
    (LE' : link_leb final init t' t'' = true),
  link_leb final init t t'' = true.
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

Lemma link_leb_sym `{OrderT BT} `{OrderT AT} (final : BT) (init : AT) :
  forall t t'
    (LE : link_leb final init t t' = true)
    (LE' : link_leb final init t' t = true),
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

Lemma link_leb_or `{OrderT BT} `{OrderT AT} (final : BT) (init : AT) :
  forall t t',
  let le1 := link_leb final init t t' in
  let le2 := link_leb final init t' t in
  le1 || le2 = true.
Proof.
  intros.
  destruct t as [bf af]; destruct t' as [bf' af'].
  simpl in *.
  destruct (leb bf bf') eqn:LEbf;
  destruct (leb bf' bf) eqn:LEbf';
  subst le1 le2.
  - replace bf with bf'; try (apply leb_sym; eauto).
    rewrite t_refl. apply leb_or.
  - assert (eqb bf bf' = false) as RR.
    { refl_bool. intros contra.
      rewrite eqb_eq in contra. subst.
      rewrite leb_refl in LEbf'. inversion LEbf'. }
    rewrite RR. eauto.
  - assert (eqb bf' bf = false) as RR.
    { refl_bool. intros contra.
      rewrite eqb_eq in contra. subst.
      rewrite leb_refl in LEbf. inversion LEbf. }
    rewrite RR. eauto.
  - assert (leb bf bf' || leb bf' bf = true) as contra.
    apply leb_or. rewrite LEbf in contra. rewrite LEbf' in contra.
    inversion contra.
Qed.

Lemma link_eqb_eq `{Eq BT} `{Eq AT} (final : BT) (init : AT):
  forall t t', link_eqb final init t t' = true <-> t = t'.
Proof.
  intros.
  destruct t as [bf af]; destruct t' as [bf' af'];
  simpl in *;
  split; intro EQ.
  destruct (eqb bf bf') eqn:EQbf;
  destruct (eqb af af') eqn:EQaf;
  try (inversion EQ; fail).
  rewrite eqb_eq in EQbf.
  rewrite eqb_eq in EQaf. subst. eauto.
  inversion EQ; subst.
  repeat rewrite t_refl. eauto.
Qed.

Lemma link_eqb_neq `{Eq BT} `{Eq AT} (final : BT) (init : AT):
  forall t t', link_eqb final init t t' = false <-> t <> t'.
Proof.
  intros.
  split; intro NEQ.
  red. intros EQ.
  assert (link_eqb final init t t' = true) as RR. apply link_eqb_eq. eauto.
  rewrite RR in NEQ. inversion NEQ.
  refl_bool. intros contra. rewrite link_eqb_eq in contra.
  apply NEQ; eauto.
Qed.

#[export] Instance LinkEq `{Eq BT} `{Eq AT} (final : BT) (init : AT) :
  Eq (link final init) :=
{
  eqb := link_eqb final init;
  eqb_eq := link_eqb_eq final init;
  eqb_neq := link_eqb_neq final init
}.

#[export] Instance LinkOrderT `{OrderT BT} `{OrderT AT} (final : BT) (init : AT) :
  @OrderT (link final init) (LinkEq final init) :=
  {
    leb := link_leb final init;
    leb_refl := link_leb_refl final init;
    leb_trans := link_leb_trans final init;
    leb_sym := link_leb_sym final init;
    leb_or := link_leb_or final init
  }.

Fixpoint filter_ctx_bf
  `{OrderT BT} `{EA : Eq AT} (final : BT) (init : AT)
  (C : @dy_ctx (link final init)) :=
  match C with
  | ([||]) => ([||])
  | dy_binde x (L _ _ bf af) C' =>
    let filtered := filter_ctx_bf final init C' in
    if eqb final bf then filtered else dy_binde x bf filtered
  | dy_bindm M C' C'' =>
    dy_bindm M (filter_ctx_bf final init C') (filter_ctx_bf final init C'')
  end.

Fixpoint filter_ctx_af
  `{OrderT BT} `{EA : Eq AT} (final : BT) (init : AT)
  (C : @dy_ctx (link final init)) :=
  match C with
  | ([||]) => ([||])
  | dy_binde x (L _ _ bf af) C' =>
    let filtered := filter_ctx_af final init C' in
    if eqb final bf then dy_binde x af filtered else filtered
  | dy_bindm M C' C'' =>
    dy_bindm M (filter_ctx_af final init C') (filter_ctx_af final init C'')
  end.

Definition filter_v_bf 
  `{OrderT BT} `{EA : Eq AT} (final : BT) (init : AT)
  (v : @expr_value (link final init)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_bf final init C)
  end.

Definition filter_v_af
  `{OrderT BT} `{EA : Eq AT} (final : BT) (init : AT)
  (v : @expr_value (link final init)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_af final init C)
  end.

Definition filter_mem_bf
  `{OrderT BT} `{EA : Eq AT} (final : BT) (init : AT)
  (mem : (link final init) -> option (@expr_value (link final init))) :=
  fun t =>
    match mem (L _ _ t init) with
    | Some v => Some (filter_v_bf final init v)
    | None => None
    end.

Definition filter_mem_af
  `{OrderT BT} `{EA : Eq AT} (final : BT) (init : AT)
  (mem : (link final init) -> option (@expr_value (link final init))) :=
  fun t =>
    match mem (L _ _ final t) with
    | Some v => Some (filter_v_af final init v)
    | None => None
    end.

Fixpoint lift_ctx_bf `{Eq BT} `{Eq AT} (final : BT) (init : AT) (C : @dy_ctx BT)
  : @dy_ctx (link final init) :=
  match C with
  | ([||]) => ([||])
  | dy_binde x t C' => dy_binde x (L _ _ t init) (lift_ctx_bf final init C')
  | dy_bindm M C' C'' => dy_bindm M (lift_ctx_bf final init C') (lift_ctx_bf final init C'')
  end.

Fixpoint lift_ctx_af `{Eq BT} `{Eq AT} (final : BT) (init : AT) (C : @dy_ctx AT)
  : @dy_ctx (link final init) :=
  match C with
  | ([||]) => ([||])
  | dy_binde x t C' => dy_binde x (L _ _ final t) (lift_ctx_af final init C')
  | dy_bindm M C' C'' => dy_bindm M (lift_ctx_af final init C') (lift_ctx_af final init C'')
  end.

Definition lift_v_af `{Eq BT} `{Eq AT} (final : BT) (init : AT) (v : @expr_value AT)
  : @expr_value (link final init) :=
  match v with
  | Closure x e C => Closure x e (lift_ctx_af final init C)
  end.

Definition link_tick `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT)
  `{Eq T} (α : link final init -> T)
  C st x v :=
  match st with
  | ST mem (L _ _ bf af) =>
    if eqb final bf then
      let Cout := lift_ctx_bf final init Cout in
      let eqb' t t' := eqb (α t) (α t') in
      let af' := 
        tick (filter_ctx_af final init (delete_ctx eqb' Cout C))
             (ST (filter_mem_af final init (delete_ctx_mem α Cout mem)) af)
             x (filter_v_af final init (delete_ctx_v eqb' Cout v)) in
      L final init final af'
    else
      let bf' := tick (filter_ctx_bf final init C)
                      (ST (filter_mem_bf final init mem) bf)
                      x (filter_v_bf final init v)
      in L final init bf' init
  end.

Lemma link_tick_lt `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT)
  `{Eq T} (α : link final init -> T):
  forall C mem t x v, t < link_tick final init Cout α C (ST mem t) x v.
Proof.
  destruct t; unfold "<"; simpl.
  destruct (eqb final bf) eqn:EQ; simpl;
  try rewrite eqb_eq in EQ; try rewrite eqb_neq in EQ.
  - intros. subst. rewrite leb_refl. rewrite t_refl. simpl.
    split; try apply tick_lt.
  - intros.
    destruct (leb
      (tick (filter_ctx_bf final init C)
         (ST (filter_mem_bf final init mem) bf) x 
         (filter_v_bf final init v)) final) eqn:LT; simpl.
    + replace (leb bf
      (tick (filter_ctx_bf final init C) (ST (filter_mem_bf final init mem) bf)
        x (filter_v_bf final init v))) with true; try (symmetry; apply tick_lt).
      replace (eqb bf
      (tick (filter_ctx_bf final init C) (ST (filter_mem_bf final init mem) bf)
        x (filter_v_bf final init v))) with false; try (symmetry; apply tick_lt).
      eauto.
    + replace (leb bf
      (tick (filter_ctx_bf final init C) (ST (filter_mem_bf final init mem) bf)
        x (filter_v_bf final init v))) with true; try (symmetry; apply tick_lt).
      replace (eqb bf
      (tick (filter_ctx_bf final init C) (ST (filter_mem_bf final init mem) bf)
        x (filter_v_bf final init v))) with false; try (symmetry; apply tick_lt).
      eauto.
Qed.

#[export] Instance link_time `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) `{Eq T} (α : link final init -> T) : (@time (link final init) _ _) :=
  {
    tick := link_tick final init Cout α;
    tick_lt := link_tick_lt final init Cout α
  }.

Definition link_mem `{OrderT BT} `{Eq AT}
  (bmem : BT -> option (@expr_value BT)) (final : BT) (init : AT) (Cout : @dy_ctx BT)
  (amem : AT -> option (@expr_value AT)) : (link final init) -> option expr_value :=
  fun t =>
    match t with
    | L _ _ bf af =>
      if eqb final bf then
        let Cout := lift_ctx_bf final init Cout in
        match amem af with
        | Some (Closure x e C) => Some (Closure x e (Cout<|lift_ctx_af final init C|>))
        | None => None
        end
      else match bmem bf with
        | Some (Closure x e C) => Some (Closure x e (lift_ctx_bf final init C))
        | None => None
        end
    end.

Lemma filter_lift_eq_af `{time BT} `{time AT} (final : BT) (init : AT):
  forall (C : @dy_ctx AT),
    filter_ctx_af final init (lift_ctx_af final init C) = C.
Proof.
  induction C; simpl; try rewrite IHC; try rewrite t_refl; eauto.
  rewrite IHC2. rewrite IHC1. eauto.
Qed.

Lemma filter_lift_eq_bf `{time BT} `{time AT} (final : BT) (init : AT) :
  forall (C : @dy_ctx BT) (BOUND : dy_ctx_bound C final),
    filter_ctx_bf final init (lift_ctx_bf final init C) = C.
Proof.
  induction C; intros; simpl in *;
  try rewrite IHC; try apply BOUND;
  try replace (eqb final tx) with false; eauto;
  try destruct BOUND as [[LE NEQ] BOUND];
  try (symmetry; refl_bool; intros contra;
      rewrite eqb_eq in contra; subst; rewrite t_refl in NEQ; inversion NEQ).
  rewrite IHC2; try rewrite IHC1; eauto; apply BOUND.
Qed.

Lemma filter_delete_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) `{Eq T} (α : link final init -> T) :
  forall bmem amem,
  filter_mem_af final init
    (delete_ctx_mem α (lift_ctx_bf final init Cout)
    (link_mem bmem final init Cout amem)) = amem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold filter_mem_af.
  unfold delete_ctx_mem. simpl. rewrite t_refl.
  remember (lift_ctx_bf final init Cout) as vout eqn:E. clear E.
  remember (amem x) as o eqn:E. clear E.
  destruct o; eauto. destruct e. simpl.
  rewrite delete_inject_eq. rewrite filter_lift_eq_af. eauto.
  intros. rewrite eqb_eq. eauto.
Qed.

Lemma link_tick_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) `{Eq T} (α : link final init -> T) :
  forall bmem C amem t x v,
    link_tick final init Cout α ((lift_ctx_bf final init Cout)<|(lift_ctx_af final init C)|>)
              (ST (link_mem bmem final init Cout amem) (L final init final t)) x 
              (inject_ctx_v (lift_ctx_bf final init Cout) (lift_v_af final init v)) =
    L final init final (tick C (ST amem t) x v).
Proof.
  intros. destruct v. unfold inject_ctx_v. simpl.
  rewrite delete_inject_eq; try (intros; rewrite eqb_eq; eauto).
  rewrite delete_inject_eq; try (intros; rewrite eqb_eq; eauto).
  rewrite filter_delete_eq.
  rewrite filter_lift_eq_af. rewrite filter_lift_eq_af. rewrite t_refl.
  reflexivity.
Qed.

Lemma link_update_m_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) :
  forall bmem amem t v (BOUND : time_bound Cout (ST bmem final)),
  (L final init final t !-> inject_ctx_v (lift_ctx_bf final init Cout) (lift_v_af final init v);
    (link_mem bmem final init Cout amem)) =
    link_mem bmem final init Cout (t !-> v; amem).
Proof.
  intros. apply functional_extensionality.
  intros. unfold update_m. destruct v. simpl.
  destruct x; simpl; eauto.
  destruct (eqb bf final) eqn:EQb; destruct (eqb af t) eqn:EQa; simpl; eauto.
  rewrite eqb_eq in EQb. rewrite eqb_eq in EQa.
  subst. rewrite t_refl. eauto.
  destruct (eqb final bf) eqn:EQb'; eauto.
  rewrite eqb_eq in EQb'. subst.
  rewrite eqb_neq in EQb. contradict.
Qed.

Lemma lift_addr_x `{time BT} `{time AT} (final : BT) (init :AT) :
  forall (C : @dy_ctx AT) x,
    addr_x (lift_ctx_af final init C) x =
      match addr_x C x with
      | Some addr => Some (L final init final addr)
      | None => None
      end.
Proof.
  induction C; simpl; eauto;
  intros;
  destruct (eq_eid x0 x); rewrite IHC;
  destruct (addr_x C x0); eauto.
Qed.

Lemma lift_ctx_M `{time BT} `{time AT} (final : BT) (init : AT) :
  forall (C : @dy_ctx AT) M,
    ctx_M (lift_ctx_af final init C) M =
      match ctx_M C M with
      | Some CM => Some (lift_ctx_af final init CM)
      | None => None
      end.
Proof.
  induction C; simpl; eauto;
  intros.
  destruct (eq_mid M0 M); rewrite IHC2;
  destruct (ctx_M C2 M0); eauto.
Qed.

Lemma lift_plugin_af `{time BT} `{time AT} (final : BT) (init : AT) :
  forall (C C' : @dy_ctx AT),
    lift_ctx_af final init (C[|C'|]) = (lift_ctx_af final init C [|lift_ctx_af final init C'|]).
Proof.
  induction C; simpl; intros; try rewrite IHC; eauto.
  rewrite IHC2. eauto.
Qed.

Lemma link_eval_eq `{time BT} `{time AT} (final : BT) (init : AT) (Cout : @dy_ctx BT) `{Eq T} (α : link final init -> T) :
  forall bmem (BOUND : time_bound Cout (ST bmem final))
         C st e v st'
         (EVAL : @EvalR AT _ _ _ C st e v st'),
    let inject_C := (lift_ctx_bf final init Cout) <|(lift_ctx_af final init C)|> in
    let inject_v :=
      match v with
      | EVal ev => EVal (inject_ctx_v (lift_ctx_bf final init Cout) (lift_v_af final init ev))
      | MVal C_v => MVal ((lift_ctx_bf final init Cout)<|(lift_ctx_af final init C_v)|>)
      end in
    let inject_st :=
      match st with
      | ST amem t => ST (link_mem bmem final init Cout amem) (L _ _ final t)
      end in
    let inject_st' :=
      match st' with
      | ST amem' t' => ST (link_mem bmem final init Cout amem') (L _ _ final t')
      end in
    @EvalR (link final init) _ _ (link_time final init Cout α)
      inject_C inject_st e inject_v inject_st'.
Proof.
  intros. induction EVAL;
  try destruct v; try destruct st; try destruct st'; try destruct st'';
  try (destruct inject_v eqn:INJv; inversion INJv; subst);
  try (destruct inject_st eqn:INJst; inversion INJst; subst);
  try (destruct inject_st' eqn:INJst'; inversion INJst'; subst); eauto.
  - inversion STATE; subst.
    eapply Eval_var_e; eauto.
    pose proof (inject_ctx_addr_x x (lift_ctx_bf final init Cout) (lift_ctx_af final init C)) as RR.
    rewrite lift_addr_x in RR.
    rewrite <- ADDR in RR. symmetry. apply RR.
    unfold link_mem. rewrite t_refl.
    rewrite <- ACCESS. eauto.
  - destruct st_v. destruct arg.
    eapply Eval_app. apply IHEVAL1. apply IHEVAL2.
    pose proof (link_tick_eq final init Cout α bmem C mem t x (Closure x1 e3 C1)) as RR.
    simpl in *. subst inject_C.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq final init Cout bmem mem t (Closure x1 e3 C1) BOUND) as RR. simpl in RR.
    rewrite RR. clear RR.
    replace (dy_binde x (L _ _ final t) ([||])) with 
    (map_inject (lift_ctx_bf final init Cout) (dy_binde x (L _ _ final t) ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. rewrite lift_plugin_af in IHEVAL3. eauto.
  - pose proof (inject_ctx_ctx_M M (lift_ctx_bf final init Cout) (lift_ctx_af final init C)) as RR.
    rewrite lift_ctx_M in RR.
    rewrite <- ACCESS in RR.
    eapply Eval_var_m; eauto.
  - eapply Eval_lete; eauto.
    pose proof (link_tick_eq final init Cout α bmem C mem t x (Closure x0 e0 C0)) as RR.
    simpl in *. subst inject_C.
    rewrite RR. clear RR.
    pose proof (link_update_m_eq final init Cout bmem mem t (Closure x0 e0 C0) BOUND) as RR. simpl in RR.
    rewrite RR. clear RR.
    replace (dy_binde x (L _ _ final t) ([||])) with 
    (map_inject (lift_ctx_bf final init Cout) (dy_binde x (L _ _ final t) ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. rewrite lift_plugin_af in IHEVAL2. eauto.
  - eapply Eval_letm; eauto.
    assert (inject_C [|dy_bindm M (lift_ctx_bf final init Cout <| lift_ctx_af final init C' |>) ([||])|] =
            (lift_ctx_bf final init Cout <| lift_ctx_af final init (C [|dy_bindm M C' ([||])|]) |>)) as RR. 
    { subst inject_C. rewrite lift_plugin_af.
      rewrite <- plugin_inject_assoc. simpl. eauto. } 
    rewrite RR. clear RR. simpl in *. exact IHEVAL2.
Qed.

Lemma link_reach_eq `{time BT} `{time AT} `{Eq T} (final : BT) (init : AT) (Cout : @dy_ctx BT) (α : link final init -> T) :
  forall bmem (BOUND : time_bound Cout (ST bmem final))
         C st e C' st' e'
         (REACH : @one_reach AT _ _ _ C st e C' st' e'),
    let inject_C := (lift_ctx_bf final init Cout) <|(lift_ctx_af final init C)|> in
    let inject_C' := (lift_ctx_bf final init Cout) <|(lift_ctx_af final init C')|> in
    let inject_st :=
      match st with
      | ST amem t => ST (link_mem bmem final init Cout amem) (L _ _ final t)
      end in
    let inject_st' :=
      match st' with
      | ST amem' t' => ST (link_mem bmem final init Cout amem') (L _ _ final t')
      end in
    @one_reach (link _ _) _ _ (link_time final init Cout α)
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
    replace (L _ _ final (tick C (ST mem t) x arg)) with 
      (link_tick final init Cout α (lift_ctx_bf final init Cout <| lift_ctx_af final init C |>)
        (ST (link_mem bmem final init Cout mem) (L _ _ final t)) x (inject_ctx_v (lift_ctx_bf final init Cout) (lift_v_af final init arg))).
    apply (@one_appbody (link final init) _ _ (link_time final init Cout α) 
                        (lift_ctx_bf _ init Cout <| lift_ctx_af final _ C |>)
                        (ST (link_mem bmem final init Cout mem0) (L _ _ final t0))
                        e1 e2 x e (lift_ctx_bf _ init Cout <| lift_ctx_af final _ C_lam |>)
                        (ST (link_mem bmem final init Cout mem1) (L _ _ final t1))
                        (inject_ctx_v (lift_ctx_bf _ init Cout) (lift_v_af final _ arg))
                        (link_mem bmem final init Cout mem) (L _ _ final t)). eauto. eauto.
    destruct arg. simpl. rewrite t_refl.
    repeat rewrite delete_inject_eq. repeat rewrite filter_delete_eq. repeat rewrite filter_lift_eq_af. eauto.
    intros; rewrite eqb_eq; eauto. intros; rewrite eqb_eq; eauto.
  - apply one_linkl.
  - destruct st_m.
    eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in MOD; eauto.
    eapply one_linkr; simpl in *; eauto.
  - apply one_letel.
  - eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in EVALx; eauto.
    subst inject_C inject_st inject_C' inject_st'.
    rewrite <- link_update_m_eq; eauto. rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    replace (L _ _ final (tick C (ST mem t) x v)) with 
      (link_tick final init Cout α (lift_ctx_bf _ init Cout <| lift_ctx_af final _ C |>)
        (ST (link_mem bmem final init Cout mem) (L _ _ final t)) x (inject_ctx_v (lift_ctx_bf _ init Cout) (lift_v_af final _ v))).
    apply (@one_leter (link final init) _ _ (link_time final init Cout α) 
                      (lift_ctx_bf _ init Cout <| lift_ctx_af final _ C |>)
                      (ST (link_mem bmem final init Cout mem0) (L _ _ final t0))
                      x e m 
                      (inject_ctx_v (lift_ctx_bf _ init Cout) (lift_v_af final _ v))
                      (link_mem bmem final init Cout mem) (L _ _ final t)). eauto.
    destruct v. simpl. rewrite t_refl.
    repeat rewrite delete_inject_eq. repeat rewrite filter_delete_eq. repeat rewrite filter_lift_eq_af. eauto.
    intros; rewrite eqb_eq; eauto. intros; rewrite eqb_eq; eauto.
  - apply one_letml.
  - destruct st_M.
    eapply link_eval_eq with (Cout := Cout) (bmem := bmem) in EVALM; eauto.
    subst inject_C inject_st inject_C' inject_st'.
    rewrite lift_plugin_af. rewrite <- plugin_inject_assoc.
    simpl in *.
    eapply one_letmr; simpl in *; eauto.
Qed.
