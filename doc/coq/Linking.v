From MODULAR Require Export Sound.
Require Export Coq.Logic.FunctionalExtensionality.

(* before, after *)
Generalizable Variables BT AT.

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

Definition inject_ctx_mem {T} `{Eq T} (Cout : @dy_ctx T) (mem : T -> option (@expr_value T)) :=
  fun t =>
    match mem t with
    | Some v => Some (inject_ctx_v Cout v)
    | None => None
    end.

Definition delete_ctx_mem {T} `{Eq T} (Cout : @dy_ctx T) (mem : T -> option (@expr_value T)) :=
  fun t =>
    match mem t with
    | Some v => Some (delete_ctx_v Cout v)
    | None => None
    end.

Lemma delete_ctx_mem_eq :
  forall {T} `{Eq T} (Cout : @dy_ctx T) (mem : T -> option (@expr_value T)),
         delete_ctx_mem Cout (inject_ctx_mem Cout mem) = mem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold inject_ctx_mem. unfold delete_ctx_mem.
  destruct (mem x) eqn:ACCESS; try reflexivity.
  destruct e. simpl. rewrite delete_inject_eq. reflexivity.
Qed.

Definition link_tick
  `{EB : Eq BT} `{EA : Eq AT} 
  `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
  `{@Conc.time BT EB OB} `{@Conc.time AT EA OA}
  (final : BT) (init : AT) t :=
  match t with
  | (L bf af) =>
    if link_leb (L final init) (L bf af) then
      L bf (tick af)
    else
      L (tick bf) af
  end.

Lemma link_tick_lt :
  forall 
    `{EB : Eq BT} `{EA : Eq AT} 
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
    `{CB : @Conc.time BT EB OB} `{CA : @Conc.time AT EA OA}
    final init t, 
  let t' := @link_tick BT EB AT EA OB OA CB CA final init t in
  link_leb t t' = true /\ link_eqb t t' = false.
Proof.
  intros. destruct t; simpl in *.
  destruct (leb final bf) eqn:LEbf;
  destruct (eqb final bf) eqn:EQbf;
  destruct (leb init af) eqn:LEaf;
  simpl;
  try rewrite eqb_refl; try rewrite leb_refl;
  try apply tick_lt; eauto;
  assert (leb bf (tick bf) = true) as RR;
  try apply tick_lt;
  assert (eqb bf (tick bf) = false) as RR';
  try apply tick_lt;
  rewrite RR; rewrite RR'; eauto.
Qed.

#[export] Instance link_time 
  `{EB : Eq BT} `{EA : Eq AT} 
  `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
  `{CB : @Conc.time BT EB OB} `{CA : @Conc.time AT EA OA}
  final init
  : (@Conc.time (@link BT EB AT EA) (@LinkEq BT EB AT EA) 
                (@LinkOrderT BT EB AT EA OB OA)) :=
{
  tick := link_tick final init;
  tick_lt := link_tick_lt final init
}.

Definition delete_update {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) :=
  fun C st x v =>
    let delete_C := delete_inject Cout C in
    let delete_st :=
      match st with
      | ST mem t => ST (delete_ctx_mem Cout mem) t
      end in
    let delete_v := 
      match v with
      | Closure x_v e_v C_v =>
        Closure x_v e_v (delete_inject Cout C_v)
      end in
    update delete_C delete_st x delete_v.

Lemma delete_update_lt {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) :
  forall C mem t x v, let t' := delete_update Cout C (ST mem t) x v in
                                leb t t' = true /\ eqb t t' = false.
Proof.
  intros. unfold delete_update in t'. apply update_lt.
Qed.

#[export] Instance delete_time {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) : @time T ET OT :=
  {
    update := delete_update Cout;
    update_lt := delete_update_lt Cout
  }.

Lemma delete_update_eq {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) :
  forall C mem t x v,
    let inject_v :=
      match v with
      | Closure x_v e_v C_v => Closure x_v e_v (Cout<|C_v|>)
      end in
    delete_update Cout (Cout<|C|>) (ST (inject_ctx_mem Cout mem) t) x inject_v =
    update C (ST mem t) x v.
Proof.
  intros. destruct v. destruct inject_v eqn:INJ. inversion INJ. subst.
  unfold delete_update. rewrite delete_inject_eq. rewrite delete_ctx_mem_eq.
  rewrite delete_inject_eq. reflexivity.
Qed.

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

Lemma inject_update_m_eq :
  forall {T} `{Eq T} t x e mem (Cout C : @dy_ctx T),
  (t !-> Closure x e (Cout <| C |>); inject_ctx_mem Cout mem) =
            inject_ctx_mem Cout (t !-> Closure x e C; mem).
Proof.
  intros. apply functional_extensionality.
  intros. unfold update_m. unfold inject_ctx_mem.
  destruct (eqb x0 t); eauto.
Qed.

Lemma delete_eval_eq {T} `{ET : Eq T} `{OT : @OrderT T ET} `{TT : @time T ET OT} (Cout : @dy_ctx T) :
  forall C st e v st'
         (EVAL : @EvalR T ET OT TT C st e v st'),
    let inject_v :=
      match v with
      | EVal (Closure x_v e_v C_v) => EVal (Closure x_v e_v (Cout<|C_v|>))
      | MVal C_v => MVal (Cout<|C_v|>)
      end in
    let inject_st :=
      match st with
      | ST mem t => ST (inject_ctx_mem Cout mem) t
      end in
    let inject_st' :=
      match st' with
      | ST mem' t' => ST (inject_ctx_mem Cout mem') t'
      end in
    @EvalR T ET OT (@delete_time T ET OT TT Cout)
      (Cout<|C|>) inject_st e inject_v inject_st'.
Proof.
  intros. induction EVAL;
  try destruct v; try destruct st; try destruct st'; try destruct st'';
  try (destruct inject_v eqn:INJv; inversion INJv; subst);
  try (destruct inject_st eqn:INJst; inversion INJst; subst);
  try (destruct inject_st' eqn:INJst'; inversion INJst'; subst); eauto.
  - inversion STATE; subst.
    eapply Eval_var_e; eauto.
    pose proof (inject_ctx_addr_x x Cout C) as RR.
    rewrite <- ADDR in RR. symmetry. apply RR.
    unfold inject_ctx_mem. rewrite <- ACCESS. eauto.
  - destruct st_v. destruct arg.
    eapply Eval_app. apply IHEVAL1. apply IHEVAL2.
    pose proof (delete_update_eq Cout C mem t x (Closure x1 e3 C1)) as RR.
    simpl in *. rewrite RR. clear RR.
    rewrite inject_update_m_eq.
    replace (dy_c_lam x t ([||])) with (map_inject Cout (dy_c_lam x t ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. eauto.
  - pose proof (inject_ctx_ctx_M M Cout C) as RR. 
    rewrite <- ACCESS in RR.
    eapply Eval_var_m; eauto.
  - eapply Eval_lete; eauto.
    pose proof (delete_update_eq Cout C mem t x (Closure x0 e0 C0)) as RR.
    simpl in *. rewrite RR. clear RR.
    rewrite inject_update_m_eq.
    replace (dy_c_lete x t ([||])) with (map_inject Cout (dy_c_lete x t ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. eauto.
  - eapply Eval_letm; eauto.
    assert ((Cout <| C |>) [|dy_c_letm M (Cout <| C' |>) ([||])|] =
            (Cout <| (C [|dy_c_letm M C' ([||])|]) |>)) as RR. 
    { rewrite <- plugin_inject_assoc. simpl. eauto. } 
    rewrite RR. clear RR. simpl in *. exact IHEVAL2.
Qed.

Fixpoint lift_state_bf `{OrderT BT} (st : @state BT) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (BF t) (lift_ctx_bf C')
  | dy_c_lete x t C' => dy_c_lete x (BF t) (lift_ctx_bf C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_bf C') (lift_ctx_bf C'')
  end.

Fixpoint lift_state_af `{OrderT AT} (st : @state AT) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (AF t) (lift_ctx_af C')
  | dy_c_lete x t C' => dy_c_lete x (AF t) (lift_ctx_af C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_af C') (lift_ctx_af C'')
  end.

Definition inject_state {T} (st_out : @Conc.state T)

Lemma link_eval `{Conc.time BT} `{Conc.time AT} :
  forall (Cout : @dy_ctx BT) (Cin : @dy_ctx AT) st e e' st'
         (EVAL : EvalR C st e e' st')
