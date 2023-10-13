From Simple Require Export Abstract.
From Simple Require Export Concrete.

Ltac lebt x :=
  apply leb_trans with (t' := x);
  try assumption; try apply tick_lt; try apply leb_refl.

Generalizable Variables T aT TT aTT.

Definition time_bound_C `{TotalOrder T} C t :=
  forall t', supp_C C t' -> leb t' t = true.

Definition time_bound_m `{TotalOrder T} m t :=
  forall t', supp_m m t' -> leb t' t = true.

Definition time_bound_v `{TotalOrder T} v t :=
  match v with
  | Closure _ _ C => time_bound_C C t
  end.

Definition time_bound_V `{TotalOrder T} V t :=
  match V with
  | EVal ev => time_bound_v ev t
  | MVal mv => time_bound_C mv t
  end.

Definition time_bound_ρ `{TotalOrder T} (ρ : config T) :=
  match ρ with
  | Cf _ C m t =>
    time_bound_C C t /\ time_bound_m m t
  | Rs V m t =>
    time_bound_V V t /\ time_bound_m m t
  end.

Ltac solve_leb1 :=
  match goal with
  | _ => assumption
  | |- leb ?t ?t = true => apply leb_refl
  | |- leb ?t (tick _ _ ?t _ _) = true => apply tick_lt
  | |- leb _ (tick _ _ ?t _ _) = true => apply leb_trans with (t' := t)
  | _ : leb ?a ?b = true |- leb ?a ?c = true => apply leb_trans with (t' := b)
  | _ : supp_v ?v ?t |- _ => destruct v; ss
  | H : time_bound_m ?m ?c, _ : supp_m ?m ?a |- leb ?a ?b = true =>
    lazymatch b with
    | c => apply H
    | _ => apply leb_trans with (t' := b)
    end
  | H : time_bound_C ?C ?c, _ : supp_C ?C ?a |- leb ?a ?b = true =>
    lazymatch b with
    | c => apply H
    | _ => apply leb_trans with (t' := b)
    end
  end.

Ltac solve_leb := repeat solve_leb1.

Lemma not_le_lt `{TotalOrder T} :
  forall (p : T) t,
    (leb p t = false) <-> (t << p).
Proof.
  intros; unfold "<<"; red; split; intros NLE;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- context [leb ?p ?t] =>
    let RR := fresh "RR" in
    destruct (leb p t) eqn:RR
  | |- context [eqb ?p ?t] =>
    let RR := fresh "RR" in
    destruct (eqb p t) eqn:RR
  | H : context [leb ?p ?t] |- _ =>
    match goal with
    | _ : leb p t = true |- _ => idtac
    | _ : leb p t = false |- _ => idtac
    | _ =>
      let RR := fresh "RR" in
      destruct (leb p t) eqn:RR
    end
  end;
  try rewrite eqb_eq in *;
  try rewrite eqb_neq in *; subst;
  try rewrite leb_refl in *;
  clarify; exfalso; eauto using leb_sym.
  pose proof leb_or as contra.
  specialize (contra p t).
  rewrite NLE in *. rewrite RR in *. clarify.
Qed.

Lemma time_bound_or_not `{TotalOrder T} :
  forall (p : T) t,
    (p << t) \/ ~(p << t).
Proof.
  intros.
  rewrite <- not_le_lt.
  destruct (leb t p); eauto.
Qed.

Lemma time_increase `{time T} :
  forall e C m t cf' (EVAL : {|(Cf e C m t) ~> cf'|}),
    match cf' with
    | Cf _ _ _ t'
    | Rs _ _ t' => leb t t' = true
    end.
Proof.
  intros.
  remember (Cf e C m t) as cf. ginduction EVAL;
  intros; clarify; try apply leb_refl; eauto 2;
  try (exploit IHEVAL3; eauto 1);
  try (exploit IHEVAL2; eauto 1);
  try (exploit IHEVAL1; eauto 1);
  try (exploit IHEVAL; eauto 1); intros;
  try lebt t';
  try lebt t_f;
  try lebt t_a;
  match goal with
  | _ : context [tick ?C ?m ?t ?x ?v] |- _ =>
    lebt (tick C m t x v)
  end.
Qed.

Lemma relax_ctx_bound `{time T} :
  forall C t1 t2 (BOUND : time_bound_C C t1) (LE : leb t1 t2 = true),
         time_bound_C C t2.
Proof.
  induction C; unfold time_bound_C;
  intros; ss; des; clarify;
  match goal with
  | H : supp_C ?C ?t |- _ =>
    match goal with
    | H : context [time_bound_C C _] |- _ => eapply H; eauto
    end
  | _ => idtac
  end; try red; intros; try apply BOUND; eauto.
  - lebt t1. apply BOUND. left; eauto.
Qed.

Lemma relax_p_bound `{time T} :
  forall p t1 t2 (BOUND : p << t1) (LE : leb t1 t2 = true),
    p << t2.
Proof.
  intros. destruct BOUND as [? EQ]. split.
  - lebt t1.
  - rewrite eqb_neq in *. red; intros.
    subst. apply EQ. apply leb_sym; eauto.
Qed.

Lemma relax_mem_bound `{TotalOrder T} :
  forall m t1 t2 (BOUND : time_bound_m m t1) (LE : leb t1 t2 = true),
         time_bound_m m t2.
Proof.
  induction m; unfold time_bound_m;
  intros; ss; repeat des_hyp; clarify.
  lebt t1. apply BOUND. eauto.
Qed.

Lemma time_bound_addr `{TotalOrder T} :
  forall C x t (BOUND : time_bound_C C t),
    match addr_x C x with
    | None => True
    | Some addr => leb addr t = true
    end.
Proof.
  induction C; unfold time_bound_C; intros; simpl in *; eauto;
  repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | IH : forall _ t, _ |- _ =>
    match type of IH with
    | context [addr_x ?C _] =>
      match goal with
      | RR : addr_x C ?x = _ |- _ =>
        specialize (IH x t);
        rewrite RR in IH;
        apply IH; red; intros
      end
    end
  | _ => idtac
  end; apply BOUND; eauto.
Qed.

Lemma time_bound_read `{TotalOrder T} :
  forall m t addr (BOUND : time_bound_m m t),
    match read m addr with
    | None => True
    | Some v => leb addr t = true /\ time_bound_v v t
    end.
Proof.
  induction m; intros; simpl; eauto;
  repeat des_goal; repeat des_hyp; eauto;
  try rewrite eqb_eq in *; clarify;
  unfold time_bound_m in *;
  unfold time_bound_v in *.
  - split; repeat des_goal; ii; apply BOUND; s; eauto.
  - exploit (IHm t addr). ii. apply BOUND. s. eauto.
    rw. eauto.
Qed.

Lemma time_bound_ctx_M `{TotalOrder T} :
  forall C M t (BOUND : time_bound_C C t),
    match ctx_M C M with
    | None => True
    | Some CM => time_bound_C CM t
    end.
Proof.
  induction C; unfold time_bound_C; intros; simpl in *; eauto;
  repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | IH : forall _ t, _ |- _ =>
    match type of IH with
    | context [ctx_M ?C _] =>
      match goal with
      | RR : ctx_M C ?M = _ |- _ =>
        specialize (IH M t);
        rewrite RR in IH;
        apply IH; red; intros
      end
    end
  | _ => idtac
  end; try apply BOUND; eauto.
Qed.

Lemma leb_t_neq_tick `{time T} :
  forall C m x v (t' t : T) (LE : leb t' t = true),
  eqb t' (tick C m t x v) = false.
Proof.
  intros. refl_bool. intros contra.
  rewrite eqb_eq in *.
  assert (t <> tick C m t x v) as NEQ.
  { rewrite <- eqb_neq. apply tick_lt. }
  apply NEQ. apply leb_sym. 
  - apply tick_lt.
  - subst. eauto.
Qed.

Lemma time_bound_tick `{time T} :
  forall C m t x v
         (BOUNDv : time_bound_v v t)
         (BOUNDm : time_bound_m m t),
  time_bound_m ((tick C m t x v) !-> v; m) (tick C m t x v).
Proof.
  intros.
  unfold time_bound_v in *.
  unfold time_bound_m in *. des_hyp.
  unfold time_bound_C in *.
  ii; ss; des; clarify;
  match goal with
  | |- leb ?t ?t = true => apply leb_refl
  | H : supp_C ?C _, 
    BD : forall _, supp_C ?C _ -> _
    |- leb _ (tick _ _ ?t _ _) = true  =>
    apply BD in H; lebt t
  | H : supp_m ?m _,
    BD : forall _, supp_m ?m _ -> _ 
    |- leb _ (tick _ _ ?t _ _) = true =>
    apply BD in H; lebt t
  end.
Qed.

Lemma time_bound `{time T} :
  forall e C m t cf'
         (EVAL : {|(Cf e C m t) ~> cf'|})
         (BOUND : time_bound_ρ (Cf e C m t)),
    time_bound_ρ cf'.
Proof.
  intros. remember (Cf e C m t) as cf.
  ginduction EVAL; intros; simpl; clarify;
  unfold time_bound_ρ in *; eauto; destruct BOUND;
  split; try assumption;
  match goal with
  | RR : read ?m ?addr = Some _ |- _ =>
    match goal with
    | H : time_bound_m m ?t |- _ =>
      pose proof (time_bound_read m t addr H);
      rewrite RR in *; des; assumption
    end
  | RR : ctx_M ?C ?M = Some _ |- _ =>
    let HINT := fresh "HINT" in
    pose proof (time_bound_ctx_M C M) as HINT;
    rewrite RR in HINT; apply HINT; eauto
  | _ =>
    repeat match goal with
    | EVAL : {|(Cf ?e ?C ?m ?t) ~> ?cf|} |- _ =>
      lazymatch goal with
      | _ : leb t _ = true |- _ => fail
      | _ => pose proof (time_increase e C m t cf EVAL); simpl in *
      end
    end
  end;
  repeat match goal with
  | IH : forall e C m t, _ -> _ -> ?P /\ ?Q |- _ =>
    edestruct IH; eauto;
    match goal with
    | _ : P |- _ => 
      clear IH; unfold time_bound_v in *;
      repeat des_goal; repeat des_hyp
    | |- _ /\ _ => split;
      match goal with
      | |- time_bound_C ?C ?t =>
        match goal with
        | _ : time_bound_C C ?t' |- _ =>
          apply relax_ctx_bound with (t1 := t'); assumption
        end
      | |- time_bound_m ?m ?t => assumption
      end
    end
  end; subst;
  try (edestruct IHEVAL3; eauto);
  try (edestruct IHEVAL2; eauto);
  repeat match goal with
  | |- _ /\ _ => split
  | |- time_bound_C ?C ?t =>
    red; intros; simpl in *;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H; subst; try apply tick_lt
    | _ : supp_C ?C ?t |- leb ?t _ = true =>
      match goal with
      | H : time_bound_C C ?t' |- _ =>
        lebt t'; try apply H; eauto 3
      end
    end
  | |- time_bound_m ?m ?t => 
    first [assumption |
    apply time_bound_tick; simpl; assumption]
  end;
  first [apply leb_refl | lebt t_a | lebt t'].
Qed.

Ltac gen_time_bound T :=
  lazymatch goal with
  | E1 : @step T _ _ _ (Cf ?e ?C ?m ?t) (Rs ?V ?m' ?t'),
    E2 : {| (Cf ?e' ?C' ?m' ?t') ~> (Rs ?V' ?m'' ?t'') |},
    E3 : {| (Cf ?e'' ?C'' ?m_up (tick ?C_v ?m'' ?t'' ?x ?v)) ~> (Rs ?V'' ?m''' ?t''') |} |- _ =>
    let INC1 := fresh E1 in
    let INC2 := fresh E2 in
    let INC3 := fresh E3 in
    apply time_increase in E1 as INC1;
    apply time_increase in E2 as INC2;
    apply time_increase in E3 as INC3;
    let BD1 := fresh E1 in
    apply time_bound in E1 as BD1;
    lazymatch goal with
    | _ : time_bound_ρ (Rs V m' t') |- _ =>
      let BD2 := fresh E2 in
      assert (time_bound_ρ (Cf e' C' m' t')) as BD2;
      lazymatch goal with
      | _ : time_bound_ρ (Cf e' C' m' t') |- _ =>
        let BD2 := fresh E2 in
        apply time_bound in E2 as BD2;
        lazymatch goal with
        | _ : time_bound_ρ (Rs V' m'' t'') |- _ =>
          let BD3 := fresh E3 in
          assert (time_bound_ρ (Cf e'' C'' m_up (tick C_v m'' t'' x v))) as BD3;
          lazymatch goal with
          | _ : time_bound_ρ (Cf e'' C'' m_up _) |- _ =>
            let BD3 := fresh E3 in
            apply time_bound in E3 as BD3;
            try assumption
          | _ => idtac
          end
        | _ => assumption
        end
      | _ => idtac
      end
    | _ => idtac
    end
  | E1 : @step T _ _ _ (Cf ?e ?C ?m ?t) (Rs ?V ?m' ?t'),
    E2 : {| (Cf ?e' ?C' ?m' ?t') ~> (Rs ?V' ?m'' ?t'') |} |- _ =>
    let INC1 := fresh E1 in
    let INC2 := fresh E2 in
    apply time_increase in E1 as INC1;
    apply time_increase in E2 as INC2;
    let BD1 := fresh E1 in
    apply time_bound in E1 as BD1;
    lazymatch goal with
    | _ : time_bound_ρ (Rs V m' t') |- _ =>
      let BD2 := fresh E2 in
      assert (time_bound_ρ (Cf e' C' m' t')) as BD2;
      lazymatch goal with
      | _ : time_bound_ρ (Cf e' C' m' t') |- _ =>
        let BD2 := fresh E2 in
        apply time_bound in E2 as BD2;
        try assumption
      | _ => idtac
      end
    | _ => idtac
    end
  | E1 : @step T _ _ _ (Cf ?e ?C ?m ?t) (Rs ?V ?m' ?t'),
    E2 : {| (Cf ?e' ?C' ?m_up (tick ?C_v ?m' ?t' ?x ?v)) ~> (Rs ?V' ?m'' ?t'') |} |- _ =>
    let INC1 := fresh E1 in
    let INC2 := fresh E2 in
    apply time_increase in E1 as INC1;
    apply time_increase in E2 as INC2;
    let BD1 := fresh E1 in
    apply time_bound in E1 as BD1;
    lazymatch goal with
    | _ : time_bound_ρ (Rs V m' t') |- _ =>
      let BD2 := fresh E2 in
      assert (time_bound_ρ (Cf e' C' m_up (tick C_v m' t' x v))) as BD2;
      lazymatch goal with
      | _ : time_bound_ρ (Cf e' C' m_up _) |- _ =>
        let BD2 := fresh E2 in
        apply time_bound in E2 as BD2;
        try assumption
      | _ => idtac
      end
    | _ => idtac
    end
  | E : @step T _ _ _ (Cf ?e ?C ?m ?t) (Rs ?V ?m' ?t') |- _ =>
    let INC := fresh E in
    apply time_increase in E as INC;
    let BD := fresh E in
    apply time_bound in E as BD; eauto
  end;
  lazymatch goal with
  | |- time_bound_ρ _ =>
    ss; des; split; red; ii; ss; des; clarify;
    repeat match goal with
    | |- leb ?t ?t = true => apply leb_refl
    | |- leb _ (tick _ _ ?t _ _) = true => lebt t
    | _ : supp_v ?v ?t |- _ => destruct v; ss
    | H : time_bound_m ?m ?t'', _ : supp_m ?m ?t |- leb ?t ?t' = true =>
      lazymatch t' with
      | t'' => apply H; eauto
      | _ => lebt t''
      end
    | H : time_bound_C ?C ?t'', _ : supp_C ?C ?t |- leb ?t ?t' = true =>
      lazymatch t' with
      | t'' => apply H; eauto
      | _ => lebt t''
      end
    end
  | _ => idtac
  end.

Lemma extend_mem `{time T} :
  forall e C m t cf'
         (EVAL : {|(Cf e C m t) ~> cf'|})
         (BOUND : time_bound_ρ (Cf e C m t)),
    match cf' with
    | Rs _ m' _
    | Cf _ _ m' _ =>
      forall t' (LE : leb t' t = true),
        read m' t' = read m t'
    end.
Proof.
  intros.
  remember (Cf e C m t) as cf.
  ginduction EVAL; ii; des; clarify;
  gen_time_bound T; s;
  try match goal with
  | |- (if eqb (tick ?C_v ?m_v ?t_v ?x ?v) ?t then _ else _) = read ?m ?t =>
    ss; des; exploit (time_bound_read m _ t); eauto;
    ii; des;
    exploit (leb_t_neq_tick C_v m_v x v t t_v);
    try (intros RR; rewrite eqb_comm in RR; rewrite RR; clear RR)
  end;
  solve_leb;
  match goal with
  | |- _ = read _ ?t =>
    try (exploit IHEVAL3;
      first [reflexivity 
        | instantiate (1 := t); solve_leb
        | solve [eauto] 
        | ii; repeat rw; s]);
    try (exploit IHEVAL2;
      first [reflexivity 
        | instantiate (1 := t); solve_leb 
        | solve [eauto] 
        | ii; repeat rw; s]);
    try (exploit IHEVAL1;
      first [reflexivity
        | instantiate (1 := t); solve_leb  
        | solve [eauto]
        | ii; repeat rw; s]);
    try (exploit IHEVAL;
      first [reflexivity 
        | instantiate (1 := t); solve_leb 
        | solve [eauto]
        | ii; repeat rw; s])
  end;
  try match goal with
  | |- (if eqb (tick ?C_v ?m_v ?t_v ?x ?v) ?t then _ else _) = read ?m ?t =>
    ss; des; exploit (time_bound_read m _ t); eauto;
    ii; des;
    exploit (leb_t_neq_tick C_v m_v x v t t_v);
    try (intros RR; rewrite eqb_comm in RR; rewrite RR; clear RR)
  end; solve [reflexivity | solve_leb].
Qed.
