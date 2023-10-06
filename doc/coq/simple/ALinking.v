From Simple Require Export Abstract.

Generalizable Variables T BT AT.

Definition link_tick `{time BT} `{time AT} (Cout : dy_ctx BT) :=
  fun C m t x v =>
    match t with
    | BF t => BF (tick (filter_ctx_bf C) (filter_mem_bf m) t x (filter_v_bf v))
    | AF t =>
      let Cout := lift_ctx_bf Cout in
      AF (tick (filter_ctx_af (delete eqb Cout C))
            (filter_mem_af (delete_ctx_mem eqb Cout m)) t
            x (filter_v_af (delete_v eqb Cout v)))
    end.

Lemma link_tick_ext `{time BT} `{time AT} (Cout : dy_ctx BT) :
  forall C m m' t x v (SAME : asame m m'),
  link_tick Cout C m t x v = link_tick Cout C m' t x v.
Proof.
  intros. destruct t; simpl;
  match goal with
  | |- BF ?a = BF ?b =>
    assert (a = b) as RR;
    first [rewrite RR; reflexivity | apply tick_ext]
  | |- AF ?a = AF ?b =>
    assert (a = b) as RR;
    first [rewrite RR; reflexivity | apply tick_ext]
  end; unfold asame in *; ii;
  match goal with
  | |- In ?v (aread (filter_mem_bf _) ?t) <-> _ =>
    specialize (SAME (BF t));
    repeat rewrite aread_filter_bf;
    split; i; des; clarify; eexists; split;
    try reflexivity; rewrite SAME in *; assumption
  | |- In ?v (aread (filter_mem_af _) ?t) <-> _ =>
    specialize (SAME (AF t));
    repeat rewrite aread_filter_af;
    split; i; des; clarify; eexists; split;
    try reflexivity; rewrite aread_delete in *;
    des; clarify; eexists; split;
    try reflexivity; rewrite SAME in *; assumption
  end.
Qed.

#[export] Instance link_time `{time BT} `{time AT} (Cout : dy_ctx BT) : (@time (link BT AT) (@link_eq BT _ AT _ )) :=
  {
    tick := link_tick Cout;
    tick_ext := link_tick_ext Cout;
  }.

Lemma link_tick_eq `{time BT} `{time AT} (Cout : @dy_ctx BT) :
  forall bmem C amem t x v,
    link_tick Cout ((lift_ctx_af C)[|(lift_ctx_bf Cout)|])
                (link_mem bmem Cout amem) (AF t) x 
                (inject_v (lift_ctx_bf Cout) (lift_v_af v)) =
    AF (tick C amem t x v).
Proof.
  intros. destruct v. unfold inject_v. simpl.
  repeat rewrite delete_inject_eq.
  rewrite filter_delete_eq.
  rewrite filter_lift_eq_af. rewrite filter_lift_eq_af.
  reflexivity.
  all:(intros; rewrite link_eqb_eq; reflexivity).
Qed.

Theorem link_step_eq `{time BT} `{time AT} (Cout : dy_ctx BT) :
  forall bmem e C m t cf'
    (EVAL : {|(Cf e C m t) ~#> cf'|}),
    (@step (link BT AT) _ (link_time Cout)
      (inject_cf Cout bmem (Cf e C m t))
      (inject_cf Cout bmem cf')).
Proof.
  intros. remember (Cf e C m t) as cf.
  ginduction EVAL; ii; ss; repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | ADDR : addr_x ?Cin ?x = Some ?addr,
    ACCESS : In (Closure ?x_lam ?e ?C) (aread ?m ?addr)
    |- context[ (lift_ctx_af ?Cin) [|lift_ctx_bf ?Cout|] ] =>
    let RR := fresh "RR" in
    pose proof (inject_addr_x x (lift_ctx_bf Cout) (lift_ctx_af Cin));
    pose proof (@lift_addr_x BT AT Cin x) as RR;
    rewrite ADDR in *; rewrite RR in *;
    assert (In (Closure x_lam e (lift_ctx_af C [|lift_ctx_bf Cout|])) 
      (aread (link_mem bmem Cout m) (AF addr)));
    first[
      unfold link_mem; rewrite aread_in; rewrite aread_in in ACCESS;
      rewrite in_app_iff; left;
      induction m; ss; des; des_goal; clarify; ss; eauto
      | eauto]
  | ACCESS: ctx_M ?Cin ?M = _
    |- context [lift_ctx_af ?Cin [|lift_ctx_bf ?Cout|] ] =>
    let RR := fresh "RR" in
    pose proof (@lift_ctx_M BT AT Cin M) as RR;
    pose proof (inject_ctx_M M (lift_ctx_bf Cout) (lift_ctx_af Cin));
    rewrite ACCESS in *;
    rewrite RR in *; eauto
  | _ => solve [exploit IHEVAL; eauto]
  | _ =>
    let RR := fresh "RR" in
    let RRR := fresh "RRR" in
    try (exploit IHEVAL1; eauto; instantiate (1 := Cout); instantiate (1 := bmem));
    try (exploit IHEVAL2; eauto; instantiate (1 := Cout); instantiate (1 := bmem));
    try (exploit IHEVAL3; eauto; instantiate (1 := Cout); instantiate (1 := bmem));
    ii;
    pose proof (@link_tick_eq BT _ _ AT _ _ Cout bmem) as RR;
    pose proof (@link_update_m_eq BT _ AT _ Cout bmem) as RRR;
    rewrite <- RRR in *;
    rewrite <- RR in *;
    pose proof (@AppBody (link BT AT) _ (link_time Cout));
    pose proof (@App (link BT AT) _ (link_time Cout));
    pose proof (@LetER (link BT AT) _ (link_time Cout));
    pose proof (@LetE (link BT AT) _ (link_time Cout));
    simpl tick in *;
    eauto
  end.
Qed.
