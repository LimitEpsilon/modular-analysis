From Simple Require Export Concrete.

Generalizable Variables T BT AT.

Definition link_leb `{TotalOrder BT} `{TotalOrder AT}
  (t1 : link BT AT) (t2 : link BT AT) :=
  match t1, t2 with
  | BF t1, BF t2 => leb t1 t2
  | AF t1, AF t2 => leb t1 t2
  | BF _, AF _ => true
  | AF _, BF _ => false
  end.

Lemma link_leb_refl `{TotalOrder BT} `{TotalOrder AT} : 
  forall (t : link BT AT), link_leb t t = true.
Proof.
  intros. destruct t; simpl; rewrite leb_refl; eauto.
Qed.

Lemma link_leb_trans `{TotalOrder BT} `{TotalOrder AT} :
  forall (t t' t'' : link BT AT)
    (LE : link_leb t t' = true)
    (LE' : link_leb t' t'' = true),
  link_leb t t'' = true.
Proof.
  intros.
  unfold link_leb in *;
  repeat des_goal; repeat des_hyp; clarify;
  eapply leb_trans; eauto.
Qed.

Lemma link_leb_sym `{TotalOrder BT} `{TotalOrder AT} :
  forall (t t' : link BT AT)
    (LE : link_leb t t' = true)
    (LE' : link_leb t' t = true),
  t = t'.
Proof.
  intros.
  unfold link_leb in *.
  repeat des_hyp; clarify;
  match goal with
  | |- BF ?t = BF ?t' =>
    assert (t = t'); 
    first [solve [subst; eauto] | apply leb_sym; auto]
  | |- AF ?t = AF ?t' => 
    assert (t = t');
    first [solve [subst; eauto] | apply leb_sym; auto]
  end.
Qed.

Lemma link_leb_or `{TotalOrder BT} `{TotalOrder AT} :
  forall (t t' : link BT AT),
  (link_leb t t') || (link_leb t' t) = true.
Proof.
  intros.
  unfold link_leb in *.
  repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | _ : AT,
    RR : leb ?a ?b = false 
    |- leb ?b ?a = true =>
    pose proof (@leb_or AT _ _ a b);
    rewrite RR in *
  | _ : BT,
    RR : leb ?a ?b = false 
    |- leb ?b ?a = true =>
    pose proof (@leb_or BT _ _ a b);
    rewrite RR in *
  end; ss.
Qed.

#[export] Instance LinkOrder `{TotalOrder BT} `{TotalOrder AT} :
  @TotalOrder (link BT AT) (@link_eq BT _ AT _) :=
  {
    leb := link_leb;
    leb_refl := link_leb_refl;
    leb_trans := link_leb_trans;
    leb_sym := link_leb_sym;
    leb_or := link_leb_or;
  }.

Definition link_tick `{Eq T} `{time BT} `{time AT} (Cout : dy_ctx BT) 
  (α : link BT AT -> T) :=
  let eqb t t' := eqb (α t) (α t') in
  fun C m t x v =>
    match t with
    | BF t => BF (tick (filter_ctx_bf C) (filter_mem_bf m) t x (filter_v_bf v))
    | AF t =>
      let Cout := lift_ctx_bf Cout in
      AF (tick (filter_ctx_af (delete eqb Cout C))
            (filter_mem_af (delete_ctx_mem eqb Cout m)) t
            x (filter_v_af (delete_v eqb Cout v)))
    end.

Local Lemma t_refl `{Eq T} {TT} (α : TT -> T) :
  forall t, 
  let eqb t t' := eqb (α t) (α t') in
  eqb t t = true.
Proof.
  ii; subst eqb; ss; rewrite eqb_eq; eauto.
Qed.

Lemma link_tick_ext `{Eq T} `{time BT} `{time AT} (Cout : dy_ctx BT) (α : link BT AT -> T) :
  forall C m m' t x v (SAME : same m m'),
  link_tick Cout α C m t x v = link_tick Cout α C m' t x v.
Proof.
  intros. destruct t; simpl;
  match goal with
  | |- BF ?a = BF ?b =>
    assert (a = b) as RR;
    first [rewrite RR; reflexivity | apply tick_ext]
  | |- AF ?a = AF ?b =>
    assert (a = b) as RR;
    first [rewrite RR; reflexivity | apply tick_ext]
  end; unfold same in *; ii;
  match goal with
  | |- Some ?v = read (filter_mem_bf _) ?t <-> _ =>
    specialize (SAME (BF t));
    repeat rewrite read_filter_bf;
    split; i; des; clarify; eexists; split;
    try reflexivity; rewrite SAME in *; assumption
  | |- Some ?v = read (filter_mem_af _) ?t <-> _ =>
    specialize (SAME (AF t));
    repeat rewrite read_filter_af;
    split; i; des; clarify; eexists; split;
    try reflexivity; rewrite read_delete in *;
    des; clarify; eexists; split;
    try reflexivity; rewrite SAME in *; assumption
  end.
Qed.

Lemma link_tick_lt `{Eq T} `{time BT} `{time AT} (Cout : dy_ctx BT) (α : link BT AT -> T) :
  forall C m t x v, t < link_tick Cout α C m t x v.
Proof.
  destruct t; ss; ii; unfold "<"; s; apply tick_lt.
Qed.

#[export] Instance link_time `{Eq T} `{time BT} `{time AT}
  (Cout : dy_ctx BT) (α : link BT AT -> T) : (@time (link BT AT) _ _) :=
  {
    tick := link_tick Cout α;
    tick_lt := link_tick_lt Cout α;
    tick_ext := link_tick_ext Cout α;
  }.

Lemma link_tick_eq `{Eq T} `{time BT} `{time AT} (Cout : dy_ctx BT) (α : link BT AT -> T) :
  forall bmem C amem t x v,
    link_tick Cout α ((lift_ctx_af C)[|(lift_ctx_bf Cout)|])
          (link_mem bmem Cout amem) (AF t) x 
          (inject_v (lift_ctx_bf Cout) (lift_v_af v)) =
    AF (tick C amem t x v).
Proof.
  intros. destruct v. unfold inject_v. simpl.
  repeat rewrite delete_inject_eq.
  rewrite filter_delete_eq.
  repeat rewrite filter_lift_eq_af.
  reflexivity.
  all:(apply t_refl).
Qed.

Theorem link_step_eq `{Eq T} `{time BT} `{time AT}
  (Cout : dy_ctx BT) (α : link BT AT -> T) :
  forall bmem e (C : dy_ctx AT) m t cf' (EVAL : {|(Cf e C m t) ~> cf'|}),
  (@step (link BT AT) _ _ (@link_time T _ BT _ _ _ AT _ _ _ Cout α)
    (inject_cf Cout bmem (Cf e C m t))
    (inject_cf Cout bmem cf')).
Proof.
  intros. remember (Cf e C m t) as cf.
  ginduction EVAL; ii; ss; repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | ADDR : addr_x ?Cin ?x = Some ?addr,
    ACCESS : read ?m ?addr = Some (Closure ?x_lam ?e ?C)
    |- context[ (lift_ctx_af ?Cin) [|lift_ctx_bf ?Cout|] ] =>
    let RR := fresh "RR" in
    pose proof (inject_addr_x x (lift_ctx_bf Cout) (lift_ctx_af Cin));
    pose proof (@lift_addr_x BT AT Cin x) as RR;
    rewrite ADDR in *; rewrite RR in *;
    assert (Some (Closure x_lam e (lift_ctx_af C [|lift_ctx_bf Cout|])) =
      read (link_mem bmem Cout m) (AF addr)); 
    first [
      unfold link_mem;
      induction m; ss; repeat des_goal; repeat des_hyp;
      clarify; eauto | eauto]
  | ACCESS: ctx_M ?Cin ?M = _
    |- context [lift_ctx_af ?Cin [|lift_ctx_bf ?Cout|] ] =>
    let RR := fresh "RR" in
    pose proof (@lift_ctx_M BT AT Cin M) as RR;
    pose proof (inject_ctx_M M (lift_ctx_bf Cout) (lift_ctx_af Cin));
    rewrite ACCESS in *;
    rewrite RR in *; eauto
  | _ => solve [exploit (IHEVAL T); eauto]
  | _ =>
    let RR := fresh "RR" in
    let RRR := fresh "RRR" in
    try (exploit (IHEVAL1 T); eauto; instantiate (1 := Cout); instantiate (1 := bmem); ii);
    try (exploit (IHEVAL2 T); eauto; instantiate (1 := Cout); instantiate (1 := bmem); ii);
    try (exploit (IHEVAL3 T); eauto; instantiate (1 := Cout); instantiate (1 := bmem); ii);
    pose proof (@link_tick_eq T _ BT _ _ _ AT _ _ _ Cout α bmem) as RR;
    pose proof (@link_update_m_eq BT _ AT _ Cout bmem) as RRR;
    rewrite <- RRR in *;
    rewrite <- RR in *;
    pose proof (@AppBody (link BT AT) _ _ (link_time Cout α));
    pose proof (@App (link BT AT) _ _ (link_time Cout α));
    pose proof (@LetER (link BT AT) _ _ (link_time Cout α));
    pose proof (@LetE (link BT AT) _ _ (link_time Cout α));
    simpl tick in *;
    eauto
  end.
Qed.
