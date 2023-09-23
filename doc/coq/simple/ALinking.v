From Simple Require Export Abstract.

Generalizable Variables T BT AT.

Fixpoint inject_ctx_mem `{Eq T} (Cout : dy_ctx T) (mem : memory T) :=
  match mem with
  | [] => []
  | (t, v) :: tl =>
    (t, inject_v Cout v) :: inject_ctx_mem Cout tl
  end.

Fixpoint delete_ctx_mem `{Eq T} (Cout : dy_ctx T) (mem : memory T) :=
  match mem with
  | [] => []
  | (t, v) :: tl =>
    (t, delete_v eqb Cout v) :: delete_ctx_mem Cout tl
  end.

Lemma delete_ctx_mem_eq `{Eq T} :
  forall (Cout : dy_ctx T) (mem : memory T),
         delete_ctx_mem Cout (inject_ctx_mem Cout mem) = mem.
Proof.
  induction mem; simpl; eauto.
  repeat des_goal; clarify; rw.
  destruct e; simpl.
  pose proof (@delete_inject_eq T eqb) as RR.
  rewrite RR; eauto.
  intros; rewrite eqb_eq; eauto.
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
  | Closure x e C => Closure x e (filter_ctx_bf C)
  end.

Definition filter_v_af {BT AT} (v : expr_value (link BT AT)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_af C)
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
  | Closure x e C => Closure x e (lift_ctx_bf C)
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
  | Closure x e C => Closure x e (lift_ctx_af C)
  end.

Fixpoint lift_mem_af {BT AT} m : memory (link BT AT) :=
  match m with
  | [] => []
  | (t, v) :: tl => (AF t, lift_v_af v) :: lift_mem_af tl
  end.

Definition link_tick `{time BT} `{time AT} (Cout : dy_ctx BT) :=
  fun C m t x v =>
    match t with
    | BF t => BF (tick (filter_ctx_bf C) (filter_mem_bf m) t x (filter_v_bf v))
    | AF t =>
      let Cout := lift_ctx_bf Cout in
      AF (tick (filter_ctx_af (delete eqb Cout C))
            (filter_mem_af (delete_ctx_mem Cout m)) t
            x (filter_v_af (delete_v eqb Cout v)))
    end.

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

Lemma aread_delete `{Eq T} :
  forall (m : memory T) (Cout : dy_ctx T) t v,
    In v (aread (delete_ctx_mem Cout m) t) <->
    exists v', v = delete_v eqb Cout v' /\ In v' (aread m t).
Proof.
  induction m; intros; ss; split; intros READ;
  des; try contradict; repeat des_hyp; des; ss; 
  try rewrite eqb_eq in *; clarify;
  try rewrite t_refl; ss; eauto;
  first [ rewrite IHm in READ; des; eauto
        | try right; rewrite IHm; exists v'; eauto].
Qed.

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

Definition link_mem `{Eq BT} `{Eq AT}
  (bmem : memory BT) (Cout : dy_ctx BT)
  (amem : memory AT) : (memory (link BT AT)) :=
  (inject_ctx_mem (lift_ctx_bf Cout) (lift_mem_af amem)) ++ 
  (lift_mem_bf bmem).

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

Lemma filter_delete_eq `{Eq BT} `{time AT} (Cout : dy_ctx BT):
  forall bmem amem,
  filter_mem_af
    (delete_ctx_mem (lift_ctx_bf Cout)
    (link_mem bmem Cout amem)) = amem.
Proof.
  induction amem; unfold link_mem;
  ss; repeat des_goal; unfold delete_v;
  ss; repeat des_goal.
  - induction bmem; simpl; eauto.
    des_goal; clarify.
  - destruct e; ss; clarify.
    rewrite delete_inject_eq.
    rewrite filter_lift_eq_af.
    unfold link_mem in *. rewrite IHamem. eauto.
    intros. rewrite link_eqb_eq. eauto.
Qed.

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

Lemma link_update_m_eq `{time BT} `{time AT} (Cout : @dy_ctx BT):
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
    | EVal (Closure x e C) =>
      Rs (EVal (Closure x e ((lift_ctx_af C)[|(lift_ctx_bf Cout)|]))) m t
    | MVal C =>
      Rs (MVal ((lift_ctx_af C)[|(lift_ctx_bf Cout)|])) m t
    end
  end.

Lemma link_step_eq `{time BT} `{time AT} (Cout : dy_ctx BT) :
  forall bmem e (C : dy_ctx AT) m t cf' (EVAL : {|(Cf e C m t) ~#> cf'|}),
    (@step (link BT AT) _ (link_time Cout) (inject_cf Cout bmem (Cf e C m t)) (inject_cf Cout bmem cf')).
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
    pose proof (@link_update_m_eq BT _ _ AT _ _ Cout bmem) as RRR;
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
