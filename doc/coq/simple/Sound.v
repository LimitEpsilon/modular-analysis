From Simple Require Export Equiv.
From Simple Require Export ALinking.
From Simple Require Export Linking.

Generalizable Variables CT AT.

Definition preserve_tick `{Concrete.time CT} `{Abstract.time AT} (α : CT -> AT) :=
  forall C m t x v,
  let abs_C := trans_C α C in
  let abs_m := trans_m α m in
  let abs_t := α t in
  let abs_v := trans_v α v in
  α (Concrete.tick C m t x v) = 
    Abstract.tick abs_C abs_m abs_t x abs_v.

Ltac gen_leb :=
  match goal with
  | BD : time_bound_C ?C _, H : supp_C ?C _ |- _ =>
    apply BD in H
  | BD : time_bound_v ?v _, H : supp_v ?v _ |- _ =>
    destruct v; unfold time_bound_v in BD; ss;
    apply BD in H
  | BD : time_bound_m ?m _, H : supp_m ?m _ |- _ =>
    apply BD in H
  | _ => idtac
  end.

Ltac solve_leb tac :=
  match goal with
  | _ => assumption
  | |- leb ?t ?t = true => apply leb_refl
  | _ : leb ?t ?t' = true |- leb ?t _ = true =>
    lebt t';
    match goal with
    | _ : leb t' ?t'' = true |- _ => lebt t''
    end
  | _ => tac
  end.

Theorem sound_eval `{Concrete.time CT} `{Abstract.time AT} (α : CT -> AT) (PRES : preserve_tick α) :
  forall e C m t ρ (EVAL : {|(Cf e C m t) ~> ρ|})
    (BOUND : time_bound_ρ (Cf e C m t)),
  let abs_C := trans_C α C in
  let abs_m := trans_m α m in
  let abs_t := α t in
  {|(Cf e abs_C abs_m abs_t) ~#> (trans_ρ α ρ)|}.
Proof.
  intros. remember (Cf e C m t) as cf.
  ginduction EVAL; ii;
  repeat match goal with
  | H : {|(Rs _ _ _) ~> _|} |- _ => inversion H
  | x := _ |- _ => subst x
  end; clarify;
  try match goal with
  | ADDR : addr_x ?C ?x = Some ?addr,
    ACCESS : read ?m ?t = Some ?v |- _ =>
    let RR := fresh "RR" in
    pose proof (trans_C_addr α C x) as RR;
    rewrite ADDR in RR;
    assert (In (trans_v α v) (aread (trans_m α m) (α addr)));
    first [rewrite trans_m_aread;
      exists addr; exists v;
      symmetry in ACCESS; eauto|ss; eauto]
  | ACCESS : ctx_M ?C ?M = Some ?CM |- _ =>
    pose proof (trans_C_ctx_M C α M CM ACCESS); ss; eauto
  end;
  repeat match goal with
  | H : {| (Cf ?e ?C ?m ?t) ~> (Rs ?V ?m' ?t') |} |- _ =>
    lazymatch goal with
    | _ : leb t t' = true |- _ => fail
    | _ =>
      let INC := fresh "INC" in
      let BD := fresh "BD" in
      apply time_increase in H as INC;
      first [solve [ss; eauto] | apply time_bound in H as BD]
    end
  end; ss; des;
  try match goal with
  | |- {| _ ~#> _ |} =>
    try exploit IHEVAL1; eauto;
    try exploit IHEVAL2; eauto;
    try exploit IHEVAL3; eauto;
    ii; ss; eauto (* simple cases are solved *)
  end;
  (* difficult cases *)
  match goal with
  | |- {| _ ~#> _ |} =>
    rewrite trans_m_update with (t := t_a) in *;
    first [apply tick_lt | rewrite PRES in *; eauto | assumption]
  | |- {| _ ~#> _ |} =>
    rewrite trans_m_update with (t := t') in *;
    first [apply tick_lt | rewrite PRES in *; eauto | assumption]
  | |- _ /\ _ =>
    try solve [split; eauto 3 using relax_ctx_bound]
  | _ => idtac
  end;
  split; red; ii; ss; des; clarify;
  gen_leb;
  solve_leb ltac:(apply time_bound in EVAL2; ss; des);
  match goal with
  | |- _ /\ _ => solve [split; eauto 3 using relax_ctx_bound]
  | |- _ /\ _ => split; red; ii; ss; des; clarify;
    first [apply leb_refl | idtac]
  | _ => idtac
  end;
  gen_leb;
  solve_leb idtac.
Qed.

Generalizable Variables BCT BAT ACT AAT.

Definition link_abs 
  `{Concrete.time BCT} `{Abstract.time BAT} 
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :=
  fun t : link BCT ACT =>
  match t with
  | BF t => BF (αbf t)
  | AF t => AF (αaf t)
  end.

Lemma trans_ctx_lift
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  let αlink := (link_abs αbf αaf) in
  forall C,
    trans_C αlink (lift_ctx_bf C) =
    lift_ctx_bf (trans_C αbf C).
Proof.
  induction C; simpl; repeat rw; eauto.
Qed.

Lemma trans_ctx_filter
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall C,
  let αlink := (link_abs αbf αaf) in
  trans_C αaf (filter_ctx_af C) = filter_ctx_af (trans_C αlink C).
Proof.
  induction C; simpl; repeat des_goal; repeat des_hyp;
  clarify; repeat rw; eauto.
Qed.

Lemma trans_ctx_filter_bf
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall C,
  let αlink := (link_abs αbf αaf) in
  trans_C αbf (filter_ctx_bf C) = filter_ctx_bf (trans_C αlink C).
Proof.
  induction C; simpl; repeat des_goal; repeat des_hyp;
  clarify; repeat rw; eauto.
Qed.

Lemma trans_ctx_link
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (Cout : dy_ctx BCT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall C,
  let αlink := (link_abs αbf αaf) in
  let eqb' t t' := eqb (αlink t) (αlink t') in
  trans_C αaf
    (filter_ctx_af (delete eqb' (lift_ctx_bf Cout) C)) =
  filter_ctx_af
    (delete eqb (lift_ctx_bf (trans_C αbf Cout)) (trans_C αlink C)).
Proof.
  intros.
  rewrite <- trans_ctx_lift with (αbf := αbf) (αaf := αaf).
  rewrite <- trans_C_delete.
  rewrite trans_ctx_filter with (αbf := αbf) (αaf := αaf).
  eauto.
Qed.

Lemma trans_m_aux_link
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (Cout : dy_ctx BCT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall (m : memory (link BCT ACT)) seen seen'
    (EQ: forall t, In t seen <-> In (AF t) seen'),
  let αlink := (link_abs αbf αaf) in
  let eqb' t t' := eqb (αlink t) (αlink t') in
  trans_m_aux αaf (filter_mem_af
     (delete_ctx_mem eqb' (lift_ctx_bf Cout) m)) seen =
  filter_mem_af
     (delete_ctx_mem eqb (lift_ctx_bf (trans_C αbf Cout))
        (trans_m_aux αlink m seen')).
Proof.
  induction m; ii; ss; repeat des_goal; repeat des_hyp; clarify; ss.
  - erewrite IHm; eauto.
  - erewrite IHm; eauto.
    ii; ss; split; ii; des; clarify. 
    right. rewrite EQ in *. eauto. 
    rewrite <- EQ in *. eauto.
  - erewrite IHm; eauto.
  - rewrite Inb_eq in *.
    rewrite Inb_neq in *.
    rewrite EQ in *. contradict.
  - rewrite Inb_eq in *.
    rewrite Inb_neq in *.
    rewrite <- EQ in *. contradict.
  - rewrite IHm with (seen' := AF t :: seen').
    destruct e; simpl.
    rewrite trans_ctx_filter with (αbf := αbf) (αaf := αaf).
    subst eqb'.
    subst αlink.
    pose proof (@trans_C_delete (link BCT ACT) (link BAT AAT) _ _) as RR.
    rewrite RR.
    rewrite trans_ctx_lift. eauto.
    ii; split; ii; ss; des; clarify; eauto.
    rewrite EQ in *. eauto.
    rewrite <- EQ in *. eauto.
Qed.

Lemma trans_m_aux_link_bf
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall (m : memory (link BCT ACT))  seen seen'
    (EQ: forall t, In t seen <-> In (BF t) seen'),
  trans_m_aux αbf (filter_mem_bf m) seen =
    filter_mem_bf (trans_m_aux (link_abs αbf αaf) m seen').
Proof.
  induction m; ii; ss; repeat des_goal; repeat des_hyp; clarify; ss.
  - erewrite IHm; eauto.
  - rewrite Inb_eq in *.
    rewrite Inb_neq in *.
    rewrite EQ in *. contradict.
  - rewrite Inb_eq in *.
    rewrite Inb_neq in *.
    rewrite EQ in *. contradict.
  - rewrite IHm with (seen' := BF t :: seen').
    destruct e; simpl.
    rewrite trans_ctx_filter_bf with (αbf := αbf) (αaf := αaf).
    reflexivity.
    ii; split; ii; ss; des; clarify; eauto.
    rewrite EQ in *. eauto.
    rewrite <- EQ in *. eauto.
  - erewrite IHm; eauto.
  - erewrite IHm; eauto.
    ii; split; ii; ss; des; clarify; eauto.
    rewrite EQ in *. eauto.
    rewrite <- EQ in *. eauto.
Qed.

Lemma trans_m_link
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (Cout : dy_ctx BCT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall (m : memory (link BCT ACT)),
  let αlink := (link_abs αbf αaf) in
  let eqb' t t' := eqb (αlink t) (αlink t') in
  trans_m αaf (filter_mem_af
    (delete_ctx_mem eqb' (lift_ctx_bf Cout) m)) =
  filter_mem_af
    (delete_ctx_mem eqb (lift_ctx_bf (trans_C αbf Cout))
      (trans_m αlink m)).
Proof.
  unfold trans_m. ii.
  apply trans_m_aux_link.
  ss.
Qed.

Lemma trans_m_link_bf
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall (m : memory (link BCT ACT)),
  trans_m αbf (filter_mem_bf m) = filter_mem_bf (trans_m (link_abs αbf αaf) m).
Proof.
  unfold trans_m. ii.
  apply trans_m_aux_link_bf.
  ss.
Qed.

Theorem link_abs_pres
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (Cout : dy_ctx BCT) (αbf : BCT -> BAT) (αaf : ACT -> AAT)
  (PRESb : preserve_tick αbf) (PRESa : preserve_tick αaf):
  @preserve_tick
    (link BCT ACT) _ _ (Linking.link_time Cout (link_abs αbf αaf))
    (link BAT AAT) _ (ALinking.link_time (trans_C αbf Cout))
    (link_abs αbf αaf).
Proof.
  unfold preserve_tick in *.
  simpl Concrete.tick. simpl Abstract.tick.
  ii; destruct t; ss; repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | |- BF ?a = BF ?b =>
    let RR := fresh "RR" in
    assert (a = b) as RR;
    first [rewrite RR; reflexivity | idtac]
  | |- AF ?a = AF ?b =>
    let RR := fresh "RR" in
    assert (a = b) as RR;
    first [rewrite RR; reflexivity | idtac]
  end.
  - rewrite PRESb.
    destruct v. s.
    repeat rewrite (trans_ctx_filter_bf αbf αaf).
    rewrite (trans_m_link_bf αbf αaf). eauto.
  - rewrite PRESa.
    pose proof (trans_m_link Cout αbf αaf) as RR.
    rewrite RR.
    destruct v. s.
    repeat rewrite (trans_ctx_filter αbf αaf).
    pose proof (trans_C_delete (link_abs αbf αaf)) as RR'.
    repeat rewrite RR'.
    rewrite trans_ctx_lift. eauto.
Qed.
