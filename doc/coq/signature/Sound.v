From Signature Require Export Bound.
From Signature Require Export ALinking.
From Signature Require Export Linking.

Generalizable Variables T CT AT.

Definition preserve_tick `{Concrete.time CT} `{Abstract.time AT} (α : CT -> AT) :=
  forall C m t x v,
  let abs_C := trans_C α C in
  let abs_m := trans_m α m in
  let abs_t := α t in
  let abs_v := trans_v α v in
  α (Concrete.tick C m t x v) = 
    Abstract.tick abs_C abs_m abs_t x abs_v.

Lemma trans_m_update `{TotalOrder T} {TT} (α : T -> TT) :
  forall m t t' v (BOUND : time_bound_m m t) (LT : t << t'),
    trans_m α (t' !-> v; m) =
    (α t' !-> trans_v α v; trans_m α m).
Proof.
  intros.
  assert (
    forall l l' 
      (IN : forall t'', (In t'' l' -> t' = t'' \/ In t'' l) /\ (In t'' l -> In t'' l')),
    trans_m_aux α m l = trans_m_aux α m l') as RR.
  {
    intros. ginduction m; intros; simpl; eauto.
    repeat des_goal; try rewrite eqb_eq in *; clarify;
    try rewrite Inb_eq in *; try rewrite Inb_neq in *;
    match goal with
    | _ : In ?t _ |- _ = _ :: _ =>
      specialize (IN t) as [L R];
      match goal with
      | H : In _ _ |- _ => apply R in H; contradict
      end
    | _ : In ?t _ |- _ :: _ = _ =>
      specialize (IN t) as [L R];
      match goal with
      | H : In _ _ |- _ => apply L in H; des; clarify
      end; rewrite <- not_le_lt in LT;
      match goal with
      | _ => contradict
      | _ => 
        assert (false = true);
        try (rewrite <- LT; apply BOUND; s; auto);
        contradict
      end
    | _ => erewrite IHm; eauto;
      match goal with
      | |- context [time_bound_m] => red; ii; apply BOUND; s; auto
      | |- forall _, _ =>
        ii; split; ii; ss; des; auto;
        match goal with
        | H : In ?t _ |- _ =>
          specialize (IN t) as [L R];
          first [apply L in H | apply R in H]; des; eauto
        end
      end
    end.
  }
  unfold trans_m, update_m. s.
  symmetry. erewrite RR; eauto.
  intros; simpl; split; intros; eauto.
Qed.

Lemma trans_C_project {CT AT} (α : CT -> AT) :
  forall s (C : dy_ctx CT),
    project (trans_C α C) s =
    match project C s with
    | Some Cs => Some (trans_C α Cs)
    | None => None
    end.
Proof.
  induction s; ii; ss;
  try rewrite trans_C_addr;
  try rewrite trans_C_ctx_M;
  repeat rw;
  repeat des_goal; repeat des_hyp;
  clarify; ss.
  all:match goal with
  | IH : context [project (trans_C _ _) ?s],
    RR : project _ ?s = _ |- _ => 
    rewrite IHs1 in *; rewrite RR in *; clarify
  end.
Qed.

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
    pose proof (trans_C_ctx_M C α M);
    rewrite ACCESS in *; ss;
    pose proof @trans_C_inject; rw; eauto
  end;
  gen_time_bound CT;
  try match goal with
  | |- {| _ ~#> _ |} =>
    try exploit IHEVAL1; eauto;
    try exploit IHEVAL2; eauto;
    try exploit IHEVAL3; eauto;
    ii; ss;
    try rewrite trans_C_inject;
    des; eauto (* simple cases are solved *)
  end;
  try (pose proof (trans_C_project α s_M C_v); rewrite PROJ in *);
  try (pose proof (trans_C_project α s C'); rewrite PROJs in *);
  eauto;
  (* difficult cases *)
  try match goal with
  | |- context [tick] =>
    rewrite trans_m_update with (t := t_a) in *;
    first [apply tick_lt | rewrite PRES in *; eauto | assumption]
  | _ : context [tick] |- _ =>
    rewrite trans_m_update with (t := t_a) in *;
    first [apply tick_lt | rewrite PRES in *; eauto | assumption]
  end.
Qed.

(* soundness of linking *)
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

Lemma trans_ctx_distribute
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall Caf Cbf,
    trans_C (link_abs αbf αaf) (lift_ctx_af Caf [|lift_ctx_bf Cbf|]) =
    (lift_ctx_af (trans_C αaf Caf) [|lift_ctx_bf (trans_C αbf Cbf)|]).
Proof.
  induction Caf; ii; ss; repeat rw; eauto.
  induction Cbf; ii; ss; repeat rw; eauto.
  f_equal. clear IHCaf1 IHCaf2 Cbf Caf2.
  induction Caf1; ii; ss; repeat rw; eauto.
Qed.

Lemma trans_m_not_seen `{Eq CT} `{Eq AT} (α : CT -> AT) :
  forall (m : memory CT) (nseen seen : list CT)
    (NSEEN : forall t (IN : In t nseen), read m t = None),
  trans_m_aux α m (seen ++ nseen) = trans_m_aux α m seen.
Proof.
  induction m; ii; ss.
  des_goal. des_v; des_goal.
  - rewrite Inb_eq in *.
    rewrite in_app_iff in *.
    rewrite <- Inb_eq in *.
    des. rw. apply IHm. ii. exploit NSEEN; eauto.
    ii. des_hyp; clarify.
    exploit NSEEN; eauto. rewrite t_refl. clarify.
  - rewrite Inb_neq in *.
    assert (~In c seen /\ ~In c nseen).
    { split; ii; eauto; apply GDES; rewrite in_app_iff; eauto. }
    des. rewrite <- Inb_neq in *.
    rw. f_equal.
    apply (IHm nseen (c :: seen)).
    ii. exploit NSEEN; eauto.
    ii. des_hyp; clarify.
Qed.

Lemma trans_m_lift
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall bmem seen,
    trans_m_aux (link_abs αbf αaf) (lift_mem_bf bmem) (map (fun t => BF t) seen) =
    lift_mem_bf (trans_m_aux αbf bmem seen).
Proof.
  induction bmem; ii; ss.
  des_goal. des_v;
  assert (forall x, Inb x seen = Inb (BF x) (map (fun t => BF t : link BCT ACT) seen));
  try solve [induction seen; ss; ii; rw; eauto];
  rw; des_goal; eauto;
  repeat f_equal;
  solve [apply trans_ctx_lift |
    specialize (IHbmem (b :: seen)); ss].
Qed.

Lemma trans_m_distribute
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) (Cbf : dy_ctx BCT) :
  forall amem bmem seen,
    trans_m_aux (link_abs αbf αaf) (link_mem bmem Cbf amem) (map (fun t => AF t) seen) =
    link_mem (trans_m αbf bmem) (trans_C αbf Cbf) (trans_m_aux αaf amem seen).
Proof.
  unfold link_mem.
  induction amem; ii; ss.
  - pose proof (trans_m_not_seen (link_abs αbf αaf) (lift_mem_bf bmem) (map (fun t => AF t) seen) []) as RR.
    ss. rw. pose proof (trans_m_lift αbf αaf bmem []). ss.
    clear RR. induction seen; ss.
    ii; des; clarify; eauto.
    clear seen IHseen. induction bmem; ss. des_goal; ss.
  - des_goal. des_v; s;
    assert (forall x, Inb x seen = Inb (AF x) (map (fun t => AF t : link BCT ACT) seen));
    try solve [induction seen; ss; ii; rw; eauto];
    rw; des_goal; eauto;
    repeat f_equal;
    solve [apply trans_ctx_distribute |
      specialize (IHamem bmem (a0 :: seen)); ss].
Qed.

Theorem inject_cf_distribute 
  `{Concrete.time BCT} `{Abstract.time BAT}
  `{Concrete.time ACT} `{Abstract.time AAT}
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) (Cout : dy_ctx BCT) 
  (bmem : memory BCT) (cf : config ACT) :
  trans_ρ (link_abs αbf αaf) (inject_cf Cout bmem cf) =
    inject_cf (trans_C αbf Cout) (trans_m αbf bmem) (trans_ρ αaf cf).
Proof.
  destruct cf; s; repeat des_goal; ss;
  repeat f_equal;
  match goal with
  | |- trans_C _ _ = _ =>
    apply (trans_ctx_distribute αbf αaf)
  | |- trans_m _ _ = link_mem _ _ (trans_m _ ?m) =>
    apply (trans_m_distribute αbf αaf Cout m bmem [])
  end.
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
    destruct e; simpl;
    rewrite trans_ctx_filter with (αbf := αbf) (αaf := αaf);
    subst eqb';
    subst αlink;
    pose proof (@trans_C_delete (link BCT ACT) (link BAT AAT) _ _) as RR;
    rewrite RR;
    rewrite trans_ctx_lift; eauto.
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
    destruct e; simpl;
    rewrite trans_ctx_filter_bf with (αbf := αbf) (αaf := αaf);
    try reflexivity.
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
    destruct v; s;
    repeat rewrite (trans_ctx_filter_bf αbf αaf);
    rewrite (trans_m_link_bf αbf αaf); eauto.
  - rewrite PRESa.
    pose proof (trans_m_link Cout αbf αaf) as RR.
    rewrite RR.
    destruct v; s;
    repeat rewrite (trans_ctx_filter αbf αaf);
    pose proof (trans_C_delete (link_abs αbf αaf)) as RR';
    repeat rewrite RR';
    rewrite trans_ctx_lift; eauto.
Qed.
