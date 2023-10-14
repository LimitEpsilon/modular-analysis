From Simple Require Import Bound.

Generalizable Variables T TT.

Lemma vpath_root_bound `{TotalOrder T} :
  forall p r m m' t
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQm : forall t', leb t' t = true -> read m t' = read m' t'),
  valid_path r m p <-> valid_path r m' p.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify.
  - des_goal; eauto.
    exploit (time_bound_addr C x); eauto. rw.
    ii. exploit EQm; eauto.
    ii. split; ii; des; clarify; split; eauto.
    erewrite <- IHp; eauto.
    erewrite IHp; eauto.
  - des_goal; eauto.
    exploit (time_bound_ctx_M C M); eauto. rw.
    ii. exploit IHp; eauto. s. eauto.
  - split; ii; des; des_hyp; des; clarify;
    exists (Closure x e C).
    split. rewrite <- EQm; eauto.
    split. eauto.
    exploit (time_bound_read m t t0); eauto.
    rrw. ii; ss; des. erewrite <- IHp; eauto.
    rewrite <- EQm in *; eauto.
    split. eauto.
    split. eauto.
    erewrite IHp; eauto.
    exploit (time_bound_read m t t0); eauto. rrw.
    ii; ss; des; eauto.
Qed.

Lemma pmap_root_bound `{TotalOrder T} {TT} :
  forall p r m (f f' : T -> TT) t
    (VALp : valid_path r m p)
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQf : forall t', leb t' t = true -> f' t' = f t'),
  pmap f' p = pmap f p.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify.
  - exploit (time_bound_addr C x); eauto.
    rewrite HDES0. ii.
    rewrite EQf; eauto. erewrite IHp; eauto. s. eauto.
  - exploit (time_bound_ctx_M C M); eauto.
    rewrite HDES0. ii.
    erewrite IHp; eauto. s. eauto.
  - des_hyp; des; clarify.
    exploit (time_bound_read m t t0). eauto.
    rewrite <- VALp. ii; ss; des.
    erewrite IHp; eauto. s. eauto.
Qed.

Lemma e_var_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall C C' m m' (f : T -> TT) f' addr x xv ev Cv
    (ISO : iso (Ctx C) m (Ctx C') m' f f')
    (ADDR : addr_x C x = Some addr)
    (ACCESS : read m addr = Some (Closure xv ev Cv)),
  exists Cv',
    addr_x C' x = Some (f addr) /\
    read m' (f addr) = Some (Closure xv ev Cv') /\
    iso (Ctx Cv) m (Ctx Cv') m' f f'.
Proof.
  ii. destruct ISO as [ISO ISO'].
  exploit (ISO (Px x addr (Pv (v_fn xv ev) Pnil))).
  s. repeat rw. split; eauto. eexists. split; eauto. s. eauto.
  ii; ss; repeat des_hyp; des; clarify.
  des_hyp; des; clarify. eexists. rrw.
  split. eauto. split. eauto.
  split; ii.
  - exploit (ISO (Px x addr (Pv (v_fn x0 e) p))).
    s. repeat rw. split; eauto.
    eexists. split; eauto. s. eauto.
    s. repeat rrw.
    ii; ss; repeat des_hyp; des; clarify.
    des; eauto.
  - exploit (ISO' (Px x (f addr) (Pv (v_fn x0 e) p'))).
    s. repeat rw. split; eauto.
    eexists. split; eauto. s. eauto.
    s. repeat rw.
    ii; ss; repeat des_hyp; des; clarify.
    des; eauto.
Qed.

Lemma m_var_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall C C' m m' (f : T -> TT) f' M CM
    (ISO : iso (Ctx C) m (Ctx C') m' f f')
    (ACCESS : ctx_M C M = Some CM),
  exists CM',
    ctx_M C' M = Some CM' /\
    iso (Ctx CM) m (Ctx CM') m' f f'.
Proof.
  ii. destruct ISO as [ISO ISO'].
  exploit (ISO (PM M Pnil)).
  s. repeat rw. eauto.
  ii; ss; repeat des_hyp; des; clarify.
  eexists.
  split. eauto.
  split; ii.
  - exploit (ISO (PM M p)).
    s. repeat rw. eauto.
    ss. repeat rw. ii; des; clarify.
  - exploit (ISO' (PM M p')).
    s. repeat rw. eauto.
    ss. repeat rw. ii; des; clarify.
Qed.

Lemma update_M_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall CM CM' C C' m m' (f : T -> TT) f' M
    (EQUIVM : <| (MVal CM) m f ≃ (MVal CM') m' f' |>)
    (EQUIVC : <| (MVal C) m f ≃ (MVal C') m' f' |>),
  iso (Ctx (dy_bindm M CM C)) m (Ctx (dy_bindm M CM' C')) m' f f'.
Proof.
  ii. split; ss.
  - ii. destruct p; ss; repeat des_hyp; des; clarify.
    + destruct EQUIVC as [EQ EQ'].
      exploit (EQ (Px x t p)). s. rw. eauto.
      ii; ss; des.
    + rewrite eqb_ID_eq in *; clarify.
      destruct EQUIVM as [EQ EQ'].
      exploit (EQ p). eauto.
      ii; ss; des. rw. eauto.
    + destruct EQUIVC as [EQ EQ'].
      exploit (EQ (PM M0 p)). s. rw. eauto.
      ii; ss; des.
  - ii. destruct p'; ss; repeat des_hyp; des; clarify.
    + destruct EQUIVC as [EQ EQ'].
      exploit (EQ' (Px x t p')). s. rw. eauto.
      ii; ss; des.
    + rewrite eqb_ID_eq in *; clarify.
      destruct EQUIVM as [EQ EQ'].
      exploit (EQ' p'). eauto.
      ii; ss; des. rw. eauto.
    + destruct EQUIVC as [EQ EQ'].
      exploit (EQ' (PM M0 p')). s. rw. eauto.
      ii; ss; des.
Qed.

Lemma update_x_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall (t t_up : T) (t' t_up' : TT) v v' C C' m m' f f' x
    (BOUNDv : time_bound_v v t)
    (BOUNDC : time_bound_C C t)
    (BOUNDm : time_bound_m m t)
    (LT : t << t_up)
    (BOUNDv' : time_bound_v v' t')
    (BOUNDC' : time_bound_C C' t')
    (BOUNDm' : time_bound_m m' t')
    (LT' : t' << t_up')
    (EQUIVv : <| (EVal v) m f ≃ (EVal v') m' f' |>)
    (EQUIVC : <| (MVal C) m f ≃ (MVal C') m' f' |>),
  let g t := if eqb t t_up then t_up' else f t in
  let g' t' := if eqb t' t_up' then t_up else f' t' in
  iso (Ctx (dy_binde x t_up C)) (t_up !-> v; m)
      (Ctx (dy_binde x t_up' C')) (t_up' !-> v'; m')
      g g'.
Proof.
  ii. subst g g'.
  assert (forall t'', leb t'' t = true -> eqb t_up t'' = false).
  {
    ii. refl_bool. ii. rewrite eqb_eq in *; clarify.
    assert (t = t'').
    apply leb_sym. apply LT. eauto.
    assert (t <> t'').
    rewrite <- eqb_neq. apply LT.
    eauto.
  }
  assert (forall t'', leb t'' t' = true -> eqb t_up' t'' = false).
  {
    ii. refl_bool. ii. rewrite eqb_eq in *; clarify.
    assert (t' = t'').
    apply leb_sym. apply LT'. eauto.
    assert (t' <> t'').
    rewrite <- eqb_neq. apply LT'.
    eauto.
  } split; ii.
  - subst p'.
    destruct p; ss;
    repeat des_hyp; des; clarify.
    + repeat rewrite t_refl. rewrite eqb_ID_eq in *. clarify.
      destruct p; ii; ss. repeat rewrite t_refl in *.
      des; des_hyp; des; clarify.
      exploit (vpath_root_bound p (Ctx C0) m (t0 !-> Closure x2 e0 C0; m)); eauto.
      ii. s. rw; eauto.
      intros RR. rewrite <- RR in *.
      exploit (pmap_root_bound p (Ctx C0) m f (fun t' => if eqb t' t0 then t_up' else f t') t);
      eauto. ii. rewrite eqb_comm. rw; eauto.
      intros RR'. rewrite RR'.
      destruct EQUIVv1 as [EQv EQv'].
      exploit EQv; eauto. ii; des.
      exploit (pmap_root_bound (pmap f p) (Ctx C1) m' f' (fun t' => if eqb t' t_up' then t0 else f' t')); eauto.
      ii. rewrite eqb_comm. rw; eauto. rw. ii. rw.
      repeat (split; eauto).
      eexists. split. reflexivity. s. split. eauto.
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_addr C x0); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p (Ptr t0) m (t_up !-> Closure x2 e0 C0; m)); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC (Px x0 t0 p)); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound p (Ptr t0) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_addr C' x0); eauto. rw. rw.
      ii. rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound (pmap f p) (Ptr (f t0)) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_ctx_M C M); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p (Ctx d) m (t_up !-> Closure x1 e0 C0; m)); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC (PM M p)); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      exploit (pmap_root_bound p (Ctx d) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_ctx_M C' M); eauto. rw.
      ii.
      exploit (pmap_root_bound (pmap f p) (Ctx d0) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
  - subst p.
    destruct p'; ss;
    repeat des_hyp; des; clarify.
    + repeat rewrite t_refl. rewrite eqb_ID_eq in *. clarify.
      destruct p'; ii; ss. repeat rewrite t_refl in *.
      des; des_hyp; des; clarify.
      exploit (vpath_root_bound p' (Ctx C1) m' (t0 !-> Closure x2 e0 C1; m')); eauto.
      ii. s. rw; eauto.
      intros RR. rewrite <- RR in *.
      exploit (pmap_root_bound p' (Ctx C1) m' f' (fun t' => if eqb t' t0 then t_up else f' t') t');
      eauto. ii. rewrite eqb_comm. rw; eauto.
      intros RR'. rewrite RR'.
      destruct EQUIVv1 as [EQv EQv'].
      exploit EQv'; eauto. ii; des.
      exploit (pmap_root_bound (pmap f' p') (Ctx C0) m f (fun t' => if eqb t' t_up then t0 else f t')); eauto.
      ii. rewrite eqb_comm. rw; eauto. rw. ii. rw.
      repeat (split; eauto).
      eexists. split. reflexivity. s. split. eauto.
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_addr C' x0); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p' (Ptr t0) m' (t_up' !-> Closure x2 e0 C1; m')); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC' (Px x0 t0 p')); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound p' (Ptr t0) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_addr C x0); eauto. rw. rw.
      ii. rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound (pmap f' p') (Ptr (f' t0)) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_ctx_M C' M); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p' (Ctx d) m' (t_up' !-> Closure x1 e0 C1; m')); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC' (PM M p')); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      exploit (pmap_root_bound p' (Ctx d) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_ctx_M C M); eauto. rw.
      ii.
      exploit (pmap_root_bound (pmap f' p') (Ctx d0) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
Qed.

Lemma extend_mem_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall r r' m m_ext m' m_ext' (t : T) (t' : TT) f f'
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQm : forall addr, leb addr t = true -> read m addr = read m_ext addr)
    (BOUNDr' : match r' with Ctx C' => time_bound_C C' t' | Ptr addr' => leb addr' t' = true end)
    (BOUNDm' : time_bound_m m' t')
    (EQm' : forall addr', leb addr' t' = true -> read m' addr' = read m_ext' addr')
    (ISO : iso r m r' m' f f'),
  iso r m_ext r' m_ext' f f'.
Proof.
  intros. split; ii.
  - subst p'. destruct ISO as [ISO ?].
    rewrite <- vpath_root_bound; eauto.
    apply ISO. rewrite vpath_root_bound; eauto.
  - subst p. destruct ISO as [? ISO].
    rewrite <- vpath_root_bound; eauto.
    apply ISO. rewrite vpath_root_bound; eauto.
Qed.

Lemma extend_iso_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall r r' m m' (t : T) (t' : TT) f f' f_ext f_ext'
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQm : forall addr, leb addr t = true -> f addr = f_ext addr)
    (BOUNDr' : match r' with Ctx C' => time_bound_C C' t' | Ptr addr' => leb addr' t' = true end)
    (BOUNDm' : time_bound_m m' t')
    (EQm' : forall addr', leb addr' t' = true -> f' addr' = f_ext' addr')
    (ISO : iso r m r' m' f f'),
  iso r m r' m' f_ext f_ext'.
Proof.
  intros. split; ii.
  - subst p'. destruct ISO as [ISO ?].
    erewrite <- pmap_root_bound; eauto.
    exploit ISO; eauto. ii; ss; des.
    erewrite <- pmap_root_bound; eauto.
    split; eauto. erewrite pmap_root_bound; eauto.
    ii; symmetry; eauto.
  - subst p. destruct ISO as [? ISO].
    erewrite <- vpath_root_bound; eauto.
    exploit ISO; eauto. ii; ss; des.
    erewrite <- pmap_root_bound; eauto.
    split; eauto. erewrite pmap_root_bound; eauto.
    ii; symmetry; eauto.
Qed.

Theorem operational_equivalence `{time T} `{time TT} :
  forall e (C : dy_ctx T) m t cf_r (C' : dy_ctx TT) m' t' f f'
    (EVAL : {| (Cf e C m t) ~> cf_r |})
    (BOUND : time_bound_ρ (Cf e C m t))
    (BOUND' : time_bound_ρ (Cf e C' m' t'))
    (ISO : iso (Ctx C) m (Ctx C') m' f f'),
  exists cf_r' g g',
    (forall a (LE : leb a t = true), f a = g a) /\
    (forall a' (LE : leb a' t' = true), f' a' = g' a') /\
    {| (Cf e C' m' t') ~> cf_r' |} /\
    match cf_r, cf_r' with
    | Cf e_r C_r m_r t_r, Cf e_r' C_r' m_r' t_r' =>
      e_r = e_r' /\ <| (MVal C_r) m_r g ≃ (MVal C_r') m_r' g' |>
    | Rs V_r m_r t_r, Rs V_r' m_r' t_r' =>
      <| V_r m_r g ≃ V_r' m_r' g' |>
    | _, _ => False
    end.
Proof.
  ii. remember (Cf e C m t) as cf.
  ginduction EVAL; ii; ss; des; clarify;
  try solve [repeat eexists; eauto; s; eauto];
  try gen_time_bound T.
  - destruct v.
    exploit (@e_var_equiv T _ _ TT); eauto.
    ii; des. eexists. exists f. exists f'.
    repeat (split; eauto).
  - exploit IHEVAL; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exists (Cf e2 C' m t). exists g. exists g'.
    split. eauto. split. eauto. split. eauto. split. eauto.
    ss. des.
    eapply extend_mem_equiv with (t := t0); eauto.
    exploit (@extend_mem T); eauto. s. eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT); eauto. s. eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0); eauto.
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto.
    ss; des. eauto using relax_ctx_bound.
    instantiate (1 := g'). instantiate (1 := g).
    eapply extend_mem_equiv with (t := t0); eauto.
    exploit (@extend_mem T); eauto. s. eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT); eauto. s. eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0); eauto.
    ii; des. repeat des_hyp; des; clarify.
    gen_time_bound TT.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure ?x ?e ?Cv)) ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f' |-
      context [iso (Ctx (dy_binde ?x ?t_up ?Cv')) (?t_up !-> ?v'; ?m_up) _ _ _ _] =>
      exists (Cf e (dy_binde x (tick C m'' t'' x v) Cv) 
        ((tick C m'' t'' x v) !-> v; m'') (tick C m'' t'' x v));
      exploit (update_x_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
      try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end.
    ss. des. eapply relax_ctx_bound; eauto.
    s.
    eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m_f); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t_f) (t' := t); eauto.
    ii.
    match goal with
    | _ : iso _ _ _ _ ?f ?f' |- _ =>
      exists f; exists f'
    end.
    repeat (split; eauto); ii;
    match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto.
    ss; des. eauto using relax_ctx_bound.
    instantiate (1 := g'). instantiate (1 := g).
    eapply extend_mem_equiv with (t := t0); eauto.
    exploit (@extend_mem T); eauto. s. eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT); eauto. s. eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0); eauto.
    ii; des. repeat des_hyp; des; clarify.
    gen_time_bound TT.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure ?x ?e ?Cv)) ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f',
      E3 : @step T _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (update_x_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
        try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end.
    ss. des. eapply relax_ctx_bound; eauto.
    s.
    eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m_f); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t_f) (t' := t); eauto.
    ii.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure ?x ?e ?Cv)) ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ (?t_up !-> ?v'; ?m_up) (Ctx ?C_up') ?m_up' ?f ?f',
      E3 : @step T _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (IHEVAL3 _ _ _ _ _ _ (t_up !-> v'; m_up) t_up C_up' m_up' (tick C m'' t'' x v) f f');
      eauto
    end.
    split; ii; ss; des; clarify; do 5 solve_leb1.
    lebt t. eauto. apply leb_refl.
    ii. des; repeat des_hyp; des; clarify.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs _ ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') _,
      E3 : @step TT _ _ _ _ (Rs (EVal (Closure ?x' ?e' ?Cv')) ?m'' ?t''),
      ISO : iso _ _ (Ctx ?Cv') ?m'' ?f ?f' |- _ =>
      exists (Rs (EVal (Closure x' e' Cv')) m'' t''); exists f; exists f'
    end.
    repeat (split; eauto); ii;
    repeat rrw;
    try match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL; eauto.
    ii; des; repeat des_hyp; clarify.
    exists (Cf e2 mv m t). exists g. exists g'.
    repeat (split; eauto).
  - exploit IHEVAL1; eauto.
    ii; des; repeat des_hyp; clarify.
    gen_time_bound TT.
    exploit (IHEVAL2 _ _ _ _ _ C' _ _ mv m t); eauto.
    ii; des; repeat des_hyp; clarify.
    exists (Rs V0 m1 t1). exists g0. exists g'0.
    repeat (split; eauto);
    ii; repeat rw; try solve_leb; reflexivity.
  - exploit (@m_var_equiv T _ _ TT); eauto.
    ii; des. repeat eexists; eauto.
  - exploit IHEVAL; eauto.
    ii; des; repeat des_hyp; clarify.
    des; clarify.
    gen_time_bound TT.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal ?v) ?m' ?t'),
      ISO : iso _ ?m_up _ _ ?f ?f' |-
      context [iso (Ctx (dy_binde ?x ?t_up ?Cv')) (?t_up !-> ?v'; ?m_up) _ _ _ _] =>
      exists (Cf e2 (dy_binde x (tick C m' t' x v) C) 
        ((tick C m' t' x v) !-> v; m') (tick C m' t' x v));
      exploit (update_x_equiv _ t_up _ (tick C m' t' x v) v' v Cv' C m_up m' f f' x);
      try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end.
    ss. des. eapply relax_ctx_bound; eauto.
    s.
    eapply extend_mem_equiv with (t := t0) (m := m0) (m' := m'0) (t' := t'0);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m'0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0) (t' := t'0); eauto.
    ii.
    match goal with
    | _ : iso _ _ _ _ ?f ?f' |- _ =>
      exists f; exists f'
    end.
    repeat (split; eauto); ii;
    match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL1; eauto.
    ii; des; repeat des_hyp; clarify.
    des; clarify.
    gen_time_bound TT.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal ?v) ?m' ?t'),
      ISO : iso _ ?m_up _ _ ?f ?f',
      E2 : @step T _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (update_x_equiv _ t_up _ (tick C m' t' x v) v' v Cv' C m_up m' f f' x);
      try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end.
    ss. des. eapply relax_ctx_bound; eauto.
    s.
    eapply extend_mem_equiv with (t := t0) (m := m0) (m' := m'0) (t' := t'0);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m'0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0) (t' := t'0); eauto.
    ii.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal ?v) ?m' ?t'),
      ISO : iso _ (?t_up !-> ?v'; ?m_up) (Ctx ?C_up') ?m_up' ?f ?f',
      E2 : @step T _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (IHEVAL2 _ _ _ _ _ _ (t_up !-> v'; m_up) t_up C_up' m_up' (tick C m' t' x v) f f');
      eauto
    end.
    split; ii; ss; des; clarify; do 5 solve_leb1.
    lebt t'0. eauto. apply leb_refl.
    ii. des; repeat des_hyp; des; clarify.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs _ ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ (dy_binde _ _ ?C) _ _) (Rs (MVal ?mv) ?m'' ?t''),
      ISO : iso _ _ (Ctx ?mv) ?m'' ?f ?f' |- _ =>
      exists (Rs (MVal mv) m'' t''); exists f; exists f'
    end.
    repeat (split; eauto); ii;
    repeat rrw;
    try match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exists (Cf e2 (dy_bindm M mv C'0) m t). exists g. exists g'.
    exploit (@update_M_equiv T _ _ TT _ _ C' mv C0 C'0 _ _ g g' M); eauto.
    s.
    eapply extend_mem_equiv with (t := t0) (m := m0) (m' := m'0) (t' := t'0);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m'0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0) (t' := t'0); eauto.
    ii.
    repeat (split; eauto).
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exploit (@update_M_equiv T _ _ TT _ _ C' mv C0 C'0 _ _ g g' M); eauto.
    s.
    eapply extend_mem_equiv with (t := t0) (m := m0) (m' := m'0) (t' := t'0);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m'0); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0) (t' := t'0); eauto.
    ii.
    exploit (IHEVAL2 _ _ _ _ _ _ _ _ (dy_bindm M mv C'0) m t g g'); eauto.
    ss. des; eauto. split; eauto.
    ii; ss; des; clarify; do 5 solve_leb1.
    lebt t'0. eauto. apply leb_refl.
    ii; des. exists cf_r'.
    repeat des_hyp; des; clarify. exists g0. exists g'0.
    repeat (split; eauto);
    ii; repeat rw; solve [reflexivity | solve_leb].
Qed.
