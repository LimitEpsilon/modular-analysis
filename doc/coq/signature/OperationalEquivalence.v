From Signature Require Import Bound.

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
    match goal with
    | _ : Some ?v = read _ _ |- _ =>
      exists v; split; try (rewrite <- EQm in *; eauto)
    end; try split; eauto;
    match goal with
    | _ => erewrite <- IHp; eauto; 
      match goal with 
      | |- ?G => first [ has_evar G; fail 1 | idtac ] 
      end
    | _ => erewrite IHp; eauto;
      match goal with
      | |- ?G => first [has_evar G; fail 1 | idtac]
      end
    end;
    match goal with
    | BD : time_bound_m ?m ?t,
      LE : leb ?t' ?t = true |- _ =>
      exploit (time_bound_read m t t'); eauto; rrw
    end;
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
  - des_hyp; des; clarify;
    match goal with
    | BD : time_bound_m ?m ?t,
      LE : leb ?t' ?t = true |- _ =>
      exploit (time_bound_read m t t'); eauto
    end;
    rewrite <- VALp; ii; ss; des;
    erewrite IHp; eauto; s; eauto.
Qed.

Lemma e_var_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall C C' m m' (f : T -> TT) f' addr x v
    (ISO : iso (Ctx C) m (Ctx C') m' f f')
    (ADDR : addr_x C x = Some addr)
    (ACCESS : read m addr = Some v),
  exists Cv',
    addr_x C' x = Some (f addr) /\
    match v with
    | Closure ev Cv => 
      read m' (f addr) = Some (Closure ev Cv') /\
      iso (Ctx Cv) m (Ctx Cv') m' f f'
    end.
Proof.
  ii. destruct ISO as [ISO ISO'].
  destruct v as [ev Cv];
  match goal with
  | _ : read _ _ = Some (Closure ?ev ?Cv) |- _ =>
    exploit (ISO (Px x addr (Pv ev Pnil)));
    s; repeat rw
  end;
  match goal with
  | |- _ -> _ =>
    ii; repeat des_hyp; des; clarify;
    repeat des_hyp; des; clarify;
    eexists; do 2 (split; eauto)
  | _ => split; eauto; eexists; split; eauto; s; eauto
  end; split; ii.
  - exploit (ISO (Px x addr (Pv e p))).
    s. repeat rw. split; eauto.
    eexists. split; eauto. s. eauto.
    s. repeat rrw.
    ii; ss; repeat des_hyp; des; clarify.
    des; eauto.
  - exploit (ISO' (Px x (f addr) (Pv e p'))).
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
      exploit (vpath_root_bound p (Ctx C0) m (t0 !-> Closure e0 C0; m)); eauto.
      ii. s. rw; eauto.
      intros RR. rewrite <- RR in *.
      exploit (pmap_root_bound p (Ctx C0) m f (fun t' => if eqb t' t0 then t_up' else f t') t);
      eauto. ii. rewrite eqb_comm. rw; eauto.
      intros RR'. rewrite RR'.
      destruct EQUIVv0 as [EQv EQv'].
      exploit EQv; eauto. ii; des.
      exploit (pmap_root_bound (pmap f p) (Ctx C1) m' f' (fun t' => if eqb t' t_up' then t0 else f' t')); eauto.
      ii. rewrite eqb_comm. rw; eauto. rw. ii. rw.
      repeat (split; eauto).
      eexists. split. reflexivity. s. split. eauto.
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_addr C x0); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p (Ptr t0) m (t_up !-> Closure e0 C0; m)); eauto.
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
      exploit (vpath_root_bound p (Ctx d) m (t_up !-> Closure e0 C0; m)); eauto.
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
      exploit (vpath_root_bound p' (Ctx C1) m' (t0 !-> Closure e0 C1; m')); eauto.
      ii. s. rw; eauto.
      intros RR. rewrite <- RR in *.
      exploit (pmap_root_bound p' (Ctx C1) m' f' (fun t' => if eqb t' t0 then t_up else f' t') t');
      eauto. ii. rewrite eqb_comm. rw; eauto.
      intros RR'. rewrite RR'.
      destruct EQUIVv0 as [EQv EQv'].
      exploit EQv'; eauto. ii; des.
      exploit (pmap_root_bound (pmap f' p') (Ctx C0) m f (fun t' => if eqb t' t_up then t0 else f t')); eauto.
      ii. rewrite eqb_comm. rw; eauto. rw. ii. rw.
      repeat (split; eauto).
      eexists. split. reflexivity. s. split. eauto.
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_addr C' x0); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p' (Ptr t0) m' (t_up' !-> Closure e0 C1; m')); eauto.
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
      exploit (vpath_root_bound p' (Ctx d) m' (t_up' !-> Closure e0 C1; m')); eauto.
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
    split; eauto. erewrite pmap_root_bound; eauto.
    ii; symmetry; eauto.
  - subst p. destruct ISO as [? ISO].
    erewrite <- pmap_root_bound; eauto.
    exploit ISO; eauto. ii; ss; des.
    split; eauto. erewrite pmap_root_bound; eauto.
    ii; symmetry; eauto.
Qed.

Lemma equiv_project `{TotalOrder T} `{TotalOrder TT} :
  forall s (C : dy_ctx T) (C' : dy_ctx TT) m m' f f' Cs
    (PROJ : project C s = Some Cs)
    (ISO : iso (Ctx C) m (Ctx C') m' f f'),
  exists Cs',
    project C' s = Some Cs' /\
    iso (Ctx Cs) m (Ctx Cs') m' f f'.
Proof.
  induction s; ii; ss; clarify.
  - eexists; split; eauto.
    split; ii; ss;
    destruct p eqn:Heqp; ss; clarify;
    destruct p' eqn:Heqp'; ss.
  - repeat des_hyp; clarify.
    exploit IHs; eauto. ii; des.
    exists (dy_binde x (f t) Cs').
    destruct ISO as [ISO ISO'].
    exploit (ISO (Px x t Pnil)); s; rw; eauto.
    ii; repeat des_hyp; des; clarify.
    split; eauto.
    split; ii; ss.
    + destruct p; ii; ss; repeat des_hyp; des; clarify.
      rewrite eqb_ID_eq in *; clarify.
      exploit (ISO (Px x t0 p)). s. rw. eauto.
      s. repeat rw. eauto.
      all:match goal with
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : addr_x ?C ?x = Some ?t |-
        context [addr_x ?C' ?x] =>
        destruct ISO as [ISO ?];
        exploit (ISO (Px x t p)); s; try rw; eauto
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : ctx_M ?C ?M = Some ?C_M |-
        context [ctx_M ?C' ?M] =>
        destruct ISO as [ISO ?];
        exploit (ISO (PM M p)); s; try rw; eauto
      end.
    + destruct p'; ii; ss; repeat des_hyp; des; clarify.
      rewrite eqb_ID_eq in *; clarify.
      exploit (ISO' (Px x (f t) p')). s. rw. eauto.
      s. repeat rw. eauto.
      all:match goal with
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : addr_x ?C' ?x = Some ?t |-
        context [addr_x ?C ?x] =>
        destruct ISO as [? ISO];
        exploit (ISO (Px x t p')); s; try rw; eauto
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : ctx_M ?C' ?M = Some ?C_M |-
        context [ctx_M ?C ?M] =>
        destruct ISO as [? ISO];
        exploit (ISO (PM M p')); s; try rw; eauto
      end.
  - repeat des_hyp; clarify.
    destruct ISO as [ISO ISO'].
    exploit (ISO (PM M Pnil)). s. rw. eauto.
    ii. ss.
    destruct (ctx_M C' M) as [d' | ] eqn:HeqCM; des; clarify.
    exploit (IHs1 d d' m m' f f'); eauto.
    split; ii.
    exploit (ISO (PM M p)). s. rw. eauto. s. rw.
    ii; des; clarify.
    exploit (ISO' (PM M p')). s. rw. eauto. s. rw.
    ii; des; clarify.
    ii; des.
    exploit (IHs2 C C' m m' f f'); eauto. split; eauto.
    ii; des.
    exists (dy_bindm M Cs' Cs'0).
    do 2 match goal with
    | RR : project _ _ = _ |- _ => rewrite RR
    end. split; eauto.
    split; ii.
    + destruct p; ss; repeat des_hyp; des; clarify; cycle 1.
      rewrite eqb_ID_eq in *; clarify.
      all:match goal with
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        VAL : valid_path (Ctx ?C) ?m ?p |- _ =>
        destruct ISO as [ISO ?];
        exploit (ISO p); s; try rw; eauto;
        ii; des; rw; eauto
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : addr_x ?C ?x = Some ?t |-
        context [addr_x ?C' ?x] =>
        destruct ISO as [ISO ?];
        exploit (ISO (Px x t p)); s; try rw; eauto
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : ctx_M ?C ?M = Some ?C_M |-
        context [ctx_M ?C' ?M] =>
        destruct ISO as [ISO ?];
        exploit (ISO (PM M p)); s; try rw; eauto
      end.
    + destruct p'; ss; repeat des_hyp; des; clarify; cycle 1.
      rewrite eqb_ID_eq in *; clarify.
      all:match goal with
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        VAL : valid_path (Ctx ?C') ?m' ?p |- _ =>
        destruct ISO as [? ISO];
        exploit (ISO p); s; try rw; eauto;
        ii; des; rw; eauto
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : addr_x ?C' ?x = Some ?t |-
        context [addr_x ?C ?x] =>
        destruct ISO as [? ISO];
        exploit (ISO (Px x t p')); s; try rw; eauto
      | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
        RR : ctx_M ?C' ?M = Some ?C_M |-
        context [ctx_M ?C ?M] =>
        destruct ISO as [? ISO];
        exploit (ISO (PM M p')); s; try rw; eauto
      end.
Qed.

Lemma equiv_inject `{TotalOrder T} `{TotalOrder TT} :
  forall (C1 : dy_ctx T) (C1' : dy_ctx TT) C2 C2' m m' f f'
    (ISO1 : iso (Ctx C1) m (Ctx C1') m' f f')
    (ISO2 : iso (Ctx C2) m (Ctx C2') m' f f'),
  iso (Ctx (C1[|C2|])) m (Ctx (C1'[|C2'|])) m' f f'.
Proof.
  intros.
  split; ii.
  - destruct p; ii; ss;
    repeat rewrite inject_addr_x in *;
    repeat rewrite inject_ctx_M in *;
    repeat des_hyp; des; clarify;
    match goal with
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : addr_x ?C ?x = Some ?t |-
      context [addr_x ?C' ?x] =>
      destruct ISO as [ISO ?];
      exploit (ISO (Px x t p)); s; try rw; eauto
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : ctx_M ?C ?M = Some ?C_M |-
      context [ctx_M ?C' ?M] =>
      destruct ISO as [ISO ?];
      exploit (ISO (PM M p)); s; try rw; eauto
    end; ii; repeat des_hyp; des; clarify;
    match goal with
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : addr_x ?C ?x = None |-
      context [addr_x ?C' ?x] =>
      destruct (addr_x C' x) eqn:ADDR;
      match goal with
      | _ : addr_x C' x = Some ?t |- _ =>
        destruct ISO as [? ISO];
        exploit (ISO (Px x t Pnil));
        s; rw; eauto; ss; repeat rw; ii; des; clarify
      | _ => repeat rw; eauto
      end
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : ctx_M ?C ?M = None |-
      context [ctx_M ?C' ?M] =>
      destruct (ctx_M C' M) eqn:CTX;
      match goal with
      | _ : ctx_M C' M = Some _ |- _ =>
        destruct ISO as [? ISO];
        exploit (ISO (PM M Pnil));
        s; rw; eauto; ss; repeat rw; ii; des; clarify
      | _ => repeat rw; eauto
      end
    | _ => repeat rw; eauto
    end.
  - destruct p'; ii; ss;
    repeat rewrite inject_addr_x in *;
    repeat rewrite inject_ctx_M in *;
    repeat des_hyp; des; clarify;
    match goal with
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : addr_x ?C' ?x = Some ?t |-
      context [addr_x ?C ?x] =>
      destruct ISO as [? ISO];
      exploit (ISO (Px x t p')); s; try rw; eauto
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : ctx_M ?C' ?M = Some ?C_M |-
      context [ctx_M ?C ?M] =>
      destruct ISO as [? ISO];
      exploit (ISO (PM M p')); s; try rw; eauto
    end; ii; repeat des_hyp; des; clarify;
    match goal with
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : addr_x ?C' ?x = None |-
      context [addr_x ?C ?x] =>
      destruct (addr_x C x) eqn:ADDR;
      match goal with
      | _ : addr_x C x = Some ?t |- _ =>
        destruct ISO as [ISO ?];
        exploit (ISO (Px x t Pnil));
        s; rw; eauto; ss; repeat rw; ii; des; clarify
      | _ => repeat rw; eauto
      end
    | ISO : iso (Ctx ?C) ?m (Ctx ?C') ?m' _ _,
      RR : ctx_M ?C' ?M = None |-
      context [ctx_M ?C ?M] =>
      destruct (ctx_M C M) eqn:CTX;
      match goal with
      | _ : ctx_M C M = Some _ |- _ =>
        destruct ISO as [ISO ?];
        exploit (ISO (PM M Pnil));
        s; rw; eauto; ss; repeat rw; ii; des; clarify
      | _ => repeat rw; eauto
      end
    | _ => repeat rw; eauto
    end.
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
  - destruct v;
    exploit (@e_var_equiv T _ _ TT); eauto;
    ii; des; eexists; exists f; exists f';
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
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto;
    try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    all:match goal with
    | E1 : @step ?TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_fn ?x ?e) ?Cv)) ?m' ?t'),
      E2 : @step ?TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f' |-
      context [iso (Ctx (dy_binde ?x ?t_up ?Cv')) (?t_up !-> ?v'; ?m_up) _ _ _ _] =>
      exists (Cf e (dy_binde x (tick C m'' t'' x v) Cv) 
        ((tick C m'' t'' x v) !-> v; m'') (tick C m'' t'' x v));
      exploit (update_x_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
      try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end; s.
    all: try match goal with
    | |- time_bound_C _ _ =>
      ss; des; eapply relax_ctx_bound; eauto
    | |- iso _ _ _ _ _ _ =>
      eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
      ss; des; eauto
    end.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
    all: ii; match goal with
    | _ : iso _ _ _ _ ?f ?f' |- _ =>
      exists f; exists f'
    end;
    repeat (split; eauto); ii;
    match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto;
    try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    exploit (equiv_project s_M C_v mv m_a _); eauto; ii; des.
    all:match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_ft ?M ?s ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (MVal ?mv) ?m'' ?t''),
      PROJ : project ?mv ?s = Some ?Cs,
      ISO : iso _ _ _ ?m'' ?f ?f' |- _ =>
      exists (Cf e (dy_bindm M Cs Cv) m'' t''); exists f; exists f'
    end.
    repeat lazymatch goal with
    | |- iso _ _ _ _ _ _ => fail
    | _ => split; eauto
    end.
    all: try (ii; repeat rw; solve[reflexivity | solve_leb]).
    eapply update_M_equiv; s; eauto.
    eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
    ss; des; eauto.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto.
    all:try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    all:match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_fn ?x ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f',
      E3 : @step _ _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (update_x_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
        try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end; s.
    all: try match goal with
    | |- time_bound_C _ _ =>
      ss; des; eapply relax_ctx_bound; eauto
    | |- iso _ _ _ _ _ _ =>
      eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
      ss; des; eauto
    end.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
    all: ii; match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_fn ?x ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ (?t_up !-> ?v'; ?m_up) (Ctx ?C_up') ?m_up' ?f ?f',
      E3 : @step _ _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (IHEVAL3 _ _ _ _ _ _ (t_up !-> v'; m_up) t_up C_up' m_up' (tick C m'' t'' x v) f f');
      eauto
    end.
    all: try (split; ii; ss; des; clarify; do 5 solve_leb1).
    all: try solve [apply leb_refl | lebt t; eauto].
    all: ii; des; repeat des_hyp; des; clarify;
    match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs _ ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') _,
      E3 : @step _ _ _ _ _ (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ _ _ ?m'' ?f ?f' |- _ =>
      exists (Rs (EVal v) m'' t''); exists f; exists f'
    end.
    all: repeat (split; eauto); ii;
    repeat rrw;
    try match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto;
    try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m0 t0); eauto; ss; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m'0 t'0); eauto; ss; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    all: exploit (equiv_project s_M C_v mv m_a _); eauto; ii; des.
    all: match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_ft ?M ?s ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (MVal ?mv) ?m'' ?t''),
      PROJ : project ?mv ?s = Some ?Cs,
      BD : time_bound_ρ (Rs (MVal ?mv) _ ?t_v),
      ISO : iso _ _ _ ?m'' ?f ?f',
      E3 : @step _ _ _ _ (Cf _ _ ?m_up _) _ |- _ =>
      exploit (time_bound_project s mv t_v);
      try solve [ss; des; eauto]; rw; ii;
      exploit (IHEVAL3 _ _ _ _ _ _ m_up _ (dy_bindm M Cs Cv) m'' t'' f f');
      eauto
    end.
    all:try (split; ii; ss; des; try do 5 solve_leb1;
      solve [apply leb_refl | lebt t; eauto]).
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      eapply update_M_equiv; s; eauto;
      eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
      ss; des; eauto
    end.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
    all: ii; des; repeat des_hyp; des; clarify;
    match goal with
    | _ : {| _ ~> (Rs ?V ?m ?t) |},
      _ : iso _ _ _ ?m ?f ?f' |- _ =>
      exists (Rs V m t); exists f; exists f'
    end.
    all: repeat (split; eauto).
    all: ii; repeat rrw; try reflexivity; rw; solve_leb.
  - exploit IHEVAL; eauto.
    ii; des; repeat des_hyp; des; clarify.
    eexists. exists g. exists g'.
    split; eauto. split; eauto.
    instantiate (1 := (Cf e2 mv m t)).
    split; eauto.
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
    s. apply equiv_inject; eauto.
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
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto;
    try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    all:match goal with
    | E1 : @step ?TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_fn ?x ?e) ?Cv)) ?m' ?t'),
      E2 : @step ?TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f' |-
      context [iso (Ctx (dy_binde ?x ?t_up ?Cv')) (?t_up !-> ?v'; ?m_up) _ _ _ _] =>
      exists (Cf e (dy_binde x (tick C m'' t'' x v) Cv) 
        ((tick C m'' t'' x v) !-> v; m'') (tick C m'' t'' x v));
      exploit (update_x_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
      try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end; s.
    all: try match goal with
    | |- time_bound_C _ _ =>
      ss; des; eapply relax_ctx_bound; eauto
    | |- iso _ _ _ _ _ _ =>
      eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
      ss; des; eauto
    end.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
    all: ii; match goal with
    | _ : iso _ _ _ _ ?f ?f' |- _ =>
      exists f; exists f'
    end;
    repeat (split; eauto); ii;
    match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto;
    try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    exploit (equiv_project s_M C_v mv m_a _); eauto; ii; des.
    all:match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_ft ?M ?s ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (MVal ?mv) ?m'' ?t''),
      PROJ : project ?mv ?s = Some ?Cs,
      ISO : iso _ _ _ ?m'' ?f ?f' |- _ =>
      exists (Cf e (dy_bindm M Cs Cv) m'' t''); exists f; exists f'
    end.
    repeat lazymatch goal with
    | |- iso _ _ _ _ _ _ => fail
    | _ => split; eauto
    end.
    all: try (ii; repeat rw; solve[reflexivity | solve_leb]).
    eapply update_M_equiv; s; eauto.
    eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
    ss; des; eauto.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C'0 m t); eauto.
    all:try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    all:match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_fn ?x ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f',
      E3 : @step _ _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (update_x_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
        try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end; s.
    all: try match goal with
    | |- time_bound_C _ _ =>
      ss; des; eapply relax_ctx_bound; eauto
    | |- iso _ _ _ _ _ _ =>
      eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
      ss; des; eauto
    end.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
    all: ii; match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_fn ?x ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ (?t_up !-> ?v'; ?m_up) (Ctx ?C_up') ?m_up' ?f ?f',
      E3 : @step _ _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (IHEVAL3 _ _ _ _ _ _ (t_up !-> v'; m_up) t_up C_up' m_up' (tick C m'' t'' x v) f f');
      eauto
    end.
    all: try (split; ii; ss; des; clarify; do 5 solve_leb1).
    all: try solve [apply leb_refl | lebt t; eauto].
    all: ii; des; repeat des_hyp; des; clarify.
    all: exploit (equiv_project s C' mv m' _); eauto; ii; des.
    all: match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs _ ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') _,
      E3 : @step _ _ _ _ _ (Rs (MVal ?mv) ?m'' ?t''),
      PROJ : project ?mv _ = Some ?Cs,
      ISO : iso _ _ _ ?m'' ?f ?f' |- _ =>
      exists (Rs (MVal (Cs[|C|])) m'' t''); exists f; exists f'
    end.
    all: repeat lazymatch goal with
    | |- iso _ _ _ _ _ _ => fail
    | _ => split; eauto
    end;
    match goal with
    | |- iso _ _ _ _ _ _ =>
      eapply equiv_inject; eauto
    | _ => ii;
      repeat rrw;
      try match goal with
      | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
        exploit (leb_t_neq_tick C m x v a t);
        try solve_leb
      end; ii; repeat rw;
      try solve [reflexivity | solve_leb]
    end.
    all:eapply extend_mem_equiv with (t := t0) (m := m0) (m' := m'0) (t' := t'0).
    all:try solve [ss; des; assumption].
    all:try match goal with
    | _ : {| (Cf _ _ ?m1 _) ~> (Rs _ ?m2 _) |},
      _ : {| (Cf _ _ ?m2 _) ~> _ |},
      _ : {| (Cf _ _ ?m3 _) ~> (Rs _ ?m4 _) |} |-
      forall _, _ -> read ?m1 _ = read ?m4 _ =>
      exploit (extend_mem _ _ m1); eauto; s;
      exploit (extend_mem _ _ m2); eauto; s;
      exploit (extend_mem _ _ m3); eauto; s
    end.
    all:match goal with
    | |- iso _ _ _ _ _ _ =>
      ss; des;
      eapply extend_iso_equiv with (t := t0) (t' := t'0) (f := f) (f' := f');
      eauto
    | |- _ /\ _ =>
      split; ii; ss; repeat des_hyp; des; clarify;
      do 5 solve_leb1; try apply leb_refl; lebt t; eauto
    | _ => ii;
      repeat rw;
      try match goal with
      | |- context [eqb (tick ?C ?m ?t ?x ?v) ?a] =>
        rewrite eqb_comm;
        exploit (leb_t_neq_tick C m x v a t);
        try solve_leb
      end; ii; repeat rw;
      try solve [reflexivity | solve_leb]
    end.
    all: ii; repeat rrw;
    try match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t)
    end; ii;
    solve [rw; reflexivity | rw; solve_leb | solve_leb].
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify;
    gen_time_bound TT;
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C'0 m t); eauto;
    try solve [ss; des; eauto using relax_ctx_bound].
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      instantiate (1 := g'); instantiate (1 := g);
      eapply extend_mem_equiv with (t := t0); eauto
    end.
    all:try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m0 t0); eauto; ss; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m'0 t'0); eauto; ss; ii; symmetry; eauto]
    end.
    all: try solve [eapply extend_iso_equiv with (t := t0); eauto].
    all: ii; des; repeat des_hyp; des; clarify; gen_time_bound TT.
    all: exploit (equiv_project s_M C_v mv m_a _); eauto; ii; des.
    all: match goal with
    | E1 : @step _ _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure (v_ft ?M ?s ?e) ?Cv)) ?m' ?t'),
      E2 : @step _ _ _ _ (Cf _ ?C ?m' ?t') (Rs (MVal ?mv) ?m'' ?t''),
      PROJ : project ?mv ?s = Some ?Cs,
      BD : time_bound_ρ (Rs (MVal ?mv) _ ?t_v),
      ISO : iso _ ?m_up _ ?m'' ?f ?f',
      E3 : @step _ _ _ _ (Cf _ _ ?m_up _) _ |- _ =>
      exploit (time_bound_project s mv t_v);
      try solve [ss; des; eauto]; rw; ii;
      exploit (IHEVAL3 _ _ _ _ _ _ m_up _ (dy_bindm M Cs Cv) m'' t'' f f');
      eauto
    end.
    all:try (split; ii; ss; des; try do 5 solve_leb1;
      solve [apply leb_refl | lebt t; eauto]).
    all:try match goal with
    | |- iso _ _ _ _ _ _ =>
      eapply update_M_equiv; s; eauto;
      eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
      ss; des; eauto
    end.
    all: try match goal with
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem T _ _ _ _ _ m_f); eauto; s; eauto; ii; symmetry; eauto]
    | |- forall _, _ -> _ =>
      solve [exploit (@extend_mem TT _ _ _ _ _ m); eauto; s; eauto; ii; symmetry; eauto]
    end.
    all: try match goal with
    | |- iso _ _ _ _ _ _ => eapply extend_iso_equiv with (t := t_f) (t' := t); eauto
    end.
    all: ii; des; repeat des_hyp; des; clarify.
    exploit (equiv_project s C' mv0); eauto. ii; des.
    match goal with
    | _ : {| _ ~> (Rs (MVal ?C) ?m ?t) |},
      _ : project ?C ?s = Some ?Cs,
      _ : iso _ _ _ ?m ?f ?f' |- _ =>
      exists (Rs (MVal (Cs[|C'0|])) m t); exists f; exists f'
    end.
    all: repeat lazymatch goal with
    | |- iso _ _ _ _ _ _ => fail
    | _ => split; eauto
    end;
    match goal with
    | |- iso _ _ _ _ _ _ =>
      eapply equiv_inject; eauto
    | _ => ii; repeat rrw; try reflexivity; rw; solve_leb
    end.
    all:eapply extend_mem_equiv with (t := t0) (m := m0) (m' := m'0) (t' := t'0).
    all:try solve [ss; des; assumption].
    all:try match goal with
    | _ : {| (Cf _ _ ?m1 _) ~> (Rs _ ?m2 _) |},
      _ : {| (Cf _ _ ?m2 _) ~> _ |},
      _ : {| (Cf _ _ ?m3 _) ~> (Rs _ ?m4 _) |} |-
      forall _, _ -> read ?m1 _ = read ?m4 _ =>
      exploit (extend_mem _ _ m1); eauto; s;
      exploit (extend_mem _ _ m2); eauto; s;
      exploit (extend_mem _ _ m3); eauto; s
    | |- iso _ _ _ _ _ _ =>
      ss; des;
      eapply extend_iso_equiv with (t := t0) (t' := t'0) (f := f) (f' := f');
      eauto
    end.
    all: try match goal with
    | |- _ /\ _ =>
      split; ii; ss; repeat des_hyp; des; clarify;
      do 5 solve_leb1; try apply leb_refl; lebt t; eauto
    | _ => ii; repeat rrw;
      solve [reflexivity | rw; solve_leb]
    end.
Qed.
