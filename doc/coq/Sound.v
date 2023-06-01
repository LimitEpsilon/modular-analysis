From MODULAR Require Export Abstract.
From MODULAR Require Export Concrete.

Fixpoint dy_ctx_bound C t :=
  match C with
  | [||] => True
  | dy_c_lam _ t' C'
  | dy_c_lete _ t' C' => t' < t /\ dy_ctx_bound C' t
  | dy_c_letm _ CM C' => dy_ctx_bound CM t /\ dy_ctx_bound C' t
  end.

Fixpoint p_bound p t :=
  match p with
  | [] => True
  | hd :: tl => hd < t /\ p_bound tl t
  end.

Definition time_bound C st :=
  match st with
  | ST mem t =>
    dy_ctx_bound C t /\
    (forall p (NBOUND : ~(p_bound p t)),
      mem p = None) /\
    (forall p (BOUND : p_bound p t),
      match mem p with
      | None => True
      | Some (Val _ _ C') => dy_ctx_bound C' t
      end)
  end.

Lemma p_bound_or_not :
  forall p t,
    p_bound p t \/ ~(p_bound p t).
Proof.
  induction p.
  - intros; left; simpl; eauto.
  - intros; simpl.
    specialize (IHp t). assert (H : a < t \/ ~ a < t). nia.
    destruct IHp as [BOUND | NBOUND]; destruct H as [BOUND' | NBOUND'].
    + left; split; eauto.
    + right. unfold not. intros H; destruct H.
      apply NBOUND' in H. contradiction H.
    + right. unfold not. intros H; destruct H.
      apply NBOUND in H0. contradiction H0.
    + right. unfold not. intros H; destruct H.
      apply NBOUND' in H. contradiction H.
Qed.

Definition trans_t := Concrete.time -> Abstract.time.

Definition eq_bound_α t (α : trans_t) α' :=
  forall t' (LE : t' <= t), α t' = α' t'.

Fixpoint trans_ctx (α : trans_t) C :=
  match C with
  | [||] => [#||#]
  | dy_c_lam x t C' => Abstract.dy_c_lam x (α t) (trans_ctx α C')
  | dy_c_lete x t C' => Abstract.dy_c_lete x (α t) (trans_ctx α C')
  | dy_c_letm M CM C' => Abstract.dy_c_letm M (trans_ctx α CM) (trans_ctx α C')
  end.

Definition sound α C st abs_C abs_st :=
  match abs_st with
  | Abstract.ST abs_mem abs_t =>
    match st with
    | ST mem t =>
      α t = abs_t /\
      trans_ctx α C = abs_C /\
      forall p (BOUND : p_bound p t),
        match mem p with
        | None => True
        | Some (Val v pf Cv) =>
          let l := abs_mem (map α p) in
          In (Abstract.Val v pf (trans_ctx α Cv)) l
        end
    end
  end.

Lemma trans_ctx_addr :
  forall α C x,
    Abstract.addr_x (trans_ctx α C) x = List.map α (addr_x C x).
Proof.
  induction C; eauto.
  - intros. specialize (IHC x0).
    simpl. rewrite IHC.
    destruct (addr_x C x0); simpl; eauto.
    destruct (eq_eid x0 x); eauto.
    rewrite map_app. eauto.
  - intros. specialize (IHC x0).
    simpl. rewrite IHC.
    destruct (addr_x C x0); simpl; eauto.
    destruct (eq_eid x0 x); eauto.
    rewrite map_app. eauto.
Qed.

Lemma time_increase_e :
  forall C st e e' st'
         (EVAL : EevalR C st e e' st'),
    match st with
    | ST _ t =>
      match st' with
      | ST _ t' => t <= t'
      end
    end.
Proof.
  apply (EevalR_ind_mut
    (fun C st e e' st'
         (EVAL : EevalR C st e e' st') =>
      match st with
      | ST _ t =>
        match st' with
        | ST _ t' => t <= t'
        end
      end)
    (fun C st m C' st'
         (EVAL : MevalR C st m C' st') =>
      match st with
      | ST _ t =>
        match st' with
        | ST _ t' => t <= t'
        end
      end)); 
      intros; 
      destruct st; try destruct st'; try destruct st_v; try destruct st_m; 
      try destruct st_m1; try destruct st_m2; try destruct st_lam;
      unfold update_t in *; simpl; try nia.
Qed.

Lemma time_increase_m :
  forall C st m C' st'
         (EVAL : MevalR C st m C' st'),
    match st with
    | ST _ t =>
      match st' with
      | ST _ t' => t <= t'
      end
    end.
Proof.
  apply (MevalR_ind_mut
    (fun C st e e' st'
         (EVAL : EevalR C st e e' st') =>
      match st with
      | ST _ t =>
        match st' with
        | ST _ t' => t <= t'
        end
      end)
    (fun C st m C' st'
         (EVAL : MevalR C st m C' st') =>
      match st with
      | ST _ t =>
        match st' with
        | ST _ t' => t <= t'
        end
      end)); 
      intros; 
      destruct st; try destruct st'; try destruct st_v; try destruct st_m; 
      try destruct st_m1; try destruct st_m2; try destruct st_lam;
      unfold update_t in *; simpl; try nia.
Qed.

Lemma relax_ctx_bound :
  forall C t1 t2 (BOUND : dy_ctx_bound C t1) (LE : t1 <= t2),
         dy_ctx_bound C t2.
Proof.
  induction C; intros; destruct BOUND; simpl in *; 
  repeat split; try nia;
  try eapply IHC; try eapply IHC1; try eapply IHC2; eauto.
Qed.

Lemma relax_p_bound :
  forall p t1 t2 (BOUND : p_bound p t1) (LE : t1 <= t2),
         p_bound p t2.
Proof.
  induction p; intros; destruct BOUND; simpl in *; 
  repeat split; try nia; eauto.
Qed.

Lemma p_bound_app :
  forall p1 p2 t,
    p_bound (p1 ++ p2) t <-> p_bound p1 t /\ p_bound p2 t.
Proof.
  induction p1; intros; split; intro H; try destruct H; simpl in *; eauto.
  - rewrite IHp1 in H0. destruct H0. repeat split; eauto.
  - rewrite IHp1. destruct H. repeat split; eauto.
Qed.

Lemma time_bound_addr :
  forall C x t,
    dy_ctx_bound C t -> p_bound (addr_x C x) t.
Proof.
  induction C; intros; simpl in *; destruct H; eauto.
  - specialize (IHC x0 t H0).
    destruct (addr_x C x0). destruct (eq_eid x0 x); simpl; eauto.
    rewrite p_bound_app with (p1 := t0 :: l) (p2 := [tx]).
    split; simpl; eauto.
  - specialize (IHC x0 t H0).
    destruct (addr_x C x0). destruct (eq_eid x0 x); simpl; eauto.
    rewrite p_bound_app with (p1 := t0 :: l) (p2 := [tx]).
    split; simpl; eauto.
Qed.

Lemma time_bound_level :
  forall C t,
    dy_ctx_bound C t -> p_bound (dy_level C) t.
Proof.
  induction C; intros; simpl in *; destruct H;
  try rewrite p_bound_app; try split; simpl; eauto.
Qed.

Lemma time_bound_ctx_M :
  forall C M t CM,
    ctx_M C M = Some CM ->
    dy_ctx_bound C t -> 
    dy_ctx_bound CM t.
Proof.
  induction C; intros; simpl in *.
  - inversion H.
  - eapply IHC. exact H. destruct H0; eauto.
  - eapply IHC. exact H. destruct H0; eauto.
  - remember (ctx_M C2 M0) as oCM.
    destruct oCM.
    + eapply IHC2. symmetry. inversion H; subst. exact HeqoCM.
      destruct H0; eauto.
    + destruct (eq_mid M0 M); inversion H; subst.
      destruct H0; eauto.
Qed.

Lemma plugin_ctx_bound :
  forall Cout Cin t,
    dy_ctx_bound (Cout[|Cin|]) t <-> dy_ctx_bound Cout t /\ dy_ctx_bound Cin t.
Proof.
  intros; split; intros H; induction Cout; repeat split; simpl in *; try nia; eauto;
  destruct H as [H' H'']; try specialize (IHCout H'') as HINT;
  try specialize (IHCout1 H'') as HINT; try specialize (IHCout2 H'') as HINT;
  try destruct HINT; eauto;
  try apply IHCout; destruct H'; try split; eauto.
Qed.

Lemma time_bound_e :
  forall C st e e' st'
         (EVAL : EevalR C st e e' st')
         (BOUND : time_bound C st),
    match e' with
    | Val _ _ C' => time_bound C' st'
    end.
Proof.
  apply (EevalR_ind_mut
    (fun C st e e' st'
         (EVAL : EevalR C st e e' st') =>
      forall (BOUND : time_bound C st),
        match e' with
        | Val _ _ C' => time_bound C' st'
        end)
    (fun C st m C' st'
         (EVAL : MevalR C st m C' st') =>
      forall (BOUND : time_bound C st), 
        time_bound C' st')); intros; simpl; eauto.
  - destruct v. unfold time_bound in *.
    destruct st. destruct BOUND as [? [? RR]].
    specialize (RR (addr_x C x)) as RR'.
    assert (p_bound (addr_x C x) t0). apply time_bound_addr. eauto.
    apply RR' in H1. inversion STATE; subst. 
    rewrite <- ACCESS in H1. repeat split; eauto.
  - specialize (H BOUND). 
    destruct v. destruct arg. 
    destruct st. destruct st_lam. destruct st_v.
    apply time_increase_e in ARG as time_inc1.
    apply time_increase_e in FN as time_inc2.
    apply time_increase_e in BODY as time_inc3.
    assert (time_bound C (ST mem1 t1)) as HINT.
    {
      simpl in H. destruct H as [? [? ?]]. 
      simpl; repeat split; eauto. 
      eapply relax_ctx_bound. 
      simpl in BOUND. destruct BOUND. exact d. eauto. 
    }
    specialize (H0 HINT).
    assert (p_bound (t :: dy_level C_lam) (update_t t)).
    {
      simpl in H. destruct H as [? [? ?]].
      simpl. split; unfold update_t; eauto.
      apply relax_p_bound with (t1 := t1).
      apply time_bound_level. eauto. nia.
    }
    apply H1; simpl. split.
    rewrite plugin_ctx_bound. split.
    simpl in H. destruct H as [? [? ?]].
    eapply relax_ctx_bound. exact H. unfold update_t. nia.
    simpl. split; eauto. simpl in H0. destruct H0 as [? [? ?]].
    split; intros;
    unfold update_m; remember (eq_p p (t :: dy_level C_lam)) as b;
    destruct b; symmetry in Heqb; try rewrite eq_p_eq in Heqb.
    + assert (p_bound p (update_t t)) as contra. { rewrite Heqb. eauto. }
      apply NBOUND in contra. inversion contra.
    + apply H3.
      unfold not. intros.
      assert (p_bound p (update_t t)) as contra. 
      { apply relax_p_bound with (t1 := t). eauto. unfold update_t; eauto. }
      apply NBOUND in contra. inversion contra.
    + apply relax_ctx_bound with (t1 := t). eauto. unfold update_t; eauto.
    + specialize (H4 p). remember (mem p) as access eqn:ACCESS.
      destruct access; eauto. destruct e0.
      apply relax_ctx_bound with (t1 := t). apply H4.
      pose proof (p_bound_or_not p t) as CASES.
      destruct CASES as [? | contra]; eauto. apply H3 in contra.
      rewrite contra in ACCESS. inversion ACCESS. unfold update_t. eauto.
  - apply H0. apply H. eauto.
  - destruct st. simpl in *. destruct BOUND as [? [? ?]].
    repeat split; eauto. eapply time_bound_ctx_M.
    symmetry. exact ACCESS. eauto.
  - specialize (H BOUND).
    destruct v_e. 
    destruct st. destruct st_m.
    apply time_increase_e in EVALe as time_inc1.
    apply time_increase_m in EVALm as time_inc2.
    assert (p_bound (t :: dy_level C) (update_t t)).
    {
      simpl in BOUND. destruct BOUND as [? [? ?]].
      simpl. split; unfold update_t; eauto.
      apply relax_p_bound with (t1 := t0).
      apply time_bound_level. eauto. nia.
    }
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in H. destruct H as [HH1 [HH2 HH3]].
    apply H0. simpl; split.
    rewrite plugin_ctx_bound; split.
    apply relax_ctx_bound with (t1 := t0).
    eauto. unfold update_t. nia. simpl; split; eauto.
    split; intros;
    unfold update_m; remember (eq_p p (t :: dy_level C)) as b;
    destruct b; symmetry in Heqb; try rewrite eq_p_eq in Heqb.
    + assert (p_bound p (update_t t)) as contra. { rewrite Heqb. eauto. }
      apply NBOUND in contra. inversion contra.
    + apply HH2. unfold not. intros.
      assert (p_bound p (update_t t)) as contra. 
      { apply relax_p_bound with (t1 := t). eauto. unfold update_t; eauto. }
      apply NBOUND in contra. inversion contra.
    + apply relax_ctx_bound with (t1 := t). eauto. unfold update_t; eauto.
    + specialize (HH3 p). remember (mem p) as access eqn:ACCESS.
      destruct access; eauto. destruct e0.
      apply relax_ctx_bound with (t1 := t). apply HH3.
      pose proof (p_bound_or_not p t) as CASES.
      destruct CASES as [? | contra]; eauto. apply HH2 in contra.
      rewrite contra in ACCESS. inversion ACCESS. unfold update_t. eauto.
  - specialize (H BOUND).
    destruct st. destruct st_m1. destruct st_m2.
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in H. destruct H as [HH1 [HH2 HH3]].
    apply time_increase_m in EVALm1 as time_inc1.
    apply time_increase_m in EVALm2 as time_inc2.
    apply H0. simpl. repeat split; eauto.
    rewrite plugin_ctx_bound. split.
    apply relax_ctx_bound with (t1 := t); eauto.
    simpl; split; eauto.
Qed.

Lemma time_bound_m :
  forall C st m C' st'
         (EVAL : MevalR C st m C' st')
         (BOUND : time_bound C st),
    time_bound C' st'.
Proof.
  apply (MevalR_ind_mut
    (fun C st e e' st'
         (EVAL : EevalR C st e e' st') =>
      forall (BOUND : time_bound C st),
        match e' with
        | Val _ _ C' => time_bound C' st'
        end)
    (fun C st m C' st'
         (EVAL : MevalR C st m C' st') =>
      forall (BOUND : time_bound C st), 
        time_bound C' st')); intros; simpl; eauto.
  - destruct v. unfold time_bound in *.
    destruct st. destruct BOUND as [? [? RR]].
    specialize (RR (addr_x C x)) as RR'.
    assert (p_bound (addr_x C x) t0). apply time_bound_addr. eauto.
    apply RR' in H1. inversion STATE; subst. 
    rewrite <- ACCESS in H1. repeat split; eauto.
  - specialize (H BOUND). 
    destruct v. destruct arg. 
    destruct st. destruct st_lam. destruct st_v.
    apply time_increase_e in ARG as time_inc1.
    apply time_increase_e in FN as time_inc2.
    apply time_increase_e in BODY as time_inc3.
    assert (time_bound C (ST mem1 t1)) as HINT.
    {
      simpl in H. destruct H as [? [? ?]]. 
      simpl; repeat split; eauto. 
      eapply relax_ctx_bound. 
      simpl in BOUND. destruct BOUND. exact d. eauto. 
    }
    specialize (H0 HINT).
    assert (p_bound (t :: dy_level C_lam) (update_t t)).
    {
      simpl in H. destruct H as [? [? ?]].
      simpl. split; unfold update_t; eauto.
      apply relax_p_bound with (t1 := t1).
      apply time_bound_level. eauto. nia.
    }
    apply H1; simpl. split.
    rewrite plugin_ctx_bound. split.
    simpl in H. destruct H as [? [? ?]].
    eapply relax_ctx_bound. exact H. unfold update_t. nia.
    simpl. split; eauto. simpl in H0. destruct H0 as [? [? ?]].
    split; intros;
    unfold update_m; remember (eq_p p (t :: dy_level C_lam)) as b;
    destruct b; symmetry in Heqb; try rewrite eq_p_eq in Heqb.
    + assert (p_bound p (update_t t)) as contra. { rewrite Heqb. eauto. }
      apply NBOUND in contra. inversion contra.
    + apply H3.
      unfold not. intros.
      assert (p_bound p (update_t t)) as contra. 
      { apply relax_p_bound with (t1 := t). eauto. unfold update_t; eauto. }
      apply NBOUND in contra. inversion contra.
    + apply relax_ctx_bound with (t1 := t). eauto. unfold update_t; eauto.
    + specialize (H4 p). remember (mem p) as access eqn:ACCESS.
      destruct access; eauto. destruct e0.
      apply relax_ctx_bound with (t1 := t). apply H4.
      pose proof (p_bound_or_not p t) as CASES.
      destruct CASES as [? | contra]; eauto. apply H3 in contra.
      rewrite contra in ACCESS. inversion ACCESS. unfold update_t. eauto.
  - apply H0. apply H. eauto.
  - destruct st. simpl in *. destruct BOUND as [? [? ?]].
    repeat split; eauto. eapply time_bound_ctx_M.
    symmetry. exact ACCESS. eauto.
  - specialize (H BOUND).
    destruct v_e. 
    destruct st. destruct st_m.
    apply time_increase_e in EVALe as time_inc1.
    apply time_increase_m in EVALm as time_inc2.
    assert (p_bound (t :: dy_level C) (update_t t)).
    {
      simpl in BOUND. destruct BOUND as [? [? ?]].
      simpl. split; unfold update_t; eauto.
      apply relax_p_bound with (t1 := t0).
      apply time_bound_level. eauto. nia.
    }
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in H. destruct H as [HH1 [HH2 HH3]].
    apply H0. simpl; split.
    rewrite plugin_ctx_bound; split.
    apply relax_ctx_bound with (t1 := t0).
    eauto. unfold update_t. nia. simpl; split; eauto.
    split; intros;
    unfold update_m; remember (eq_p p (t :: dy_level C)) as b;
    destruct b; symmetry in Heqb; try rewrite eq_p_eq in Heqb.
    + assert (p_bound p (update_t t)) as contra. { rewrite Heqb. eauto. }
      apply NBOUND in contra. inversion contra.
    + apply HH2. unfold not. intros.
      assert (p_bound p (update_t t)) as contra. 
      { apply relax_p_bound with (t1 := t). eauto. unfold update_t; eauto. }
      apply NBOUND in contra. inversion contra.
    + apply relax_ctx_bound with (t1 := t). eauto. unfold update_t; eauto.
    + specialize (HH3 p). remember (mem p) as access eqn:ACCESS.
      destruct access; eauto. destruct e0.
      apply relax_ctx_bound with (t1 := t). apply HH3.
      pose proof (p_bound_or_not p t) as CASES.
      destruct CASES as [? | contra]; eauto. apply HH2 in contra.
      rewrite contra in ACCESS. inversion ACCESS. unfold update_t. eauto.
  - specialize (H BOUND).
    destruct st. destruct st_m1. destruct st_m2.
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in H. destruct H as [HH1 [HH2 HH3]].
    apply time_increase_m in EVALm1 as time_inc1.
    apply time_increase_m in EVALm2 as time_inc2.
    apply H0. simpl. repeat split; eauto.
    rewrite plugin_ctx_bound. split.
    apply relax_ctx_bound with (t1 := t); eauto.
    simpl; split; eauto.
Qed.

Lemma plugin_trans_ctx :
  forall Cout Cin α,
    trans_ctx α (Cout[|Cin|]) = (trans_ctx α Cout [#|trans_ctx α Cin|#]).
Proof.
  induction Cout; intros; simpl; 
  try rewrite IHCout; try rewrite IHCout1; try rewrite IHCout2;
  eauto.
Qed.

Lemma bound_trans_ctx_eq :
  forall C t α α',
         dy_ctx_bound C t ->
         eq_bound_α t α α' ->
         trans_ctx α C = trans_ctx α' C.
Proof.
  intros.
  induction C; simpl; try rewrite IHC; 
  try rewrite IHC1; try rewrite IHC2; simpl in *; eauto;
  destruct H; eauto.
  unfold eq_bound_α in H0. rewrite H0; eauto. nia.
  unfold eq_bound_α in H0. rewrite H0; eauto. nia.
Qed.

Lemma level_trans_ctx_eq :
  forall C α α' t,
    eq_bound_α t α α' ->
    dy_ctx_bound C t ->
    Abstract.dy_level (trans_ctx α C) = map α' (dy_level C).
Proof.
  induction C; intros; simpl; eauto; try rewrite map_app; simpl;
  try erewrite IHC; simpl in H0; destruct H0; eauto.
  - assert (α tx = α' tx). red in H. apply H. nia. rewrite H0. eauto.
  - assert (α tx = α' tx). red in H. apply H. nia. rewrite H0. eauto.
Qed.

Lemma abs_eq_p_refl :
  forall p,
    Abstract.eq_p p p = true.
Proof.
  intros. apply Abstract.eq_p_eq. eauto.
Qed.

(* Set Printing Implicit. *)

Lemma sound_eval :
  forall C st e e' st'
         (EVAL : EevalR C st e e' st')
         (BOUND : time_bound C st)
         abs_C abs_st α
         (SOUND : sound α C st abs_C abs_st),
    exists abs_C' abs_st' α',
      match st with
      | ST _ t =>
        eq_bound_α t α α' /\
        match e' with
        | Val _ _ C' =>
          sound α' C' st' abs_C' abs_st'
        end
      end.
Proof.
  apply (EevalR_ind_mut 
    (fun C st e e' st'
         (EVAL : EevalR C st e e' st') =>
    forall
         (BOUND : time_bound C st)
         abs_C abs_st α
         (SOUND : sound α C st abs_C abs_st),
    exists abs_C' abs_st' α',
      match st with
      | ST _ t =>
        eq_bound_α t α α' /\
        match e' with
        | Val _ _ C' =>
          sound α' C' st' abs_C' abs_st'
        end
      end)
    (fun C st m C' st'
         (EVAL : MevalR C st m C' st') =>
    forall
         (BOUND : time_bound C st)
         abs_C abs_st α
         (SOUND : sound α C st abs_C abs_st),
    exists abs_C' abs_st' α',
      match st with
      | ST _ t =>
        eq_bound_α t α α' /\
        sound α' C' st' abs_C' abs_st'
      end)); intros; subst.
  - unfold sound in SOUND. destruct abs_st as [abs_mem abs_t].
    destruct SOUND as [? [? ?]].
    specialize (H1 (addr_x C x)) as HINT. rewrite <- ACCESS in HINT.
    destruct v as [v pf C'].
    exists (trans_ctx α C'). exists (Abstract.ST abs_mem abs_t). exists α.
    split; red; intros; eauto.
  - exists abs_C. exists abs_st. exists α. repeat split; eauto using Abstract.EevalR.
    destruct st; simpl; split; red; intros; eauto.
  - pose proof (time_bound_e C st e1 (Val (e_lam x e) (v_fn x e) C_lam) st_lam FN) as BOUND'.
    pose proof (time_bound_e C st_lam e2 arg (ST mem t) ARG) as BOUND''.
    pose proof (time_bound_e (C_lam [|dy_c_lam x t ([||])|])
                             (ST (t :: dy_level C_lam !-> arg; mem) (update_t t))
                             e v st_v BODY) as BOUND'''.
    specialize (BOUND' BOUND). simpl in BOUND'.
    destruct st. destruct st_lam. destruct st_v.
    apply time_increase_e in ARG as time_inc1.
    apply time_increase_e in FN as time_inc2.
    apply time_increase_e in BODY as time_inc3.
    assert (time_bound C (ST mem1 t1)) as B1. 
    { simpl. simpl in BOUND. destruct BOUND as [? [? ?]].
             simpl in BOUND'. destruct BOUND' as [? [? ?]].
      split. eapply relax_ctx_bound. eauto. eauto.
      split; eauto. }
    specialize (BOUND'' B1).
    destruct arg. destruct v.
    assert (time_bound (C_lam [|dy_c_lam x t ([||])|])
             (ST (t :: dy_level C_lam !-> Val v0 pf C0; mem) (update_t t))) as B2.
    { simpl. simpl in BOUND. destruct BOUND as [? [? ?]].
             simpl in BOUND'. destruct BOUND' as [? [? ?]].
             simpl in BOUND''. destruct BOUND'' as [? [? ?]].
      unfold update_t in *.
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. eauto. simpl. split; eauto. split.
      (* not bound, then None *)
      intros. unfold update_m. remember (eq_p p (t :: dy_level C_lam)) as b.
      destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
      rewrite Heqb in NBOUND. simpl in NBOUND.
      assert (t < S t /\ p_bound (dy_level C_lam) (S t)) as contra.
      split; eauto. apply time_bound_level. apply relax_ctx_bound with (t1 := t1). eauto. eauto.
      apply NBOUND in contra. inversion contra.
      apply H9. unfold not. intros contra.
      assert (p_bound p (S t)). apply relax_p_bound with (t1 := t); eauto.
      apply NBOUND in H11. inversion H11.
      (* bound, then access is bound *)
      intros. unfold update_m. remember (eq_p p (t :: dy_level C_lam)) as b.
      destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
      rewrite Heqb in BOUND. simpl in BOUND. destruct BOUND.
      apply relax_ctx_bound with (t1 := t); eauto.
      pose proof (p_bound_or_not p t). 
      remember (mem p) as access eqn:ACCESS. 
      destruct H11; destruct access; try destruct e0; eauto;
      try specialize (H10 p H11); try specialize (H9 p H11);
      try rewrite <- ACCESS in H10; try rewrite <- ACCESS in H9; 
      apply relax_ctx_bound with (t1 := t); eauto. inversion H9. }
    specialize (BOUND''' B2).
    specialize (H BOUND). specialize (H0 B1). specialize (H1 B2). 
    specialize (H abs_C abs_st α SOUND). 
    destruct H as [abs_C' [abs_st' [α' [EQ' SOUND']]]].
    assert (sound α' C (ST mem1 t1) abs_C abs_st').
    { destruct abs_st'. simpl. simpl in SOUND'. destruct SOUND' as [? [? ?]].
      repeat split; eauto. destruct abs_st. simpl in SOUND. destruct SOUND as [? [? ?]].
      rewrite <- H5. symmetry. eapply bound_trans_ctx_eq. simpl in BOUND. destruct BOUND.
      eauto. eauto. }
    specialize (H0 abs_C abs_st' α' H). clear H.
    destruct H0 as [abs_C'' [abs_st'' [α'' [EQ'' SOUND'']]]]. destruct abs_st'' as [mem'' t''].
    remember (fun (t' : nat) => if t' =? S t 
                        then Abstract.update_t (α'' t) else α'' t') as α'''.
    assert (sound α''' (C_lam [|dy_c_lam x t ([||])|])
            (ST (t :: dy_level C_lam !-> Val v0 pf C0; mem) (update_t t))
            (abs_C'[#| Abstract.dy_c_lam x (α'' t) ([#||#]) |#])
            (Abstract.ST ((α'' t) :: Abstract.dy_level abs_C' !#-> Abstract.Val v0 pf abs_C''; mem'') (Abstract.update_t (α'' t)))).
    { simpl. unfold update_t in *. repeat split.
      - rewrite Heqα'''. simpl. assert (t =? t = true). rewrite Nat.eqb_eq. eauto. rewrite H. eauto.
      - rewrite Heqα'''. simpl. rewrite plugin_trans_ctx; simpl.
        assert (t =? S t = false). rewrite Nat.eqb_neq. eauto. rewrite H.
        assert (trans_ctx α''' C_lam = abs_C'). rewrite Heqα'''.
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [? [? ?]]. rewrite <- H2.
        apply bound_trans_ctx_eq with (t := t1). simpl in BOUND'. destruct BOUND'. eauto.
        red. intros. assert (t' <> S t). nia. rewrite <- Nat.eqb_neq in H4. rewrite H4.
        symmetry. apply EQ''. eauto. rewrite <- Heqα'''. rewrite H0. eauto.
      - intros. simpl in SOUND''. destruct SOUND'' as [? [? ?]].
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [? [? ?]].
        unfold update_m. unfold Abstract.update_m.
        remember (eq_p p (t :: dy_level C_lam)) as b.
        destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
        assert (map α''' p =  α'' t :: Abstract.dy_level abs_C').
        rewrite Heqα'''. rewrite Heqb. simpl. assert (RR : t =? S t = false). 
        apply Nat.eqb_neq. eauto. rewrite RR. clear RR. rewrite <- H4.
        assert (Abstract.dy_level (trans_ctx α' C_lam) = map (fun t' : nat =>
                      if t' =? S t then Abstract.update_t (α'' t) else α'' t')
                      (dy_level C_lam)) as RR.
        apply level_trans_ctx_eq with (t := t1). red. intros.
        assert (t' =? S t = false). rewrite Nat.eqb_neq. nia. rewrite H6. apply EQ''. eauto.
        simpl in BOUND'. destruct BOUND'. eauto.
        rewrite RR. eauto. rewrite <- H6.
        (* A bug? in Coq : have to write explicitly the implicit parameters *)
        assert (Abstract.eq_p (@map time Abstract.time α''' p) (@map nat bool α''' p) = true).
        rewrite Abstract.eq_p_eq. eauto. rewrite H7. simpl. left.
        assert (abs_C'' = trans_ctx α''' C0).
        rewrite <- H0. eapply bound_trans_ctx_eq. simpl in BOUND''. destruct BOUND''. eauto.
        rewrite Heqα'''. red. intros. assert (t' =? S t = false). rewrite Nat.eqb_neq. nia.
        rewrite H8. eauto. rewrite H8. eauto.
        pose proof (p_bound_or_not p t) as CASES.
        simpl in BOUND''. destruct BOUND'' as [B1'' [B2'' B3'']].
        destruct CASES as [L | R]; 
        try (specialize (B2'' p R); rewrite B2''; eauto; fail).
        remember (mem p) as access eqn: ACCESS.
        destruct access; eauto; destruct e0; simpl.
        specialize (H2 p L). rewrite <- ACCESS in H2.
        assert (@map time Abstract.time α''' p = map α'' p) as RR. 
        { clear H2. clear BOUND0. clear Heqb. clear ACCESS.
          induction p; simpl; eauto. simpl in L; destruct L.
          rewrite IHp; eauto. rewrite Heqα'''. 
          assert (a =? S t = false). rewrite Nat.eqb_neq. nia.
          rewrite H7. eauto. } rewrite RR; clear RR.
        assert (trans_ctx α''' C2 = trans_ctx α'' C2) as RR.
        { apply bound_trans_ctx_eq with (t := t).
          specialize (B3'' p L). rewrite <- ACCESS in B3''. eauto.
          rewrite Heqα'''. red. intros. assert (t' =? S t = false).
          rewrite Nat.eqb_neq. nia. rewrite H6. eauto. } rewrite RR; clear RR.
        remember (α'' t :: Abstract.dy_level abs_C') as p'.
        remember (Abstract.eq_p (map α'' p) p') as b.
        destruct b. 
        simpl. right. symmetry in Heqb0. rewrite Abstract.eq_p_eq in Heqb0.
        rewrite <- Heqb0. apply H2. apply H2.
    }
    assert (eq_bound_α t α'' α''') as EQ'''.
    { red. intros. rewrite Heqα'''. assert (t' =? S t = false). rewrite Nat.eqb_neq. nia.
      rewrite H0. eauto. }
    specialize (H1 (abs_C' [#|Abstract.dy_c_lam x (α'' t) ([#||#])|#])
                (Abstract.ST
                  (α'' t :: Abstract.dy_level abs_C'
                      !#-> Abstract.Val v0 pf abs_C''; mem'')
                  (Abstract.update_t (α'' t))) α''' H).
    destruct H1 as [abs_C''' [abs_st''' [α'''' [EQ'''' SOUND''']]]].
    exists abs_C'''. exists abs_st'''. exists α''''. split; eauto.
    red. intros. 
    assert (α t' = α' t') as RR. apply EQ'. eauto. rewrite RR; clear RR.
    assert (α' t' = α'' t') as RR. apply EQ''. nia. rewrite RR; clear RR.
    assert (α'' t' = α''' t') as RR. apply EQ'''. nia. rewrite RR; clear RR.
    apply EQ''''. unfold update_t. nia.
  - 
  
