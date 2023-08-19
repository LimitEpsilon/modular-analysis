From Simple Require Export Abstract.
From Simple Require Export Concrete.

Ltac lebt x :=
  apply leb_trans with (t' := x); try assumption; try apply tick_lt.

Module Abs := Abstract.
Module Conc := Concrete.

Generalizable Variables CT.
Generalizable Variables AT.

Definition sound_cf {CT AT} (α : CT -> AT) C st abs_C abs_st :=
  match st, abs_st with
  | ST mem t, Abs.ST abs_mem abs_t =>
    trans_ctx α C = abs_C /\ trans_mem α mem abs_mem /\ α t = abs_t
  end.

Definition sound_res {CT AT} (α : CT -> AT) V st abs_V abs_st :=
  match st, abs_st with
  | ST mem t, Abs.ST abs_mem abs_t =>
    trans_V α V = abs_V /\ trans_mem α mem abs_mem /\ α t = abs_t
  end.

Definition preserve_tick `{Conc.time CT} `{Abs.time AT} (α : CT -> AT) :=
  forall x C st abs_C abs_st v abs_v
    (SOUND : sound_cf α C st abs_C abs_st)
    (SOUNDv : trans_v α v = abs_v),
  α (tick C st x v) = Abs.tick abs_C abs_st x abs_v.

Fixpoint dy_ctx_bound `{Conc.time CT} C t :=
  match C with
  | [||] => True
  | dy_binde _ t' C' => t' < t /\ dy_ctx_bound C' t
  | dy_bindm _ CM C' => dy_ctx_bound CM t /\ dy_ctx_bound C' t
  end.

Definition time_bound `{Conc.time CT} C st :=
  match st with
  | ST mem t =>
    dy_ctx_bound C t /\
    (forall p (NBOUND : ~(p < t)),
      mem p = None) /\
    (forall p (BOUND : p < t),
      match mem p with
      | Some (Closure _ _ C') => dy_ctx_bound C' t
      | _ => True
      end)
  end.

Lemma p_bound_or_not :
  forall `{Conc.time CT} (p : CT) t,
    (p < t) \/ ~(p < t).
Proof.
  intros. unfold "<". unfold not.
  remember (leb p t) as le. remember (eqb p t) as eq.
  destruct le; destruct eq.
  - right. intros contra. destruct contra as [? contra]. inversion contra.
  - left; eauto.
  - symmetry in Heqeq. rewrite eqb_eq in Heqeq. subst.
    rewrite leb_refl in Heqle. inversion Heqle.
  - right. intros contra. destruct contra as [contra ?]. inversion contra.
Qed.

Lemma time_increase_e :
  forall `{Conc.time CT} C st e e' st'
         (EVAL : EvalR C st e e' st'),
    match st with
    | ST _ t =>
      match st' with
      | ST _ t' => leb t t' = true
      end
    end.
Proof.
  intros. 
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  induction EVAL;
  intros; 
  destruct st; try destruct st'; try destruct st''; try destruct st_v; 
  try destruct st_m; try destruct st_lam; simpl; try apply leb_refl.
  - inversion STATE; subst. apply leb_refl.
  - lebt (tick C (ST mem t) x arg). lebt t2. lebt t.
  - lebt t1.
  - lebt (tick C (ST mem t) x v). lebt t.
  - lebt t0.
Qed.

Lemma relax_ctx_bound :
  forall `{Conc.time CT}
         C t1 t2 (BOUND : dy_ctx_bound C t1) (LE : leb t1 t2 = true),
         dy_ctx_bound C t2.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  revert C t1 t2 BOUND LE.
  induction C; intros; destruct BOUND; simpl in *; 
  repeat split;
  try eapply IHC; try eapply IHC1; try eapply IHC2; eauto;
  try destruct H; try lebt t1; eauto.
  rewrite eqb_neq in *. red. intros; subst. apply H1. apply leb_sym; eauto.
Qed.

Lemma relax_p_bound :
  forall `{Conc.time CT}
    p t1 t2 (BOUND : p < t1) (LE : leb t1 t2 = true),
  p < t2.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  destruct BOUND. split.
  lebt t1.
  rewrite eqb_neq. red. intros; subst.
  assert (t1 = t2). apply leb_sym; eauto. subst.
  assert (true = eqb t2 t2). symmetry. apply eqb_eq; eauto.
  rewrite <- H1 in H0. inversion H0.
Qed.

Lemma time_bound_addr :
  forall `{Conc.time CT} C x t,
    dy_ctx_bound C t -> 
    match addr_x C x with
    | None => True
    | Some addr => addr < t
    end.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  rename H2 into BOUND.
  revert C x t BOUND.
  induction C; intros; simpl in *; try destruct BOUND; eauto.
  - specialize (IHC x0 t H0).
    destruct (addr_x C x0); eauto. 
    destruct (eq_eid x0 x); simpl; eauto.
  - apply IHC2; eauto.
Qed.

Lemma time_bound_ctx_M :
  forall `{Conc.time CT} C M t CM,
    ctx_M C M = Some CM ->
    dy_ctx_bound C t -> 
    dy_ctx_bound CM t.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  rename H2 into ACCESS. rename H3 into BOUND.
  revert C M t CM ACCESS BOUND.
  induction C; intros; simpl in *.
  - inversion ACCESS.
  - eapply IHC; eauto. destruct BOUND; eauto.
  - remember (ctx_M C2 M0) as oCM.
    destruct oCM.
    + inversion ACCESS; subst. eapply IHC2; eauto.
      destruct BOUND; eauto.
    + destruct (eq_mid M0 M); inversion ACCESS; subst.
      destruct BOUND; eauto.
Qed.

Lemma plugin_ctx_bound :
  forall `{Conc.time CT} Cout Cin t,
    dy_ctx_bound (Cout[|Cin|]) t <-> dy_ctx_bound Cout t /\ dy_ctx_bound Cin t.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  revert Cout Cin t. induction Cout; repeat split; intros; simpl in *; 
  try destruct H as [[LE NEQ] BD]; 
  try destruct H as [BD1 BD2];
  try (try apply IHCout with (Cin := Cin);
       try apply IHCout1 with (Cin := Cin1);
       try apply IHCout2 with (Cin := Cin2); eauto; fail);
  try (destruct LE; eauto).
  rewrite IHCout2 in BD2. destruct BD2; eauto.
  rewrite IHCout2 in BD2. destruct BD2; eauto.
  rewrite IHCout2; eauto.
Qed.

Lemma leb_t_neq_tick :
  forall `{Conc.time CT} C mem x v (t' : CT) (t : CT) (LE : leb t' t = true),
  eqb t' (tick C (ST mem t) x v) = false.
Proof.
  intros. refl_bool. intros contra.
  rewrite eqb_eq in *.
  assert (t <> tick C (ST mem t) x v) as NEQ.
  { rewrite <- eqb_neq. apply tick_lt. }
  apply NEQ. apply leb_sym. 
  apply tick_lt.
  subst. eauto.
Qed.

Lemma time_bound_tick :
  forall `{Conc.time CT} C' x' x e C mem t
         (B : time_bound C (ST mem t)),
  time_bound C (ST (t !-> Closure x e C; mem) (tick C' (ST mem t) x' (Closure x e C))).
Proof.
  intros. destruct B as [CTX [NB B]].
  split. apply relax_ctx_bound with (t1 := t).
  apply CTX. apply tick_lt.
  split; intros;
  unfold update_m; destruct (eqb p t) eqn:EQ;
  try rewrite eqb_eq in EQ.
  - subst. assert False as contra. apply NBOUND.
    apply tick_lt. inversion contra.
  - apply NB. red. intros contra.
    apply NBOUND.
    apply relax_p_bound with (t1 := t); try assumption. apply tick_lt.
  - subst. apply relax_ctx_bound with (t1 := t); try assumption. apply tick_lt.
  - specialize (B p). 
    destruct (mem p) eqn:ACCESS; eauto.
    destruct e0.
    apply relax_ctx_bound with (t1 := t).
    apply B.
    pose proof (p_bound_or_not p t) as CASES.
    destruct CASES as [? | contra]; eauto.
    specialize (NB p contra). rewrite NB in ACCESS. inversion ACCESS. apply tick_lt.
Qed.

Lemma time_bound_e :
  forall `{Conc.time CT} C st e e' st'
         (EVAL : EvalR C st e e' st')
         (BOUND : time_bound C st),
    match e' with
    | EVal (Closure _ _ C') => time_bound C' st'
    | MVal C' => time_bound C' st'
    end.
Proof.
  intros. 
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  induction EVAL; intros; simpl; eauto.
  - destruct v. unfold time_bound in *.
    destruct st. destruct BOUND as [? [? RR]].
    specialize (RR addr) as RR'. inversion STATE; subst.
    pose proof (time_bound_addr C x t0 H).
    rewrite <- ADDR in H1.
    apply RR' in H1. 
    rewrite <- ACCESS in H1. repeat split; eauto.
  - specialize (IHEVAL1 BOUND). 
    destruct v. destruct arg. 
    destruct st. destruct st_lam. destruct st_v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    apply time_increase_e in EVAL3 as time_inc3.
    assert (time_bound C (ST mem1 t1)) as HINT.
    {
      simpl in IHEVAL1. destruct IHEVAL1 as [? [? ?]]. 
      simpl; repeat split; eauto. 
      eapply relax_ctx_bound. 
      simpl in BOUND. destruct BOUND. exact d. eauto. 
    }
    specialize (IHEVAL2 HINT).
    apply IHEVAL3; simpl. split.
    rewrite plugin_ctx_bound. split.
    simpl in IHEVAL1. destruct IHEVAL1 as [? [? ?]].
    eapply relax_ctx_bound. eauto. lebt t.
    simpl. split; eauto using tick_lt.
    apply time_bound_tick. eauto.
  - apply IHEVAL2. apply IHEVAL1. eauto.
  - destruct st. simpl in *. destruct BOUND as [? [? ?]].
    repeat split; eauto. eapply time_bound_ctx_M.
    symmetry. exact ACCESS. eauto.
  - specialize (IHEVAL1 BOUND).
    destruct v. 
    destruct st. destruct st_m.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in IHEVAL1. destruct IHEVAL1 as [HH1 [HH2 HH3]].
    apply IHEVAL2. simpl; split.
    rewrite plugin_ctx_bound; split.
    apply relax_ctx_bound with (t1 := t0); eauto.
    lebt t.
    simpl; split; eauto. apply tick_lt.
    apply time_bound_tick. repeat split; eauto.
  - specialize (IHEVAL1 BOUND).
    destruct st. destruct st'. destruct st''.
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in IHEVAL1. destruct IHEVAL1 as [HH1 [HH2 HH3]].
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    apply IHEVAL2. simpl. repeat split; eauto.
    rewrite plugin_ctx_bound. split.
    apply relax_ctx_bound with (t1 := t); eauto.
    simpl; split; eauto.
Qed.

Lemma trans_mem_update `{Conc.time CT} `{Abs.time AT} (α : CT -> AT) :
  forall C t arg arg' mem mem'
    (BOUND : time_bound C (ST mem t))
    (SOUNDm : trans_mem α mem mem')
    (SOUNDv : trans_v α arg = arg'),
  trans_mem α (t !-> arg; mem) (α t !#-> arg'; mem').
Proof.
  intros.
  red. intros. unfold update_m. unfold Abs.update_m.
  destruct (eqb abs_t (α t)) eqn:EQ.
  - rewrite eqb_eq in EQ.
    split; intros IN.
    destruct IN as [EQv | IN].
    exists t. exists arg.
    split. rewrite <- EQv; eauto.
    split. eauto. rewrite t_refl. eauto.
    red in SOUNDm. rewrite SOUNDm in IN.
    destruct IN as [p [v HINT]].
    exists p. exists v. rewrite EQ.
    repeat split; try apply HINT.
    pose proof (p_bound_or_not p t) as CASES.
    destruct BOUND as [B1 [B2 B3]].
    destruct CASES as [L | R]; 
    try (specialize (B2 p R); rewrite B2 in HINT; 
        destruct HINT as [? [? contra]]; inversion contra).
    replace (eqb p t) with false; try (symmetry; apply L). apply HINT.
    destruct IN as [p [v [EQv [EQt ACCESS]]]].
    destruct (eqb p t) eqn:EQ'.
    rewrite eqb_eq in EQ'. subst.
    left. inversion ACCESS; eauto.
    right. red in SOUNDm. rewrite SOUNDm. exists p. exists v. repeat split; try assumption.
    rewrite <- EQ. eauto.
  - split; intros IN.
    red in SOUNDm. rewrite SOUNDm in IN.
    destruct IN as [p [v HINT]].
    exists p. exists v.
    repeat split; try apply HINT.
    pose proof (p_bound_or_not p t) as CASES.
    destruct BOUND as [B1 [B2 B3]].
    destruct CASES as [L | R]; 
    try (specialize (B2 p R); rewrite B2 in HINT; 
        destruct HINT as [? [? contra]]; inversion contra).
    replace (eqb p t) with false; try (symmetry; apply L). apply HINT.
    destruct IN as [p [v [EQv [EQt ACCESS]]]].
    red in SOUNDm. rewrite SOUNDm.
    destruct (eqb p t) eqn:EQ'.
    rewrite eqb_eq in EQ'. subst.
    rewrite t_refl in EQ. inversion EQ.
    exists p. exists v. eauto.
Qed.

(* Set Printing Implicit. *)

Lemma sound_eval `{Conc.time CT} `{Abs.time AT} (α : CT -> AT) (PRES : preserve_tick α) :
  forall C st e V stV (EVAL : EvalR C st e V stV)
    abs_C abs_st
    (SOUND : sound_cf α C st abs_C abs_st)
    (BOUND : time_bound C st),
  exists abs_V abs_stV,
    sound_res α V stV abs_V abs_stV /\
    Abs.EvalR abs_C abs_st e abs_V abs_stV.
Proof.
  intros C st e V stV EVAL.
  induction EVAL; intros; simpl in *.
  - pose proof (trans_ctx_addr α C x) as RR.
    rewrite <- ADDR in RR. rewrite <- STATE in SOUND.
    exists (EVal (trans_v α v)).
    exists abs_st. destruct abs_st.
    repeat split; try apply SOUND.
    eapply Abs.Eval_var_e with (addr := α addr); eauto.
    destruct SOUND as [RRC [? ?]]. rewrite <- RRC. symmetry. assumption.
    destruct SOUND as [? [MEM ?]].
    red in MEM. specialize (MEM (α addr) (trans_v α v)).
    rewrite MEM. exists addr. exists v. repeat split; eauto.
  - exists (EVal (Closure x e (trans_ctx α C))).
    exists abs_st.
    destruct st as [mem t]. destruct abs_st as [abs_mem abs_t].
    repeat split; try apply SOUND.
    destruct SOUND as [RR [? ?]]. rewrite RR.
    apply Abs.Eval_lam.
  - pose proof (time_bound_e C st e1 (EVal (Closure x e C_lam)) st_lam EVAL1) as BOUND1.
    pose proof (time_bound_e C st_lam e2 (EVal arg) (ST mem t) EVAL2) as BOUND2.
    pose proof (time_bound_e (C_lam [|dy_binde x t ([||])|])
                             (ST (t !-> arg; mem) (tick C (ST mem t) x arg))
                             e (EVal v) st_v EVAL3) as BOUND3.
    specialize (BOUND1 BOUND). simpl in BOUND1.
    destruct st as [memi ti]. destruct st_lam as [memf tf]. destruct st_v as [memv tv].
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    apply time_increase_e in EVAL3 as time_inc3.
    assert (time_bound C (ST memf tf)) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [? [? ?]].
             simpl in BOUND1. destruct BOUND1 as [? [? ?]].
      split. eapply relax_ctx_bound. eauto. eauto.
      split; eauto. }
    specialize (BOUND2 B1).
    destruct arg. destruct v.
    assert (time_bound (C_lam [|dy_binde x t ([||])|])
             (ST (t !-> Closure x0 e0 C0; mem) (tick C (ST mem t) x (Closure x0 e0 C0)))) as B2.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND1. destruct BOUND1 as [BB1' [BB2' BB3']].
             simpl in BOUND2. destruct BOUND2 as [BB1'' [BB2'' BB3'']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. lebt t.
      simpl. split; eauto. split. apply tick_lt. apply tick_lt.
      apply time_bound_tick. repeat split; eauto. }
    specialize (BOUND3 B2).
    specialize (IHEVAL1 abs_C abs_st SOUND BOUND).
    destruct IHEVAL1 as [abs_V' [[memf' tf'] [SOUND1 EVAL1']]].
    assert (sound_cf α C (ST memf tf) abs_C (Abs.ST memf' tf')) as HINT.
    { destruct SOUND1 as [? [? ?]].
      split. destruct abs_st; apply SOUND.
      split; assumption. }
    specialize (IHEVAL2 abs_C (Abs.ST memf' tf') HINT B1). clear HINT.
    destruct IHEVAL2 as [abs_V'' [[mem' t'] [SOUND2 EVAL2']]].
    destruct abs_V' as [[x' e' C_lam'] | ?]; 
    inversion SOUND1 as [SOUNDV1 [SOUNDm1 SOUNDt1]];
    try (inversion SOUNDV1; fail).
    destruct SOUND2 as [SOUNDV2 [SOUNDm2 SOUNDt2]].
    destruct abs_V'' as [arg' | ?]; try (inversion SOUNDV2; fail).
    assert (sound_cf α (C_lam [|dy_binde x t ([||])|])
            (ST (t !-> Closure x0 e0 C0; mem) (tick C (ST mem t) x (Closure x0 e0 C0)))
            (C_lam'[| dy_binde x (α t) ([||]) |])
            (Abs.ST ((α t) !#-> arg'; mem') 
                    (Abs.tick abs_C (Abs.ST mem' t') x arg'))) as HINT.
    { split. rewrite plugin_trans_ctx; inversion SOUNDV1; eauto.
      split; try apply PRES.
      eapply trans_mem_update; eauto. inversion SOUNDV2; eauto.
      split. destruct abs_st; apply SOUND.
      split; eauto.
      inversion SOUNDV2; eauto. }
    specialize (IHEVAL3 (C_lam' [|dy_binde x (α t) ([||])|])
                (Abs.ST ((α t) !#-> arg'; mem') 
                    (Abs.tick abs_C (Abs.ST mem' t') x arg')) HINT B2). clear HINT.
    destruct IHEVAL3 as [abs_V [abs_stV [SOUND3 EVAL3']]].
    exists abs_V. exists abs_stV.
    split; eauto. destruct abs_stV as [memv' tv']. 
    destruct SOUND3 as [SOUNDV3 [SOUNDm3 SOUNDt3]].
    destruct abs_V; try (inversion SOUNDV3; fail).
    eapply Abs.Eval_app; eauto.
    rewrite <- SOUNDt2. inversion SOUNDV1; subst; eauto.
  - pose proof (time_bound_e C st m (MVal C_m) st_m EVAL1) as BOUND1.
    pose proof (time_bound_e C_m st_m e v st_v EVAL2) as BOUND2.
    specialize (BOUND1 BOUND). simpl in BOUND1. 
    specialize (BOUND2 BOUND1). simpl in BOUND2.
    destruct st as [memi ti]. destruct st_m as [memm tm]. destruct st_v as [memv tv].
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    specialize (IHEVAL1 abs_C abs_st SOUND BOUND).
    destruct IHEVAL1 as [[? | C_m'] [[memm' tm'] [SOUND1 EVAL1']]];
    destruct SOUND1 as [SOUNDV1 [SOUNDm1 SOUNDt1]];
    try (inversion SOUNDV1; fail).
    assert (sound_cf α C_m (ST memm tm) C_m' (Abs.ST memm' tm')) as HINT.
    { split. inversion SOUNDV1; eauto. 
      split; assumption. }
    specialize (IHEVAL2 C_m' (Abs.ST memm' tm') HINT BOUND1). clear HINT.
    destruct IHEVAL2 as [abs_V [[memv' tv'] [SOUND2 EVAL2']]].
    exists abs_V. exists (Abs.ST memv' tv').
    split. assumption.
    eapply Abs.Eval_link; eauto.
  - exists (MVal abs_C). exists abs_st. destruct st; destruct abs_st.
    split; eauto. destruct SOUND as [RR [? ?]].
    split. simpl. rewrite RR. eauto. split; assumption.
  - exists (MVal (trans_ctx α C_M)). exists abs_st. destruct st; destruct abs_st.
    destruct SOUND as [? [? ?]].
    split. split; eauto.
    eapply Abstract.Eval_var_m. erewrite trans_ctx_ctx_M; eauto.
  - pose proof (time_bound_e C st e (EVal v) (ST mem t) EVAL1) as BOUND1.
    pose proof (time_bound_e (C [|dy_binde x t ([||])|]) 
                             (ST (t !-> v; mem) (tick C (ST mem t) x v)) m
                             (MVal C_m) st_m EVAL2) as BOUND2.
    specialize (BOUND1 BOUND). simpl in BOUND1.
    destruct st as [memi ti]. destruct st_m as [memm tm]. destruct v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (time_bound (C [|dy_binde x t ([||])|])
            (ST (t !-> (Closure x0 e0 C0); mem) (tick C (ST mem t) x (Closure x0 e0 C0)))) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND1. destruct BOUND1 as [BB1' [BB2' BB3']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. lebt t.
      simpl. split; eauto. apply tick_lt.
      apply time_bound_tick. repeat split; eauto. }
    specialize (BOUND2 B1).
    specialize (IHEVAL1 abs_C abs_st SOUND BOUND).
    destruct IHEVAL1 as [[v' | ?] [[mem' t'] [[SOUNDV1 [SOUNDm1 SOUNDt1]] EVAL1']]];
    try (inversion SOUNDV1; fail).
    assert (sound_cf α (C [|dy_binde x t ([||])|])
            (ST (t !-> Closure x0 e0 C0; mem) (tick C (ST mem t) x (Closure x0 e0 C0)))
            (abs_C [| dy_binde x (α t) ([||]) |])
            (Abs.ST ((α t) !#-> v'; mem')
                    (Abs.tick abs_C (Abs.ST mem' t') x v'))) as HINT.
    { split. rewrite plugin_trans_ctx; destruct abs_st; destruct SOUND as [RR [? ?]]; rewrite RR; eauto.
      split; try apply PRES.
      eapply trans_mem_update; eauto. inversion SOUNDV1; eauto.
      split. destruct abs_st; apply SOUND.
      split; eauto.
      inversion SOUNDV1; eauto. }
    specialize (IHEVAL2 (abs_C [|dy_binde x (α t) ([||])|])
                (Abs.ST
                  (α t !#-> v'; mem')
                  (Abs.tick abs_C (Abs.ST mem' t') x v')) HINT B1). clear HINT.
    destruct IHEVAL2 as [abs_V [abs_stV [SOUND2 EVAL2']]].
    exists abs_V. exists abs_stV. split; eauto.
    destruct abs_V as [? | ?]; 
    destruct abs_stV; destruct SOUND2 as [contra [? ?]]; try (inversion contra; fail).
    eapply Abs.Eval_lete; eauto. rewrite <- SOUNDt1 in *. eauto.
  - pose proof (time_bound_e C st m' (MVal C') st' EVAL1) as BOUND1.
    pose proof (time_bound_e (C [|dy_bindm M C' ([||])|]) st' m''
                             (MVal C'') st'' EVAL2) as BOUND2.
    specialize (BOUND1 BOUND). simpl in BOUND1.
    destruct st as [memi ti]. destruct st' as [memM tM]. destruct st'' as [memV tV].
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (time_bound (C [|dy_bindm M C' ([||])|]) (ST memM tM)) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND1. destruct BOUND1 as [BB1' [BB2' BB3']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. eauto. simpl. split; eauto. split; eauto. }
    specialize (BOUND2 B1).
    specialize (IHEVAL1 abs_C abs_st SOUND BOUND).
    destruct IHEVAL1 as [abs_C' [[memM' tM'] [[SOUNDV1 [SOUNDm1 SOUNDt1]] EVAL1']]].
    destruct abs_C' as [? | abs_C']; try (inversion SOUNDV1; fail).
    assert (sound_cf α (C [|dy_bindm M C' ([||])|]) (ST memM tM)
            (abs_C [|dy_bindm M abs_C' ([||]) |]) (Abs.ST memM' tM')) as HINT.
    { split. rewrite plugin_trans_ctx. simpl.
      destruct abs_st; destruct SOUND as [RR [? ?]].
      rewrite RR; inversion SOUNDV1; subst; eauto.
      split; eauto. }
    specialize (IHEVAL2 (abs_C [|dy_bindm M abs_C' ([||])|])
                        (Abs.ST memM' tM') HINT B1).
    destruct IHEVAL2 as [abs_V [[memV' tV'] [[SOUNDV2 [SOUNDm2 SOUNDt2]] EVAL2']]].
    exists abs_V. exists (Abs.ST memV' tV').
    split. split. eauto. split; eauto.
    destruct abs_V as [? | abs_V]; try (inversion SOUNDV2; fail).
    eauto.
Qed.

Lemma sound_reach `{Conc.time CT} `{Abs.time AT} (α : CT -> AT) (PRES : preserve_tick α) :
  forall C st e C' st' e'
         (REACH : one_reach C st e C' st' e')
         (BOUND : time_bound C st)
         abs_C abs_st
         (SOUND : sound_cf α C st abs_C abs_st),
    exists abs_C' abs_st',
    sound_cf α C' st' abs_C' abs_st' /\
    Abs.one_reach abs_C abs_st e abs_C' abs_st' e'.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  rename H2 into EAT. rename H3 into T2.
  destruct st as [memi ti].
  destruct REACH.
  - exists abs_C. exists abs_st.
    repeat split; eauto. apply Abs.one_appl.
  - eapply sound_eval in FN; eauto.
    destruct FN as [abs_V [abs_stV [SOUND' EVAL]]].
    exists abs_C. exists abs_stV.
    destruct st_lam as [memf tf].
    destruct abs_stV as [memf' tf']. destruct SOUND' as [SOUNDV1 [SOUNDm1 SOUNDt1]].
    split. split. destruct abs_st; apply SOUND. split; eauto.
    destruct abs_V as [[x' e' C_lam'] | ?]; try (inversion SOUNDV1; fail).
    eapply Abs.one_appr; eauto.
  - eapply sound_eval in FN as SOUND1; eauto.
    destruct SOUND1 as [abs_V [[memf' tf'] [SOUND1 EVAL1]]].
    apply time_bound_e in FN as BOUND1; eauto.
    destruct st_lam as [memf tf].
    destruct SOUND1 as [SOUNDV1 [SOUNDm1 SOUNDt1]].
    destruct abs_V as [[x' e' C_lam'] | ?]; try (inversion SOUNDV1; fail).
    apply time_increase_e in FN as INC1; eauto.
    assert (time_bound C (ST memf tf)) as B1.
    { split. eapply relax_ctx_bound; eauto. apply BOUND.
      apply BOUND1. }
    assert (sound_cf α C (ST memf tf) abs_C (Abs.ST memf' tf')) as HINT.
    { split. destruct abs_st; apply SOUND.
      split; eauto. }
    eapply sound_eval in ARG as SOUND2; eauto. clear HINT.
    destruct SOUND2 as [arg' [[mem' t'] [SOUND2 EVAL2]]].
    apply time_bound_e in ARG as BOUND2; eauto.
    apply time_increase_e in ARG as INC2; eauto.
    destruct SOUND2 as [SOUNDV2 [SOUNDm2 SOUNDt2]].
    destruct arg' as [arg' | ?]; try (inversion SOUNDV2; fail).
    exists (C_lam' [| dy_binde x (α t) ([||]) |]).
    exists (Abs.ST (α t !#-> arg'; mem') (Abs.tick abs_C (Abs.ST mem' t') x arg')).
    split. split.
    rewrite plugin_trans_ctx; inversion SOUNDV1; eauto.
    split; try apply PRES.
    destruct arg. eapply trans_mem_update; eauto. inversion SOUNDV2; eauto.
    split. destruct abs_st; apply SOUND.
    split; eauto.
    inversion SOUNDV2; eauto.
    rewrite <- SOUNDt2 in *.
    eapply Abs.one_appbody; eauto.
    inversion SOUNDV1; subst; eauto.
  - exists abs_C. exists abs_st.
    split; eauto. eapply Abs.one_linkl; eauto.
  - eapply sound_eval in MOD; eauto.
    destruct MOD as [abs_V [abs_stV [SOUND1 EVAL1]]].
    destruct st_m as [memm tm]. destruct abs_stV as [memm' tm'].
    destruct SOUND1 as [SOUNDV1 [SOUNDm1 SOUNDt1]].
    destruct abs_V as [? | C_m']; try (inversion SOUNDV1; fail).
    exists C_m'. exists (Abs.ST memm' tm').
    split. split. inversion SOUNDV1; eauto.
    split; eauto.
    eapply Abs.one_linkr; eauto.
  - exists abs_C. exists abs_st. split; eauto.
    eapply Abs.one_letel.
  - eapply sound_eval in EVALx as SOUND1; eauto.
    destruct SOUND1 as [abs_V [[mem' t'] [SOUND1 EVAL1]]].
    destruct SOUND1 as [SOUNDV1 [SOUNDm1 SOUNDt1]].
    destruct abs_V as [v' | ?]; try (inversion SOUNDV1; fail).
    apply time_bound_e in EVALx; eauto.
    exists (abs_C [| dy_binde x (α t) ([||]) |]).
    exists (Abs.ST (α t !#-> v'; mem') (Abs.tick abs_C (Abs.ST mem' t') x v')).
    split. split.
    rewrite plugin_trans_ctx. destruct abs_st; destruct SOUND as [RR [? ?]]; rewrite RR. eauto.
    split; try apply PRES.
    destruct v; eapply trans_mem_update; eauto. inversion SOUNDV1; eauto.
    split. destruct abs_st; apply SOUND.
    split; eauto.
    inversion SOUNDV1; eauto.
    rewrite <- SOUNDt1 in *.
    eapply Abs.one_leter; eauto.
  - exists abs_C. exists abs_st.
    split; eauto. apply Abs.one_letml.
  - eapply sound_eval in EVALM as SOUND1; eauto.
    destruct st_M as [memM tM].
    destruct SOUND1 as [C_M' [[memM' tM'] [[SOUNDV1 [SOUNDm1 SOUNDt1]] EVAL1]]].
    destruct C_M' as [? | C_M']; try (inversion SOUNDV1; fail).
    eapply time_increase_e in EVALM as INC1; eauto.
    eapply time_bound_e in EVALM as BOUND1; eauto.
    exists (abs_C [|dy_bindm M C_M' ([||])|]).
    exists (Abs.ST memM' tM').
    split. split. rewrite plugin_trans_ctx.
    destruct abs_st; destruct SOUND as [RR [? ?]]; rewrite RR; inversion SOUNDV1; eauto.
    split; eauto.
    eapply Abs.one_letmr. eauto.
Qed.
