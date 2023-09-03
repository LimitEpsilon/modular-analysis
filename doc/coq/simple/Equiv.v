From Simple Require Import Concrete.

Ltac lebt x :=
  apply leb_trans with (t' := x);
  try assumption; try apply tick_lt; try apply leb_refl.

Generalizable Variables T TT.

Definition time_bound_C `{TotalOrder T} C t :=
  forall t', supp_C C t' -> t' < t.

Definition time_bound_m `{TotalOrder T} m t :=
  forall t', supp_m m t' -> t' < t.

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

Lemma not_le_lt `{TotalOrder T} :
  forall (p : T) t,
    (leb p t = false) <-> (t < p).
Proof.
  intros; unfold "<"; red; split; intros NLE;
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
    (p < t) \/ ~(p < t).
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
  intros; edestruct BOUND; simpl in *;
  try contradict; eauto 3;
  match goal with
  | H : _ \/ _ |- _ => destruct H; subst
  end;
  match goal with
  | H : supp_C ?C ?t |- _ =>
    match goal with
    | H : context [time_bound_C C _] |- _ => eapply H; eauto
    end
  | _ => idtac
  end; red; intros; try apply BOUND; eauto.
  Unshelve. split.
  - lebt t1.
  - rewrite eqb_neq in *. red; intros; subst.
    match goal with
    | H : _ |- _ => apply H; apply leb_sym; eauto
    end.
  - assumption.
Qed.

Lemma relax_p_bound `{time T} :
  forall p t1 t2 (BOUND : p < t1) (LE : leb t1 t2 = true),
    p < t2.
Proof.
  intros. destruct BOUND as [? EQ]. split.
  - lebt t1.
  - rewrite eqb_neq in *. red; intros.
    subst. apply EQ. apply leb_sym; eauto.
Qed.

Lemma relax_mem_bound `{time T} :
  forall m t1 t2 (BOUND : time_bound_m m t1) (LE : leb t1 t2 = true),
         time_bound_m m t2.
Proof.
  induction m; unfold time_bound_m;
  intros; edestruct BOUND; simpl in *;
  try contradict; eauto 3;
  repeat des_hyp.
  Unshelve.
  apply relax_p_bound with (t1 := t1); eauto.
  eauto.
Qed.

Lemma time_bound_addr `{time T} :
  forall C x t (BOUND : time_bound_C C t),
    match addr_x C x with
    | None => True
    | Some addr => addr < t
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

Lemma time_bound_read `{time T} :
  forall m t addr (BOUND : time_bound_m m t),
    match read m addr with
    | None => True
    | Some v => time_bound_v v t
    end.
Proof.
  induction m; intros; simpl; eauto;
  repeat des_goal; repeat des_hyp; eauto;
  try rewrite eqb_eq in *; clarify;
  match goal with
  | _ => 
    unfold time_bound_m in *;
    unfold time_bound_v;
    des_goal; red; intros; simpl in *;
    apply BOUND; eauto; fail
  | RR : read ?m ?addr = Some ?v |- _ => 
    specialize (IHm t addr);
    rewrite RR in IHm;
    apply IHm; red; intros; apply BOUND; simpl; eauto
  end.
Qed.

Lemma time_bound_ctx_M `{time T} :
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
  let t' := tick C m t x v in
  time_bound_m (t !-> v; m) t'.
Proof.
  intros. subst t'.
  unfold time_bound_v in *.
  unfold time_bound_m in *. des_hyp.
  unfold time_bound_C in *.
  intros; simpl in *;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H; subst
  | |- _ < _ => split; try (lebt t); try (apply leb_t_neq_tick)
  | |- leb ?t ?t = true => apply leb_refl
  | _ : supp_C ?C ?t |- _ =>
    match goal with
    | H : forall _, supp_C C _ -> _ |- _ =>
      apply H; eauto; fail
    end
  | _ : supp_m ?m ?t |- _ =>
    match goal with
    | H : forall _, supp_m m _ -> _ |- _ =>
      apply H; eauto; fail
    end
  end.
Qed.

Lemma trans_m_update `{TotalOrder T} {TT} (α : T -> TT) :
  forall m t v (BOUND : time_bound_m m t),
    trans_m α (t !-> v; m) =
    (α t !-> trans_v α v; trans_m α m).
Proof.
  intros.
  assert (
    forall l l' 
      (IN : forall t', (In t' l' -> t = t' \/ In t' l) /\ (In t' l -> In t' l')),
    trans_m_aux α m l = trans_m_aux α m l') as RR.
  {
    intros. ginduction m; intros; simpl; eauto.
    repeat des_goal; try rewrite eqb_eq in *; clarify;
    try rewrite Inb_eq in *; try rewrite Inb_neq in *;
    match goal with
    | _ : In ?t _ |- _ => (* contradictory *)
      specialize (IN t); destruct IN as [L R];
      try match goal with
      | H : _ |- _ => apply R in H
      end;
      try match goal with
      | H : _ |- _ => apply L in H
      end;
      try match goal with
      | H : _ \/ _ |- _ => destruct H
      end; clarify;
      match goal with
      | _ => contradict
      | H : time_bound_m ((?t, _) :: _) ?t |- _ =>
        let contra := fresh "contra" in
        assert (t < t) as contra;
        first [
          unfold time_bound_m in *; apply H; intros; simpl in *; eauto |
          inversion contra; rewrite eqb_neq in *; contradict]
      end
    | _ => idtac
    end;
    match goal with
    | |- context [trans_m_aux α m ?l] =>
    match goal with
    | |- context [trans_m_aux α m ?l'] =>
    lazymatch l' with
    | l => fail
    | _ => let RR := fresh "RR" in
      assert (trans_m_aux α m l = trans_m_aux α m l') as RR;
      match goal with
      | _ => rewrite RR; reflexivity
      | _ => (* solve RR *)
        eapply IHm with (t := t); eauto; unfold time_bound_m in *;
        intros; try apply BOUND; simpl in *; eauto; split; intros;
        repeat match goal with
        | H : _ \/ _ |- _ => destruct H; eauto
        end; specialize (IN t'); destruct IN as [L R];
        try match goal with
        | H : _ |- _ => apply R in H; eauto
        end;
        try match goal with
        | H : _ |- _ => apply L in H; destruct H
        end; eauto
      end
    end end end.
  }
  unfold trans_m, trans_v, update_m.
  simpl. des_goal.
  symmetry. erewrite RR; eauto.
  intros; simpl; split; intros; eauto.
Qed.

Lemma time_bound_e `{time T} :
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
  | RR : read ?m ?addr = Some ?v |- _ =>
    match goal with
    | H : time_bound_m m ?t |- _ =>
      pose proof (time_bound_read m t addr H);
      rewrite RR in *; assumption
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
    | |- ?t < ?t' =>
      split; try apply leb_t_neq_tick;
      try match t' with
      | tick _ _ ?t' _ _ => lebt t'
      end
    | _ : supp_C ?C ?t |- leb ?t _ = true =>
      match goal with
      | H : time_bound_C C ?t' |- _ =>
        lebt t'; apply H; eauto
      end
    | IN : supp_C ?C ?t |- eqb ?t _ = false =>
      match goal with
      | H : time_bound_C C ?t' |- _ =>
        specialize (H t IN); destruct H as [? contra];
        rewrite eqb_neq in *; red; intros; subst;
        apply contra; try reflexivity;
        apply leb_sym; assumption
      end
    end
  | |- time_bound_m ?m ?t => try assumption;
    apply time_bound_tick; simpl; assumption
  end.
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
