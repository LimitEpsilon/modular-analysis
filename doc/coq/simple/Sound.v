From Simple Require Export Abstract.
From Simple Require Export Concrete.

Ltac lebt x :=
  apply leb_trans with (t' := x); try assumption; try apply tick_lt.

Module Abs := Abstract.
Module Conc := Concrete.

Generalizable Variables CT.
Generalizable Variables AT.

Definition concret {CT AT} := AT -> CT -> bool.

Definition preserve_tick `{Conc.time CT} `{Abs.time AT} (γ : concret) :=
  forall (t : CT) (abs_t : AT) C abs_mem x abs_v
    (SOUND : γ abs_t t = true),
    γ (Abs.tick C (Abs.ST abs_mem abs_t) x abs_v) (Conc.tick t) = true
.

Definition galois {CT AT} (γ : concret) (α : CT -> AT) :=
  forall (t : CT), γ (α t) t = true.

Fixpoint dy_ctx_bound `{Conc.time CT} C t :=
  match C with
  | [||] => True
  | dy_c_lam _ t' C'
  | dy_c_lete _ t' C' => t' < t /\ dy_ctx_bound C' t
  | dy_c_letm _ CM C' => dy_ctx_bound CM t /\ dy_ctx_bound C' t
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

Definition eq_bound
  `{Conc.time CT} {AT} t (α : CT -> AT) α' :=
  forall t' (LE : leb t' t = true), α t' = α' t'.

Lemma eq_bound_comm :
  forall `{Conc.time CT} {AT} t (α : CT -> AT) α',
  eq_bound t α α' <-> eq_bound t α' α.
Proof.
  intros. split; intros EQ; red; intros; specialize (EQ t' LE); eauto.
Qed.

Fixpoint trans_ctx {CT AT} (α : CT -> AT) (C : @dy_ctx CT) :=
  match C with
  | [||] => [||]
  | dy_c_lam x t C' => dy_c_lam x (α t) (trans_ctx α C')
  | dy_c_lete x t C' => dy_c_lete x (α t) (trans_ctx α C')
  | dy_c_letm M CM C' => dy_c_letm M (trans_ctx α CM) (trans_ctx α C')
  end.

Definition sound `{Conc.time CT} `{Abs.time AT} 
  (α : CT -> AT) C st abs_C abs_st :=
  match abs_st with
  | Abs.ST abs_mem abs_t =>
    match st with
    | ST mem t =>
      α t = abs_t /\
      trans_ctx α C = abs_C /\
      forall p (BOUND : p < t),
        match mem p with
        | None => True
        | Some (Closure x e Cv) =>
          let l := abs_mem (α p) in
          In (Closure x e (trans_ctx α Cv)) l
        end
    end
  end.

Lemma trans_ctx_addr :
  forall {CT AT} (α : CT -> AT) C x,
    addr_x (trans_ctx α C) x = 
      match (addr_x C x) with 
      | None => None 
      | Some addr => Some (α addr) 
      end.
Proof.
  induction C; eauto.
  - intros. specialize (IHC x0).
    simpl. rewrite IHC.
    destruct (addr_x C x0); simpl; eauto.
    destruct (eq_eid x0 x); eauto.
  - intros. specialize (IHC x0).
    simpl. rewrite IHC.
    destruct (addr_x C x0); simpl; eauto.
    destruct (eq_eid x0 x); eauto.
Qed.

Lemma trans_ctx_ctx_M :
  forall {CT AT} C (α : CT -> AT) abs_C M C_M
        (ACCESS : ctx_M C M = Some C_M)
        (TRANS : trans_ctx α C = abs_C),
    ctx_M abs_C M = Some (trans_ctx α C_M).
Proof.
  assert (forall {CT AT} C (α : CT -> AT) M,
    match ctx_M (trans_ctx α C) M with
    | Some _ => 
      match ctx_M C M with
      | Some _ => True
      | None => False
      end
    | None =>
      match ctx_M C M with
      | Some _ => False
      | None => True
      end
    end) as A.
  {
    induction C; intros; simpl; eauto; try apply IHC.
    destruct (eq_mid M0 M); 
    remember (ctx_M (trans_ctx α C2) M0) as ctx';
    destruct ctx';
    specialize (IHC2 α M0);
    rewrite <- Heqctx' in IHC2;
    destruct (ctx_M C2 M0);
    try inversion IHC2; eauto.
  }
  intros. revert C α abs_C M C_M ACCESS TRANS. 
  induction C; intros; simpl in *; eauto.
  - inversion ACCESS.
  - rewrite <- TRANS. simpl. apply IHC; eauto.
  - rewrite <- TRANS. simpl. apply IHC; eauto. 
  - rewrite <- TRANS. simpl.
    remember (ctx_M (trans_ctx α C2) M0) as ctx1.
    destruct ctx1; try (inversion ACCESS; fail).
    + specialize (A CT AT C2 α M0).
      rewrite <- Heqctx1 in A.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion A; inversion ACCESS; subst.
      rewrite Heqctx1. apply IHC2; eauto.
    + specialize (A CT AT C2 α M0).
      rewrite <- Heqctx1 in A.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion A; destruct (eq_mid M0 M);
      inversion ACCESS; subst; eauto.
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
  - lebt (tick t). lebt t2. lebt t.
  - lebt t1.
  - lebt (tick t). lebt t.
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
  forall `{Conc.time CT} (t' : CT) (t : CT) (LE : leb t' t = true),
  eqb t' (tick t) = false.
Proof.
  intros. refl_bool. intros contra.
  rewrite eqb_eq in *.
  assert (t <> tick t) as NEQ.
  { rewrite <- eqb_neq. apply tick_lt. }
  apply NEQ. apply leb_sym. 
  apply tick_lt.
  subst. eauto.
Qed.

Lemma time_bound_tick :
  forall `{Conc.time CT} x e C mem t
         (B : time_bound C (ST mem t)),
  time_bound C (ST (t !-> Closure x e C; mem) (tick t)).
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

Lemma eq_bound_tick :
  forall `{Conc.time CT} `{Abs.time AT} (t : CT) (abs_t : AT) (α : CT -> AT),
  eq_bound t α (fun t' => if eqb t' (tick t) then abs_t else α t').
Proof.
  intros. red. intros.
  replace (eqb t' (tick t)) with false. eauto.
  symmetry. refl_bool. intros contra.
  rewrite leb_t_neq_tick in contra; eauto.
  inversion contra.
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

Lemma plugin_trans_ctx :
  forall {CT AT} Cout Cin (α : CT -> AT),
    trans_ctx α (Cout[|Cin|]) = (trans_ctx α Cout [|trans_ctx α Cin|]).
Proof.
  induction Cout; intros; simpl; 
  try rewrite IHCout; try rewrite IHCout1; try rewrite IHCout2;
  eauto.
Qed.

Lemma bound_trans_ctx_eq :
  forall `{Conc.time CT} {AT} C t (α : CT -> AT) α',
         dy_ctx_bound C t ->
         eq_bound t α α' ->
         trans_ctx α C = trans_ctx α' C.
Proof.
  intros. 
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  rename H2 into BOUND. rename H3 into EQ.
  revert C t α α' BOUND EQ.
  induction C; intros; simpl; try erewrite IHC; 
  try erewrite IHC1; try erewrite IHC2; simpl in *; eauto;
  destruct BOUND; eauto; destruct H; rewrite EQ; eauto.
Qed.

Lemma eqb_refl : forall `{Eq CT} t, eqb t t = true.
Proof.
  intros. rewrite eqb_eq. eauto.
Qed.

Lemma galois_tick `{Conc.time CT} `{Abs.time AT} (γ : concret) (PRES : preserve_tick γ) :
  forall α (GALOIS : galois γ α) (t : CT) abs_C abs_mem abs_t x abs_v (EQ : α t = abs_t),
  galois γ (fun t' => if eqb t' (tick t) then Abs.tick abs_C (Abs.ST abs_mem abs_t) x abs_v else α t').
Proof.
  intros. red. intros.
  destruct (eqb t0 (tick t)) eqn:EQt.
  - red in PRES. rewrite eqb_eq in EQt. rewrite EQt. apply PRES.
    red in GALOIS. rewrite <- EQ. apply GALOIS.
  - apply GALOIS.
Qed.

(* Set Printing Implicit. *)

Lemma sound_eval `{Conc.time CT} `{Abs.time AT} (γ : concret) (PRES : preserve_tick γ) :
  forall C st e v' st'
         (EVAL : EvalR C st e v' st')
         (BOUND : time_bound C st)
         abs_C abs_st α
         (SOUND : sound α C st abs_C abs_st)
         (GALOIS : galois γ α),
    exists abs_C' abs_st' α',
      match st with
      | ST _ t =>
        eq_bound t α α' /\
        galois γ α' /\
        match v' with
        | EVal (Closure x' e' C') =>
          sound α' C' st' abs_C' abs_st' /\
          Abs.EvalR 
            abs_C abs_st e 
            (EVal (Closure x' e' (trans_ctx α' C')))
            abs_st'
        | MVal C' =>
          sound α' C' st' abs_C' abs_st' /\
          Abs.EvalR 
            abs_C abs_st e 
            (MVal (trans_ctx α' C'))
            abs_st' 
        end
      end.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  rename H2 into EAT. rename H3 into T2.
  revert abs_C abs_st α SOUND GALOIS. induction EVAL; intros; subst.
  - unfold sound in SOUND. destruct abs_st as [abs_mem abs_t].
    destruct SOUND as [? [? ?]].
    specialize (H1 addr) as HINT. rewrite <- ACCESS in HINT.
    destruct v as [v e C'].
    exists (trans_ctx α C'). exists (Abs.ST abs_mem abs_t). exists α.
    repeat split; try red; intros; eauto. apply H1. eauto.
    apply Abs.Eval_var_e with (addr := α addr) (mem := abs_mem) (t := abs_t); eauto.
    rewrite <- H0. rewrite trans_ctx_addr.
    destruct (addr_x C x); inversion ADDR; subst; eauto.
    apply HINT. simpl in BOUND. destruct BOUND.
    pose proof (time_bound_addr C x t H2). rewrite <- ADDR in *. eauto.
  - exists abs_C. exists abs_st. exists α. repeat split; eauto.
    destruct st; simpl; repeat split; try red; intros; eauto.
    destruct abs_st. simpl in SOUND. destruct SOUND as [? [? ?]].
    rewrite H0. eauto.
  - pose proof (time_bound_e C st e1 (EVal (Closure x e C_lam)) st_lam EVAL1) as BOUND'.
    pose proof (time_bound_e C st_lam e2 (EVal arg) (ST mem t) EVAL2) as BOUND''.
    pose proof (time_bound_e (C_lam [|dy_c_lam x t ([||])|])
                             (ST (t !-> arg; mem) (tick t))
                             e (EVal v) st_v EVAL3) as BOUND'''.
    specialize (BOUND' BOUND). simpl in BOUND'.
    destruct st. destruct st_lam. destruct st_v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    apply time_increase_e in EVAL3 as time_inc3.
    assert (time_bound C (ST mem1 t1)) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [? [? ?]].
             simpl in BOUND'. destruct BOUND' as [? [? ?]].
      split. eapply relax_ctx_bound. eauto. eauto.
      split; eauto. }
    specialize (BOUND'' B1).
    destruct arg. destruct v.
    assert (time_bound (C_lam [|dy_c_lam x t ([||])|])
             (ST (t !-> Closure x0 e0 C0; mem) (tick t))) as B2.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND'. destruct BOUND' as [BB1' [BB2' BB3']].
             simpl in BOUND''. destruct BOUND'' as [BB1'' [BB2'' BB3'']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. lebt t.
      simpl. split; eauto. split. apply tick_lt. apply tick_lt.
      apply time_bound_tick. repeat split; eauto. }
    specialize (BOUND''' B2).
    specialize (IHEVAL1 BOUND). specialize (IHEVAL2 B1). specialize (IHEVAL3 B2). 
    specialize (IHEVAL1 abs_C abs_st α SOUND).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' SOUND']]]]; eauto.
    assert (sound α' C (ST mem1 t1) abs_C abs_st').
    { destruct abs_st'. simpl. simpl in SOUND'. destruct SOUND' as [G' [[? [? ?]] ?]].
      repeat split; eauto. destruct abs_st. simpl in SOUND. destruct SOUND as [? [RR ?]].
      rewrite <- RR. symmetry. eapply bound_trans_ctx_eq; simpl in BOUND; destruct BOUND; eauto. }
    specialize (IHEVAL2 abs_C abs_st' α' H). clear H.
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α'' [EQ'' SOUND'']]]]. apply SOUND'.
    destruct abs_st'' as [mem'' t''].
    remember (fun t' => if eqb t' (tick t)
                        then Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'') 
                        else α'' t') as α'''.
    assert (eq_bound t α'' α''') as EQ'''.
    { rewrite Heqα'''. apply eq_bound_tick. }
    assert (sound α''' (C_lam [|dy_c_lam x t ([||])|])
            (ST (t !-> Closure x0 e0 C0; mem) (tick t))
            (abs_C'[| dy_c_lam x (α'' t) ([||]) |])
            (Abs.ST ((α'' t) !#-> Closure x0 e0 abs_C''; mem'') 
                    (Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'')))).
    { clear EVAL1 EVAL2 EVAL3 BOUND SOUND IHEVAL3 EQ' time_inc1 C mem0 t0 B1 B2.
      destruct SOUND' as [? [SOUND' ?]]. clear H H0.
      destruct SOUND'' as [? [SOUND'' ?]]. clear H H0.
      rewrite Heqα'''. simpl. repeat split.
      - rewrite eqb_refl. eauto.
      - rewrite plugin_trans_ctx; simpl.
        replace (eqb t (tick t)) with false; try (symmetry; apply tick_lt).
        rewrite <- Heqα'''.
        replace (trans_ctx α''' C_lam) with abs_C'. eauto.
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [? [RR ?]]. rewrite <- RR.
        apply bound_trans_ctx_eq with (t := t1). apply BOUND'.
        rewrite Heqα'''. red. intros. rewrite leb_t_neq_tick. apply EQ''. eauto. lebt t1.
      - rewrite <- Heqα'''. destruct SOUND'' as [? [RR HINT]].
        unfold update_m. unfold Abs.update_m. intros.
        destruct (eqb p t) eqn:EQ.
        + rewrite eqb_eq in EQ. rewrite EQ.
          replace (eqb t (tick t)) with false; try (symmetry; apply tick_lt).
          rewrite eqb_refl.
          replace (trans_ctx α''' C0) with (trans_ctx α'' C0).
          left; rewrite RR; eauto.
          apply bound_trans_ctx_eq with (t := t); eauto. apply BOUND''.
        + pose proof (p_bound_or_not p t) as CASES.
          destruct BOUND'' as [B1'' [B2'' B3'']].
          destruct CASES as [L | R]; 
          try (specialize (B2'' p R); rewrite B2''; eauto; fail).
          destruct (mem p) eqn: ACCESS; eauto. destruct e4.
          specialize (HINT p L). rewrite ACCESS in HINT.
          replace (eqb p (tick t)) with false; try (symmetry; apply BOUND).
          replace (trans_ctx α''' C) with (trans_ctx α'' C).
          { destruct (eqb (α'' p) (α'' t)) eqn:EQb;
            try (rewrite eqb_eq in EQb; rewrite <- EQb; right); apply HINT. }
          { apply bound_trans_ctx_eq with (t := t); eauto.
            specialize (B3'' p L). rewrite ACCESS in B3''. exact B3''. }
    }
    specialize (IHEVAL3 (abs_C' [|dy_c_lam x (α'' t) ([||])|])
                (Abs.ST
                  (α'' t !#-> Closure x0 e0 abs_C''; mem'')
                  (Abs.tick abs_C (Abs.ST mem'' t'') x
                  (Closure x0 e0 abs_C''))) α''' H).
    destruct IHEVAL3 as [abs_C''' [abs_st''' [α'''' [EQ'''' SOUND''']]]].
    rewrite Heqα'''. apply galois_tick. apply PRES. apply SOUND''. 
    destruct SOUND'' as [? [RR ?]]. apply RR.
    destruct SOUND' as [? [SOUND' EVAL']].
    destruct SOUND'' as [? [SOUND'' EVAL'']].
    destruct SOUND''' as [? [SOUND''' EVAL''']].
    exists abs_C'''. exists abs_st'''. exists α''''. repeat split; eauto.
    red. intros. 
    assert (α t' = α' t') as RR. apply EQ'. eauto. rewrite RR; clear RR.
    assert (α' t' = α'' t') as RR. apply EQ''. lebt t0. rewrite RR; clear RR.
    assert (α'' t' = α''' t') as RR. apply EQ'''. lebt t1. lebt t0. rewrite RR; clear RR.
    apply EQ''''. lebt t. lebt t1. lebt t0.
    eapply Abstract.Eval_app. exact EVAL'. exact EVAL''.
    destruct abs_st'. simpl in SOUND'. destruct SOUND' as [EQt' [RR ?]].
    rewrite RR. simpl in SOUND''. destruct SOUND'' as [EQt'' [RR' ?]].
    rewrite RR'. rewrite <- EQt''. rewrite <- EQt'' in EVAL'''. exact EVAL'''.
  - pose proof (time_bound_e C st m (MVal C_m) st_m EVAL1) as BOUND'.
    pose proof (time_bound_e C_m st_m e v st_v EVAL2) as BOUND''.
    specialize (BOUND' BOUND). simpl in BOUND'. 
    specialize (BOUND'' BOUND'). simpl in BOUND''.
    destruct st. destruct st_m. destruct st_v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    specialize (IHEVAL1 BOUND abs_C abs_st α SOUND GALOIS).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' [GALOIS' SOUND']]]]].
    destruct SOUND' as [SOUND' EVAL']. 
    specialize (IHEVAL2 BOUND' abs_C' abs_st' α' SOUND' GALOIS').
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α'' [EQ'' [GALOIS'' SOUND'']]]]].
    destruct v; try destruct ev;
    destruct SOUND'' as [SOUND'' EVAL''];
    exists abs_C''; exists abs_st''; exists α''; repeat split; eauto;
    unfold eq_bound in *; intros;
    try assert (α'' t' = α' t'); try symmetry; try apply EQ''; try lebt t;
    try (rewrite H; symmetry; apply EQ'; eauto);
    eapply Abstract.Eval_link; eauto;
    destruct abs_st'; simpl in SOUND'; destruct SOUND' as [? [RR ?]];
    rewrite RR; eauto.
  - exists abs_C. exists abs_st. exists α. destruct st.
    repeat split; eauto. unfold eq_bound; intros; eauto.
    destruct abs_st. simpl in SOUND. destruct SOUND as [? [RR ?]].
    rewrite RR. eauto.
  - exists (trans_ctx α C_M). exists abs_st. exists α. destruct st.
    destruct abs_st. destruct SOUND as [? [RR ?]].
    repeat split; eauto. rewrite <- RR.
    eapply Abstract.Eval_var_m. erewrite trans_ctx_ctx_M; eauto.
  - pose proof (time_bound_e C st e (EVal v) (ST mem t) EVAL1) as BOUND'.
    pose proof (time_bound_e (C [|dy_c_lete x t ([||])|]) 
                             (ST (t !-> v; mem) (tick t)) m
                             (MVal C_m) st_m EVAL2) as BOUND''.
    specialize (BOUND' BOUND). simpl in BOUND'.
    destruct st. destruct st_m. destruct v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (time_bound (C [|dy_c_lete x t ([||])|])
            (ST (t !-> (Closure x0 e0 C0); mem) (tick t))) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND'. destruct BOUND' as [BB1' [BB2' BB3']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. lebt t.
      simpl. split; eauto. apply tick_lt.
      apply time_bound_tick. repeat split; eauto. }
    specialize (BOUND'' B1).
    specialize (IHEVAL1 BOUND). specialize (IHEVAL2 B1).
    specialize (IHEVAL1 abs_C abs_st α SOUND GALOIS).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' [GALOIS' SOUND']]]]].
    remember (fun t' => if eqb t' (tick t)
                        then Abs.tick abs_C abs_st'
                                        x (Closure x0 e0 abs_C') 
                        else α' t') as α''.
    destruct abs_st as [mem' t']. destruct abs_st' as [mem'' t''].
    assert (eq_bound t α' α'') as EQ''.
    { rewrite Heqα''. apply eq_bound_tick. }
    assert (sound α'' (C [|dy_c_lete x t ([||])|])
            (ST (t !-> Closure x0 e0 C0; mem) (tick t))
            (abs_C [| dy_c_lete x (α' t) ([||]) |])
            (Abs.ST ((α' t) !#-> Closure x0 e0 abs_C'; mem'') 
                    (Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C')))).
    { destruct SOUND' as [SOUND' ?]. clear H.
      rewrite Heqα''. simpl. repeat split.
      - rewrite eqb_refl. eauto.
      - rewrite plugin_trans_ctx; simpl.
        replace (eqb t (tick t)) with false; try (symmetry; apply tick_lt).
        rewrite <- Heqα''.
        replace (trans_ctx α'' C) with abs_C. eauto.
        destruct SOUND as [? [RR ?]]. rewrite <- RR.
        apply bound_trans_ctx_eq with (t := t0). apply BOUND.
        rewrite Heqα''. red. intros. rewrite leb_t_neq_tick. apply EQ'. eauto. lebt t0.
      - rewrite <- Heqα''. destruct SOUND' as [? [RR HINT]].
        unfold update_m. unfold Abs.update_m. intros.
        destruct (eqb p t) eqn:EQ.
        + rewrite eqb_eq in EQ. rewrite EQ.
          replace (eqb t (tick t)) with false; try (symmetry; apply tick_lt).
          rewrite eqb_refl.
          replace (trans_ctx α'' C0) with (trans_ctx α' C0).
          left; rewrite RR; eauto.
          apply bound_trans_ctx_eq with (t := t); eauto. apply BOUND'.
        + pose proof (p_bound_or_not p t) as CASES.
          destruct BOUND' as [B1' [B2' B3']].
          destruct CASES as [L | R]; 
          try (specialize (B2' p R); rewrite B2'; eauto; fail).
          destruct (mem p) eqn: ACCESS; eauto. destruct e1.
          specialize (HINT p L). rewrite ACCESS in HINT.
          replace (eqb p (tick t)) with false; try (symmetry; apply BOUND0).
          replace (trans_ctx α'' C1) with (trans_ctx α' C1).
          { destruct (eqb (α' p) (α' t)) eqn:EQb;
            try (rewrite eqb_eq in EQb; rewrite <- EQb; right); apply HINT. }
          { apply bound_trans_ctx_eq with (t := t); eauto.
            specialize (B3' p L). rewrite ACCESS in B3'. exact B3'. }
    }
    specialize (IHEVAL2 (abs_C [|dy_c_lete x (α' t) ([||])|])
                (Abs.ST
                  (α' t !#-> Closure x0 e0 abs_C'; mem'')
                  (Abs.tick abs_C (Abs.ST mem'' t'') x
                  (Closure x0 e0 abs_C'))) α'' H). clear H.
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α''' [EQ''' SOUND''']]]].
    rewrite Heqα''. apply galois_tick. apply PRES. eauto. apply SOUND'. 
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND''' as [GALOIS''' [SOUND''' EVAL''']].
    exists abs_C''. exists abs_st''. exists α'''. repeat split; eauto.
    red. intros. 
    assert (α t'0 = α' t'0) as RR. apply EQ'. eauto. rewrite RR; clear RR.
    assert (α' t'0 = α'' t'0) as RR. apply EQ''. lebt t0. rewrite RR; clear RR.
    apply EQ'''. lebt t. lebt t0.
    eapply Abstract.Eval_lete; eauto.
    destruct SOUND' as [? [RR ?]]. rewrite RR. 
    destruct abs_st''. destruct SOUND''' as [? [RR' ?]]. rewrite RR' in *.
    rewrite <- H. rewrite <- H in EVAL'''.
    rewrite <- RR in *. exact EVAL'''.
  - pose proof (time_bound_e C st m' (MVal C') st' EVAL1) as BOUND'.
    pose proof (time_bound_e (C [|dy_c_letm M C' ([||])|]) st' m''
                             (MVal C'') st'' EVAL2) as BOUND''.
    specialize (BOUND' BOUND). simpl in BOUND'.
    destruct st. destruct st'. destruct st''.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (time_bound (C [|dy_c_letm M C' ([||])|])
            (ST mem0 t0)) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND'. destruct BOUND' as [BB1' [BB2' BB3']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. eauto. simpl. split; eauto. split; eauto. }
    specialize (BOUND'' B1).
    specialize (IHEVAL1 BOUND). specialize (IHEVAL2 B1).
    specialize (IHEVAL1 abs_C abs_st α SOUND GALOIS).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' [GALOIS' SOUND']]]]].
    assert (sound α' (C [|dy_c_letm M C' ([||])|]) (ST mem0 t0)
            (abs_C [|dy_c_letm M abs_C' ([||]) |]) abs_st').
    { unfold sound in *. destruct abs_st'. destruct abs_st.
      destruct SOUND' as [[? [? ?]] ?].
      destruct SOUND as [? [? ?]].
      repeat split; simpl; eauto.
      rewrite plugin_trans_ctx. simpl.
      assert (trans_ctx α' C = abs_C).
      rewrite <- H4. apply bound_trans_ctx_eq with (t := t).
      simpl in BOUND. destruct BOUND; eauto. 
      red; intros. red in EQ'. symmetry; apply EQ'; eauto.
      rewrite H6.
      assert (trans_ctx α' C' = abs_C').
      rewrite <- H0. eauto. rewrite H7. eauto.
    }
    assert (eq_bound t α' α') as EQ''.
    { red. intros; eauto. }
    specialize (IHEVAL2 (abs_C [|dy_c_letm M abs_C' ([||])|])
                        abs_st' α' H GALOIS').
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α'' [EQ''' [GALOIS'' SOUND''']]]]].
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND''' as [SOUND''' EVAL'''].
    exists abs_C''. exists abs_st''. exists α''. repeat split; eauto.
    red. intros. 
    assert (α t' = α' t') as RR. apply EQ'. eauto. rewrite RR; clear RR.
    apply EQ'''. lebt t.
    eapply Abstract.Eval_letm; eauto.
    destruct abs_st'. destruct SOUND' as [? [RR ?]].
    destruct abs_st''. destruct SOUND''' as [? [RR' ?]].
    rewrite RR in *. rewrite RR' in *. eauto.
Qed.

Lemma sound_reach `{Conc.time CT} `{Abs.time AT} (γ : concret) (PRES : preserve_tick γ) :
  forall C st e C' st' e'
         (REACH : one_reach C st e C' st' e')
         (BOUND : time_bound C st)
         abs_C abs_st α
         (SOUND : sound α C st abs_C abs_st)
         (GALOIS : galois γ α),
    exists abs_C' abs_st' α',
      match st with
      | ST _ t =>
        eq_bound t α α' /\
        galois γ α' /\
        sound α' C' st' abs_C' abs_st' /\
        Abs.one_reach abs_C abs_st e abs_C' abs_st' e'
      end.
Proof.
  intros.
  rename H into ECT. rename H0 into OCT. rename H1 into T1.
  rename H2 into EAT. rename H3 into T2.
  destruct st.
  destruct REACH.
  - exists abs_C. exists abs_st. exists α.
    repeat split; eauto. apply Abs.one_appl.
  - eapply sound_eval in FN; eauto.
    destruct FN as [abs_C' [abs_st' [α' [EQ [GALOIS' [SOUND' EVAL']]]]]].
    exists abs_C. exists abs_st'. exists α'.
    repeat split; eauto.
    destruct abs_st'; simpl in *. destruct st_lam.
    destruct SOUND' as [? [RR' ?]].
    repeat split; eauto.
    destruct abs_st; simpl in SOUND.
    destruct SOUND as [? [RR ?]].
    rewrite <- RR.
    destruct BOUND as [? [? ?]].
    eapply bound_trans_ctx_eq; eauto.
    rewrite eq_bound_comm. eauto.
    eapply Abs.one_appr; eauto.
  - eapply sound_eval in FN as SOUND'; eauto.
    destruct SOUND' as [abs_C' [abs_st' [α' [EQ [GALOIS' [SOUND' EVAL']]]]]].
    apply time_bound_e in FN as BOUND'; eauto.
    destruct st_lam; simpl in BOUND'. simpl in BOUND.
    destruct BOUND as [BOUND [NONE SOME]].
    destruct BOUND' as [BOUND' [NONE' SOME']].
    apply time_increase_e in FN as INC'; eauto.
    assert (dy_ctx_bound C t1).
    { eapply relax_ctx_bound; eauto. }
    assert (sound α' C (ST mem1 t1) abs_C abs_st').
    { destruct abs_st'; destruct SOUND' as [? [? ?]].
      destruct abs_st; destruct SOUND as [? [RR ?]].
      repeat split; eauto. rewrite <- RR.
      apply bound_trans_ctx_eq with (t := t); eauto.
      rewrite eq_bound_comm. eauto. }
    eapply sound_eval in ARG as SOUND''; repeat split; eauto.
    destruct arg. destruct SOUND'' as [abs_C'' [abs_st'' [α'' [EQ'' [GALOIS'' [SOUND'' EVAL'']]]]]].
    apply time_bound_e in ARG as BOUND''; repeat split; eauto. clear H H0.
    apply time_increase_e in ARG as INC''; eauto.
    destruct abs_st' as [mem' t']. destruct abs_st'' as [mem'' t''].
    replace (trans_ctx α'' C0) with abs_C'' in *;
    try (destruct SOUND'' as [? [? ?]]; eauto; fail).
    replace (trans_ctx α' C_lam) with abs_C' in *;
    try (destruct SOUND' as [? [? ?]]; eauto; fail).
    remember (fun t => if eqb t (tick t0)
                        then Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'') 
                        else α'' t) as α'''.
    assert (eq_bound t0 α'' α''') as EQ'''.
    { rewrite Heqα'''. apply eq_bound_tick. }
    assert (sound α''' (C_lam [|dy_c_lam x t0 ([||])|])
            (ST (t0 !-> Closure x0 e0 C0; mem0) (tick t0))
            (abs_C'[| dy_c_lam x t'' ([||]) |])
            (Abs.ST (t'' !#-> Closure x0 e0 abs_C''; mem'') 
                    (Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'')))).
    { rewrite Heqα'''. simpl. repeat split.
      - rewrite eqb_refl. eauto.
      - rewrite plugin_trans_ctx; simpl.
        replace (eqb t0 (tick t0)) with false; try (symmetry; apply tick_lt).
        rewrite <- Heqα'''.
        replace (trans_ctx α''' C_lam) with abs_C'. destruct SOUND'' as [RR ?]; rewrite RR; eauto.
        destruct SOUND' as [? [RR ?]]. rewrite <- RR.
        apply bound_trans_ctx_eq with (t := t1). apply BOUND'.
        rewrite Heqα'''. red. intros. rewrite leb_t_neq_tick. apply EQ''. eauto. lebt t1.
      - rewrite <- Heqα'''. destruct SOUND'' as [? [RR HINT]].
        unfold update_m. unfold Abs.update_m. intros.
        destruct (eqb p t0) eqn:EQp.
        + rewrite eqb_eq in EQp. rewrite EQp.
          replace (eqb t0 (tick t0)) with false; try (symmetry; apply tick_lt).
          rewrite H; rewrite eqb_refl.
          replace (trans_ctx α''' C0) with (trans_ctx α'' C0).
          left; rewrite RR; eauto.
          apply bound_trans_ctx_eq with (t := t0); eauto. apply BOUND''.
        + pose proof (p_bound_or_not p t0) as CASES.
          destruct BOUND'' as [B1'' [B2'' B3'']].
          destruct CASES as [L | R]; 
          try (specialize (B2'' p R); rewrite B2''; eauto; fail).
          destruct (mem0 p) eqn: ACCESS; eauto. destruct e3.
          specialize (HINT p L). rewrite ACCESS in HINT.
          replace (eqb p (tick t0)) with false; try (symmetry; apply BOUND0).
          replace (trans_ctx α''' C1) with (trans_ctx α'' C1).
          { rewrite <- H. 
            destruct (eqb (α'' p) (α'' t0)) eqn:EQb;
            try (rewrite eqb_eq in EQb; rewrite <- EQb; right); apply HINT. }
          { apply bound_trans_ctx_eq with (t := t0); eauto.
            specialize (B3'' p L). rewrite ACCESS in B3''. exact B3''. }
    }
    exists (abs_C' [|dy_c_lam x t'' ([||])|]).
    exists (Abs.ST (t'' !#-> Closure x0 e0 abs_C''; mem'')
                   (Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C''))).
    exists α'''.
    split. red; intros.
    replace (α t'0) with (α' t'0).
    replace (α' t'0) with (α'' t'0).
    apply EQ'''. lebt t. lebt t1.
    symmetry. apply EQ''. lebt t.
    symmetry. apply EQ. eauto.
    split. rewrite Heqα'''. apply galois_tick; eauto. apply SOUND''.
    split. exact H.
    eapply Abs.one_appbody; eauto.
  - exists abs_C. exists abs_st. exists α.
    split. red; intros; eauto.
    split. eauto.
    split. apply SOUND.
    eapply Abs.one_linkl; eauto.
  - eapply sound_eval in MOD; eauto.
    destruct MOD as [abs_C' [abs_st' [α' [EQ [GALOIS' [SOUND' EVAL']]]]]].
    exists (trans_ctx α' C_m). exists abs_st'. exists α'.
    repeat split; eauto.
    destruct abs_st'; simpl in *. destruct st_m.
    destruct SOUND' as [? [RR' ?]].
    repeat split; eauto.
    eapply Abs.one_linkr; eauto.
  - exists abs_C. exists abs_st. exists α.
    split. red; intros; eauto.
    split. eauto.
    split. apply SOUND.
    eapply Abs.one_letel.
  - eapply sound_eval in EVALx as SOUND'; eauto. destruct v.
    destruct SOUND' as [abs_C' [abs_st' [α' [EQ [GALOIS' [SOUND' EVAL']]]]]].
    eapply time_increase_e in EVALx as INC'; eauto.
    eapply time_bound_e in EVALx as BOUND'; eauto.
    destruct abs_st as [mem' t']. destruct abs_st' as [mem'' t''].
    replace (trans_ctx α' C0) with abs_C' in *; try (symmetry; destruct SOUND' as [? [? ?]]; eauto).
    remember (fun t => if eqb t (tick t0)
                       then Abs.tick abs_C (Abs.ST mem'' t'')
                             x (Closure x0 e0 abs_C') 
                       else α' t) as α''.
    assert (eq_bound t0 α' α'') as EQ''.
    { rewrite Heqα''. apply eq_bound_tick. }
    assert (sound α'' (C [|dy_c_lete x t0 ([||])|])
            (ST (t0 !-> Closure x0 e0 C0; mem0) (tick t0))
            (abs_C [| dy_c_lete x t'' ([||]) |])
            (Abs.ST (t'' !#-> Closure x0 e0 abs_C'; mem'') 
                    (Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C')))).
    { rewrite Heqα''. simpl. repeat split.
      - rewrite eqb_refl. eauto.
      - destruct SOUND' as [? [? ?]].
        rewrite plugin_trans_ctx; simpl.
        replace (eqb t0 (tick t0)) with false; try (symmetry; apply tick_lt).
        rewrite <- Heqα''.
        replace (trans_ctx α'' C) with abs_C.
        replace (α' t0) with t''. eauto.
        destruct SOUND as [? [RR ?]]. rewrite <- RR.
        apply bound_trans_ctx_eq with (t := t). apply BOUND.
        rewrite Heqα''. red. intros. rewrite leb_t_neq_tick. apply EQ. eauto. lebt t.
      - rewrite <- Heqα''. destruct SOUND' as [? [RR HINT]].
        unfold update_m. unfold Abs.update_m. intros.
        destruct (eqb p t0) eqn:EQp.
        + rewrite eqb_eq in EQp. rewrite EQp.
          replace (eqb t0 (tick t0)) with false; try (symmetry; apply tick_lt).
          replace t'' with (α' t0). rewrite eqb_refl.
          replace (trans_ctx α'' C0) with (trans_ctx α' C0).
          left; rewrite RR; eauto.
          apply bound_trans_ctx_eq with (t := t0); eauto. apply BOUND'.
        + pose proof (p_bound_or_not p t0) as CASES.
          destruct BOUND' as [B1' [B2' B3']].
          destruct CASES as [L | R]; 
          try (specialize (B2' p R); rewrite B2'; eauto; fail).
          destruct (mem0 p) eqn: ACCESS; eauto. destruct e1.
          specialize (HINT p L). rewrite ACCESS in HINT.
          replace (eqb p (tick t0)) with false; try (symmetry; apply BOUND0).
          replace (trans_ctx α'' C1) with (trans_ctx α' C1).
          { replace t'' with (α' t0).
            destruct (eqb (α' p) (α' t0)) eqn:EQb;
            try (rewrite eqb_eq in EQb; rewrite <- EQb; right); apply HINT. }
          { apply bound_trans_ctx_eq with (t := t0); eauto.
            specialize (B3' p L). rewrite ACCESS in B3'. exact B3'. }
    }
    exists (abs_C [|dy_c_lete x t'' ([||])|]).
    exists (Abs.ST (t'' !#-> Closure x0 e0 abs_C'; mem'')
                   (Abs.tick abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'))).
    exists α''.
    split. red; intros.
    replace (α t'0) with (α' t'0).
    apply EQ''. lebt t. 
    symmetry. apply EQ. eauto.
    split. rewrite Heqα''. apply galois_tick; eauto. apply SOUND'.
    split. exact H.
    eapply Abs.one_leter; eauto.
  - exists abs_C. exists abs_st. exists α.
    split. red; intros; eauto.
    split. assumption.
    split. assumption.
    apply Abs.one_letml.
  - eapply sound_eval in EVALM as SOUND'; eauto.
    destruct SOUND' as [abs_C' [abs_st' [α' [EQ [GALOIS' [SOUND' EVAL']]]]]].
    eapply time_increase_e in EVALM as INC'; eauto.
    eapply time_bound_e in EVALM as BOUND'; eauto. destruct st_M.
    destruct abs_st as [mem' t']. destruct abs_st' as [mem'' t''].
    replace (trans_ctx α' C_M) with abs_C' in *;
    try (symmetry; destruct SOUND' as [? [? ?]]; eauto).
    assert (sound α' (C [|dy_c_letm M C_M ([||])|]) (ST mem0 t0)
            (abs_C [|dy_c_letm M abs_C' ([||]) |]) (Abs.ST mem'' t'')).
    { destruct SOUND' as [? [? ?]].
      destruct SOUND as [? [RR ?]].
      repeat split; simpl; eauto.
      rewrite plugin_trans_ctx. simpl.
      assert (trans_ctx α' C = abs_C) as RR'.
      rewrite <- RR. apply bound_trans_ctx_eq with (t := t).
      simpl in BOUND. destruct BOUND; eauto. 
      red; intros. symmetry; apply EQ; eauto.
      rewrite RR'.
      replace (trans_ctx α' C_M) with abs_C';
      try (symmetry; eauto).
    }
    exists (abs_C [|dy_c_letm M abs_C' ([||])|]).
    exists (Abs.ST mem'' t'').
    exists α'.
    split. red; intros; eauto.
    split. eauto.
    split. exact H.
    eapply Abs.one_letmr. eauto.
Qed.