From MODULAR Require Export Abstract.
From MODULAR Require Export Concrete.

Module Abs := Abstract.
Module Conc := Concrete.

Generalizable Variables CT.
Generalizable Variables AT.

Definition lt `{Conc.Time CT} (t1 : CT) (t2 : CT) :=
  leb t1 t2 = true /\ eqb t1 t2 = false.

Notation "t1 '<' t2" := (lt t1 t2).

Fixpoint dy_ctx_bound `{Conc.Time CT} C t :=
  match C with
  | [||] => True
  | dy_c_lam _ t' C'
  | dy_c_lete _ t' C' => t' < t /\ dy_ctx_bound C' t
  | dy_c_letm _ CM C' => dy_ctx_bound CM t /\ dy_ctx_bound C' t
  end.

Definition time_bound `{Conc.Time CT} C st :=
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
  forall `{Conc.Time CT} (p : CT) t,
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

Definition eq_bound_α 
  `{Conc.Time CT} `{Abs.Time AT} t (α : CT -> AT) α' :=
  forall t' (LE : leb t' t = true), α t' = α' t'.

Fixpoint trans_ctx `{Conc.Time CT} `{Abs.Time AT} (α : CT -> AT) C :=
  match C with
  | [||] => [||]
  | dy_c_lam x t C' => dy_c_lam x (α t) (trans_ctx α C')
  | dy_c_lete x t C' => dy_c_lete x (α t) (trans_ctx α C')
  | dy_c_letm M CM C' => dy_c_letm M (trans_ctx α CM) (trans_ctx α C')
  end.

Definition sound `{Conc.Time CT} `{Abs.Time AT} α C st abs_C abs_st :=
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
  forall `{Conc.Time CT} `{Abs.Time AT} α C x,
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
  forall `{Conc.Time CT} `{Abs.Time AT} C α abs_C M C_M
        (ACCESS : ctx_M C M = Some C_M)
        (TRANS : trans_ctx α C = abs_C),
    ctx_M abs_C M = Some (trans_ctx α C_M).
Proof.
  assert (forall `{Conc.Time CT} `{Abs.Time AT} C α M,
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
    end).
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
  induction C; intros; simpl in *; eauto.
  - inversion ACCESS.
  - rewrite <- TRANS. simpl. apply IHC; eauto.
  - rewrite <- TRANS. simpl. apply IHC; eauto. 
  - rewrite <- TRANS. simpl.
    remember (ctx_M (trans_ctx α C2) M0) as ctx1.
    destruct ctx1; try (inversion ACCESS; fail).
    + specialize (H CT H0 H1 AT H2 H3 C2 α M0).
      rewrite <- Heqctx1 in H.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion H; inversion ACCESS; subst.
      rewrite Heqctx1. apply IHC2; eauto.
    + specialize (H CT H0 H1 AT H2 H3 C2 α M0).
      rewrite <- Heqctx1 in H.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion H; destruct (eq_mid M0 M);
      inversion ACCESS; subst; eauto.
Qed.

Lemma time_increase_e :
  forall `{Conc.Time CT} `{Abs.Time AT} C st e e' st'
         (EVAL : EvalR C st e e' st'),
    match st with
    | ST _ t =>
      match st' with
      | ST _ t' => leb t t' = true
      end
    end.
Proof.
  intros. 
  induction EVAL;
  intros; 
  destruct st; try destruct st'; try destruct st''; try destruct st_v; 
  try destruct st_m; try destruct st_lam; simpl; try apply leb_refl.
  - inversion STATE; subst. apply leb_refl.
  - assert (t < update C (ST mem t) x arg).
    { apply update_lt. }
    destruct H3. 
    apply leb_trans with (t' := (update C (ST mem t) x arg)); eauto.
    apply leb_trans with (t' := t); eauto.
    apply leb_trans with (t' := t2); eauto.
  - apply leb_trans with (t' := t1); eauto.
  - assert (t < update C (ST mem t) x v).
    { apply update_lt. }
    destruct H3.
    apply leb_trans with (t' := (update C (ST mem t) x v)); eauto.
    apply leb_trans with (t' := t); eauto.
  - apply leb_trans with (t' := t0); eauto.
Qed.

Lemma relax_ctx_bound :
  forall `{Conc.Time CT} `{Abs.Time AT} 
         C t1 t2 (BOUND : dy_ctx_bound C t1) (LE : leb t1 t2 = true),
         dy_ctx_bound C t2.
Proof.
  induction C; intros; destruct BOUND; simpl in *; 
  repeat split;
  try eapply IHC; try eapply IHC1; try eapply IHC2; eauto;
  try destruct H3; try apply leb_trans with (t' := t1); eauto.
  rewrite eqb_neq in *. red. intros; subst. apply H5. apply leb_sym; eauto.
  rewrite eqb_neq in *. red. intros; subst. apply H5. apply leb_sym; eauto.
Qed.

Lemma relax_p_bound :
  forall `{Conc.Time CT} `{Abs.Time AT}
    p t1 t2 (BOUND : p < t1) (LE : leb t1 t2 = true),
  p < t2.
Proof.
  intros. destruct BOUND. split.
  apply leb_trans with (t' := t1); eauto.
  rewrite eqb_neq. red. intros; subst.
  assert (t1 = t2). apply leb_sym; eauto. subst.
  assert (true = eqb t2 t2). symmetry. apply eqb_eq; eauto.
  rewrite <- H5 in H4. inversion H4.
Qed.

Lemma time_bound_addr :
  forall `{Conc.Time CT} `{Abs.Time AT} C x t,
    dy_ctx_bound C t -> 
    match addr_x C x with
    | None => True
    | Some addr => addr < t
    end.
Proof.
  induction C; intros; simpl in *; try destruct H3; eauto.
  - specialize (IHC x0 t H4).
    destruct (addr_x C x0); eauto. 
    destruct (eq_eid x0 x); simpl; eauto.
  - specialize (IHC x0 t H4).
    destruct (addr_x C x0); eauto. 
    destruct (eq_eid x0 x); simpl; eauto.
  - apply IHC2; eauto.
Qed.

Lemma time_bound_ctx_M :
  forall `{Conc.Time CT} `{Abs.Time AT} C M t CM,
    ctx_M C M = Some CM ->
    dy_ctx_bound C t -> 
    dy_ctx_bound CM t.
Proof.
  induction C; intros; simpl in *.
  - inversion H3.
  - eapply IHC; eauto. destruct H4; eauto.
  - eapply IHC; eauto. destruct H4; eauto.
  - remember (ctx_M C2 M0) as oCM.
    destruct oCM.
    + inversion H3; subst. eapply IHC2; eauto.
      destruct H4; eauto.
    + destruct (eq_mid M0 M); inversion H3; subst.
      destruct H4; eauto.
Qed.

Lemma plugin_ctx_bound :
  forall `{Conc.Time CT} `{Abs.Time AT} Cout Cin t,
    dy_ctx_bound (Cout[|Cin|]) t <-> dy_ctx_bound Cout t /\ dy_ctx_bound Cin t.
Proof.
  intros. 
  rename H into O1. rename H0 into T1. rename H1 into O2. rename H2 into T2.
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


Ltac contradict :=
  let contra := fresh "contra" in
  assert False as contra; eauto 3; inversion contra.

Lemma __R__ : forall b, b = false <-> ~ b = true.
Proof. 
  intros; destruct b; unfold "<>"; split; 
  intros; try inversion H; try inversion H0; try contradict; eauto.
Qed.

Ltac refl_bool :=
  let contra := fresh "contra" in
  match goal with
  | |- _ = false => 
    rewrite __R__; unfold "<>"; intros contra
  | |- _ <> true => 
    rewrite <- __R__
  | _ => idtac
  end.

Ltac lebt x :=
  apply leb_trans with (t' := x); try assumption; try apply update_lt.

Lemma eqb_refl : forall `{OrderT CT} t, eqb t t = true.
Proof.
  intros. rewrite eqb_eq. eauto.
Qed.

Lemma eqb_update : forall `{Conc.Time CT} C mem t x x' e' C',
  eqb t (update C (ST mem t) x (Closure x' e' C')) = false.
Proof.
  intros. refl_bool.
  assert (t < update C (ST mem t) x (Closure x' e' C')) as contra'. apply update_lt.
  destruct contra' as [? contra']. rewrite contra' in *. inversion contra.
Qed.

Lemma time_bound_e :
  forall `{Conc.Time CT} `{Abs.Time AT} C st e e' st'
         (EVAL : EvalR C st e e' st')
         (BOUND : time_bound C st),
    match e' with
    | EVal (Closure _ _ C') => time_bound C' st'
    | MVal C' => time_bound C' st'
    end.
Proof.
  intros. 
  rename H into O1. rename H0 into T1.
  rename H1 into O2. rename H2 into T2.
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
    assert (t < (update C (ST mem t) x (Closure x1 e3 C1))).
    { apply update_lt. }
    apply IHEVAL3; simpl. split.
    rewrite plugin_ctx_bound. split.
    simpl in IHEVAL1. destruct IHEVAL1 as [? [? ?]].
    eapply relax_ctx_bound. eauto. destruct H.
    apply leb_trans with (t' := t); eauto.
    simpl. split; eauto.
    split; intros;
    unfold update_m; remember (eqb p t) as b;
    destruct b; symmetry in Heqb; try rewrite eqb_eq in Heqb.
    + assert (p < update C (ST mem t) x (Closure x1 e3 C1)) as contra. 
      { rewrite Heqb. destruct H; split; eauto. }
      apply NBOUND in contra. inversion contra.
    + simpl in IHEVAL2. destruct IHEVAL2 as [? [RR ?]].
      apply RR. unfold not. intros.
      assert (p < update C (ST mem t) x (Closure x1 e3 C1)) as contra.
      apply relax_p_bound with (t1 := t); try assumption.
      apply update_lt.
      apply NBOUND in contra. inversion contra.
    + apply relax_ctx_bound with (t1 := t).
      simpl in IHEVAL2. destruct IHEVAL2 as [? [? ?]]; eauto.
      apply update_lt.
    + destruct IHEVAL2 as [? [? RR]]. 
      specialize (RR p). remember (mem p) as access eqn:ACCESS.
      destruct access; eauto. destruct e4.
      apply relax_ctx_bound with (t1 := t). apply RR. split; try assumption.
      pose proof (p_bound_or_not p t) as CASES.
      destruct CASES as [? | contra]. apply H2.
      specialize (H1 p contra). rewrite H1 in ACCESS. inversion ACCESS. apply H.
  - apply IHEVAL2. apply IHEVAL1. eauto.
  - destruct st. simpl in *. destruct BOUND as [? [? ?]].
    repeat split; eauto.
  - destruct st. simpl in *. destruct BOUND as [? [? ?]].
    repeat split; eauto.
    eapply time_bound_ctx_M.
    symmetry. exact ACCESS. eauto.
  - specialize (IHEVAL1 BOUND).
    destruct v. 
    destruct st. destruct st_m.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in IHEVAL1. destruct IHEVAL1 as [HH1 [HH2 HH3]].
    assert (time_bound C_m (ST mem1 t1)).
    {
      apply IHEVAL2.
      simpl; rewrite plugin_ctx_bound. split. split.
      apply relax_ctx_bound with (t1 := t0); try assumption. 
      lebt t. simpl. split; eauto; try apply update_lt.
      split; intros; unfold update_m; remember (eqb p t) as b;
      destruct b; symmetry in Heqb; try rewrite eqb_eq in Heqb; try rewrite eqb_neq in Heqb.
      - subst. assert False as contra. apply NBOUND. apply update_lt. inversion contra.
      - apply HH2. unfold not. intros. 
        assert False as contra. apply NBOUND.
        apply relax_p_bound with (t1 := t); try assumption. apply update_lt. eauto.
      - subst. apply relax_ctx_bound with (t1 := t); try assumption. apply update_lt.
      - specialize (HH3 p). remember (mem p) as access eqn:ACCESS.
        destruct access; eauto. destruct e1.
        apply relax_ctx_bound with (t1 := t); try assumption. apply HH3.
        pose proof (p_bound_or_not p t) as CASES.
        destruct CASES as [? | contra]; eauto.
        specialize (HH2 p contra). rewrite HH2 in ACCESS. inversion ACCESS. apply update_lt.
    }
    destruct H as [HH1' [HH2' HH3']].
    repeat split; try assumption.
    lebt ((update C (ST mem t) x (Closure x0 e0 C0))).
    refl_bool. rewrite eqb_eq in contra. rewrite contra in time_inc2. clear contra.
    assert (t1 = (update C (ST mem t1) x (Closure x0 e0 C0))).
    apply leb_sym; try assumption. apply update_lt.
    assert (eqb t1 (update C (ST mem t1) x (Closure x0 e0 C0)) = false) as contra.
    apply update_lt.
    rewrite eqb_neq in contra. apply contra; eauto.
  - specialize (IHEVAL1 BOUND).
    destruct st. destruct st'. destruct st''.
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in IHEVAL1. destruct IHEVAL1 as [HH1 [HH2 HH3]].
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (time_bound C'' (ST mem1 t1)).
    {
      apply IHEVAL2.
      simpl; rewrite plugin_ctx_bound. split. split.
      apply relax_ctx_bound with (t1 := t); try assumption. 
      simpl. split; eauto.
      split; intros; unfold update_m; remember (eqb p t) as b;
      destruct b; symmetry in Heqb; try rewrite eqb_eq in Heqb; try rewrite eqb_neq in Heqb.
      - apply HH2; eauto.
      - apply HH2; eauto.
      - apply HH3; eauto.
      - apply HH3; eauto.
    }
    destruct H as [HH1' [HH2' HH3']].
    repeat split; try assumption.
    apply relax_ctx_bound with (t1 := t0); eauto.
Qed.

Lemma plugin_trans_ctx :
  forall `{Conc.Time CT} `{Abs.Time AT} Cout Cin α,
    trans_ctx α (Cout[|Cin|]) = (trans_ctx α Cout [|trans_ctx α Cin|]).
Proof.
  induction Cout; intros; simpl; 
  try rewrite IHCout; try rewrite IHCout1; try rewrite IHCout2;
  eauto.
Qed.

Lemma bound_trans_ctx_eq :
  forall `{Conc.Time CT} `{Abs.Time AT} C t α α',
         dy_ctx_bound C t ->
         eq_bound_α t α α' ->
         trans_ctx α C = trans_ctx α' C.
Proof.
  intros. 
  rename H into O1. rename H0 into T1.
  rename H1 into O2. rename H2 into T2.
  induction C; simpl; try rewrite IHC; 
  try rewrite IHC1; try rewrite IHC2; simpl in *; eauto;
  destruct H3; eauto; inversion H.
  unfold eq_bound_α in H0. rewrite H4; eauto.
  unfold eq_bound_α in H0. rewrite H4; eauto.
Qed.

(* Set Printing Implicit. *)

Lemma sound_eval :
  forall `{Conc.Time CT} `{Abs.Time AT} C st e v' st'
         (EVAL : EvalR C st e v' st')
         (BOUND : time_bound C st)
         abs_C abs_st α
         (SOUND : sound α C st abs_C abs_st),
    exists abs_C' abs_st' α',
      match st with
      | ST _ t =>
        eq_bound_α t α α' /\
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
  intros. rename H into O1. rename H0 into T1. rename H1 into O2. rename H2 into T2.
  revert abs_C abs_st α SOUND. induction EVAL; intros; subst.
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
                             (ST (t !-> arg; mem) (update C (ST mem t) x arg))
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
             (ST (t !-> Closure x0 e0 C0; mem)
                (update C (ST mem t) x (Closure x0 e0 C0)))) as B2.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND'. destruct BOUND' as [BB1' [BB2' BB3']].
             simpl in BOUND''. destruct BOUND'' as [BB1'' [BB2'' BB3'']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. lebt t.
      simpl. split; eauto. split. apply update_lt. apply update_lt. split.
      (* not bound, then None *)
      intros. unfold update_m. remember (eqb p t) as b.
      destruct b. symmetry in Heqb. rewrite eqb_eq in Heqb.
      rewrite Heqb in NBOUND. simpl in NBOUND.
      assert False as contra. apply NBOUND. apply update_lt. inversion contra.
      apply BB2''. unfold not. intros [LE NEQ].
      apply NBOUND. split. lebt t.
      refl_bool. rewrite eqb_eq in *.
      assert (t = p) as RR. apply leb_sym; try assumption. rewrite contra. apply update_lt.
      rewrite eqb_neq in NEQ. apply NEQ; eauto.
      (* bound, then access is bound *)
      intros. unfold update_m. remember (eqb p t) as b.
      destruct b. symmetry in Heqb. rewrite eqb_eq in Heqb.
      rewrite Heqb in BOUND. simpl in BOUND. destruct BOUND.
      apply relax_ctx_bound with (t1 := t); eauto.
      pose proof (p_bound_or_not p t) as CASES.
      remember (mem p) as access eqn:ACCESS.
      destruct CASES; destruct access; try destruct e4; eauto;
      try specialize (BB2'' p H); try specialize (BB3'' p H);
      try rewrite <- ACCESS in BB2''; try rewrite <- ACCESS in BB3'';
      try apply relax_ctx_bound with (t1 := t); try apply update_lt. eauto. inversion BB2''. }
    specialize (BOUND''' B2).
    specialize (IHEVAL1 BOUND). specialize (IHEVAL2 B1). specialize (IHEVAL3 B2). 
    specialize (IHEVAL1 abs_C abs_st α SOUND).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' SOUND']]]].
    assert (sound α' C (ST mem1 t1) abs_C abs_st').
    { destruct abs_st'. simpl. simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?].
      repeat split; eauto. destruct abs_st. simpl in SOUND. destruct SOUND as [? [? ?]].
      rewrite <- H4. symmetry. eapply bound_trans_ctx_eq. simpl in BOUND. destruct BOUND.
      eauto. eauto. }
    specialize (IHEVAL2 abs_C abs_st' α' H). clear H.
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α'' [EQ'' SOUND'']]]]. destruct abs_st'' as [mem'' t''].
    remember (fun t' => if eqb t' (update C (ST mem t) x (Closure x0 e0 C0))
                        then Abs.update abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'') 
                        else α'' t') as α'''.
    assert (eq_bound_α t α'' α''') as EQ'''.
    { red. intros. rewrite Heqα'''. 
      assert (eqb t' (update C (ST mem t) x (Closure x0 e0 C0)) = false) as RR.
      refl_bool. rewrite eqb_eq in contra.
      assert (leb t t' = true). rewrite contra. apply update_lt. 
      assert (t = t') as RR. apply leb_sym; eauto. rewrite <- RR in contra.
      clear RR.
      assert (eqb t (update C (ST mem t) x (Closure x0 e0 C0)) <> true).
      refl_bool. apply update_lt. apply H0. rewrite <- contra. apply eqb_refl.
      rewrite RR. eauto. }
    assert (sound α''' (C_lam [|dy_c_lam x t ([||])|])
            (ST (t !-> Closure x0 e0 C0; mem) 
                (update C (ST mem t) x (Closure x0 e0 C0)))
            (abs_C'[| dy_c_lam x (α'' t) ([||]) |])
            (Abs.ST ((α'' t) !#-> Closure x0 e0 abs_C''; mem'') 
                    (Abs.update abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'')))).
    { simpl. repeat split.
      - rewrite Heqα'''. rewrite eqb_refl. eauto.
      - rewrite plugin_trans_ctx; simpl. rewrite Heqα'''.
        rewrite eqb_update. rewrite <- Heqα'''.
        assert (trans_ctx α''' C_lam = abs_C'). rewrite Heqα'''.
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?]. rewrite <- H0.
        apply bound_trans_ctx_eq with (t := t1). apply BOUND'.
        red. intros. assert (eqb t' (update C (ST mem t) x (Closure x0 e0 C0)) = false).
        refl_bool. rewrite eqb_eq in contra.
        assert (leb t' t = true). lebt t1.
        assert (t = t') as RR. apply leb_sym; try assumption. rewrite contra. apply update_lt.
        assert (t < t') as contra'. rewrite contra. apply update_lt.
        destruct contra' as [? contra']. rewrite RR in contra'. rewrite eqb_refl in contra'. inversion contra'.
        rewrite H3. symmetry. apply EQ''. assumption. rewrite H. eauto.
      - intros. simpl in SOUND''. destruct SOUND'' as [[? [? ?]] ?].
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?].
        unfold update_m. unfold Abs.update_m.
        remember (eqb p t) as b.
        destruct b. symmetry in Heqb. rewrite eqb_eq in Heqb.
        assert (eqb (α''' p) (α'' t) = true) as RR.
        rewrite Heqα'''. rewrite Heqb. rewrite eqb_update. apply eqb_refl.
        rewrite RR. clear RR. simpl. left. rewrite <- H0.
        assert (trans_ctx α'' C0 = trans_ctx α''' C0) as RR.
        apply bound_trans_ctx_eq with (t := t); eauto. apply BOUND''. rewrite RR; eauto.
        pose proof (p_bound_or_not p t) as CASES.
        destruct BOUND'' as [B1'' [B2'' B3'']].
        destruct CASES as [L | R]; 
        try (specialize (B2'' p R); rewrite B2''; eauto; fail).
        remember (mem p) as access eqn: ACCESS.
        destruct access; eauto; destruct e4; simpl.
        specialize (H1 p L) as HINT. rewrite <- ACCESS in HINT.
        assert (α''' p = α'' p) as RR. 
        { symmetry. apply EQ'''. apply L. } rewrite RR; clear RR.
        assert (trans_ctx α'' C2 = trans_ctx α''' C2) as RR.
        { apply bound_trans_ctx_eq with (t := t); eauto.
          specialize (B3'' p L). rewrite <- ACCESS in B3''. exact B3''. } rewrite <- RR; clear RR.
        remember (α'' t) as p'.
        remember (eqb (α'' p) p') as b.
        destruct b. 
        simpl. right. symmetry in Heqb0. rewrite eqb_eq in Heqb0.
        rewrite <- Heqb0. apply HINT; eauto. apply HINT; eauto.
    }
    specialize (IHEVAL3 (abs_C' [|dy_c_lam x (α'' t) ([||])|])
                (Abs.ST
                  (α'' t !#-> Closure x0 e0 abs_C''; mem'')
                  (Abs.update abs_C (Abs.ST mem'' t'') x
                  (Closure x0 e0 abs_C''))) α''' H).
    destruct IHEVAL3 as [abs_C''' [abs_st''' [α'''' [EQ'''' SOUND''']]]].
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND'' as [SOUND'' EVAL''].
    destruct SOUND''' as [SOUND''' EVAL'''].
    exists abs_C'''. exists abs_st'''. exists α''''. repeat split; eauto.
    red. intros. 
    assert (α t' = α' t') as RR. apply EQ'. eauto. rewrite RR; clear RR.
    assert (α' t' = α'' t') as RR. apply EQ''. lebt t0. rewrite RR; clear RR.
    assert (α'' t' = α''' t') as RR. apply EQ'''. lebt t1. lebt t0. rewrite RR; clear RR.
    apply EQ''''. lebt t. lebt t1. lebt t0. 
    eapply Abstract.Eval_app. exact EVAL'. exact EVAL''.
    destruct abs_st'. simpl in SOUND'. destruct SOUND' as [? [RR ?]].
    rewrite RR. simpl in SOUND''. destruct SOUND'' as [? [RR' ?]].
    rewrite RR'. rewrite <- H2. rewrite <- H2 in EVAL'''. exact EVAL'''.
  - pose proof (time_bound_e C st m (MVal C_m) st_m EVAL1) as BOUND'.
    pose proof (time_bound_e C_m st_m e (EVal v) st_v EVAL2) as BOUND''.
    specialize (BOUND' BOUND). simpl in BOUND'. 
    specialize (BOUND'' BOUND'). simpl in BOUND''. destruct v.
    destruct st. destruct st_m. destruct st_v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    specialize (IHEVAL1 BOUND abs_C abs_st α SOUND).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' SOUND']]]].
    destruct SOUND' as [SOUND' EVAL']. 
    specialize (IHEVAL2 BOUND' abs_C' abs_st' α' SOUND').
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α'' [EQ'' SOUND'']]]].
    destruct SOUND'' as [SOUND'' EVAL''].
    exists abs_C''. exists abs_st''. exists α''. repeat split; eauto.
    unfold eq_bound_α in *. intros.
    assert (α'' t' = α' t'). symmetry. apply EQ''. lebt t.
    rewrite H. apply EQ'. eauto.
    eapply Abstract.Eval_link. eauto.
    destruct abs_st'. simpl in SOUND'. destruct SOUND' as [? [RR ?]].
    rewrite RR. eauto.
  - exists ([||]). exists abs_st. exists α. destruct st.
    repeat split; eauto. unfold eq_bound_α; intros; eauto.
    destruct abs_st. simpl in SOUND. destruct SOUND as [? [RR ?]].
    simpl. repeat split; eauto.
  - exists (trans_ctx α C_M). exists abs_st. exists α. destruct st.
    destruct abs_st. destruct SOUND as [? [RR ?]].
    repeat split; eauto. rewrite <- RR.
    eapply Abstract.Eval_var_m. erewrite trans_ctx_ctx_M; eauto.
  - pose proof (time_bound_e C st e (EVal v) (ST mem t) EVAL1) as BOUND'.
    pose proof (time_bound_e (C [|dy_c_lete x t ([||])|]) 
                             (ST (t !-> v; mem)
                                 (update C (ST mem t) x v)) m
                             (MVal C_m) st_m EVAL2) as BOUND''.
    specialize (BOUND' BOUND). simpl in BOUND'.
    destruct st. destruct st_m. destruct v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (time_bound (C [|dy_c_lete x t ([||])|])
            (ST (t !-> (Closure x0 e0 C0); mem)
               (update C (ST mem t) x (Closure x0 e0 C0)))) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND'. destruct BOUND' as [BB1' [BB2' BB3']].
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. lebt t. simpl. split; eauto. apply update_lt. split.
      (* not bound, then None *)
      intros. unfold update_m. remember (eqb p t) as b.
      destruct b. symmetry in Heqb. rewrite eqb_eq in Heqb. 
      assert False as contra. apply NBOUND. rewrite Heqb. apply update_lt. inversion contra.
      apply BB2'. unfold not. intros [LE NEQ].
      apply NBOUND. split. lebt t.
      refl_bool. unfold "<>". rewrite eqb_eq in *.
      assert (t = p) as RR. apply leb_sym; try assumption. rewrite contra. apply update_lt.
      rewrite eqb_neq in NEQ. apply NEQ; eauto.
      (* bound, then access is bound *)
      intros. unfold update_m. remember (eqb p t) as b.
      destruct b. symmetry in Heqb. rewrite eqb_eq in Heqb.
      rewrite Heqb in BOUND. simpl in BOUND. destruct BOUND.
      apply relax_ctx_bound with (t1 := t); eauto.
      pose proof (p_bound_or_not p t) as CASES.
      remember (mem p) as access eqn:ACCESS.
      destruct CASES; destruct access; try destruct e1; eauto;
      try specialize (BB2' p H); try specialize (BB3' p H);
      try rewrite <- ACCESS in BB2'; try rewrite <- ACCESS in BB3';
      try apply relax_ctx_bound with (t1 := t); try apply update_lt; eauto. inversion BB2'. }
    specialize (BOUND'' B1).
    specialize (IHEVAL1 BOUND). specialize (IHEVAL2 B1).
    specialize (IHEVAL1 abs_C abs_st α SOUND).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' SOUND']]]].
    remember (fun t' => if eqb t' (update C (ST mem t) x (Closure x0 e0 C0))
                        then Abs.update abs_C abs_st'
                                        x (Closure x0 e0 abs_C') 
                        else α' t') as α''.
    destruct abs_st as [mem' t']. destruct abs_st' as [mem'' t''].
    assert (eq_bound_α t α' α'') as EQ''.
    { red. intros. rewrite Heqα''. 
      assert (eqb t'0 (update C (ST mem t) x (Closure x0 e0 C0)) = false).
      refl_bool. rewrite eqb_eq in contra.
      assert (leb t t'0 = true). rewrite contra. apply update_lt. 
      assert (t = t'0) as RR. apply leb_sym; eauto. rewrite <- RR in contra.
      clear RR.
      assert (eqb t (update C (ST mem t) x (Closure x0 e0 C0)) <> true).
      refl_bool. apply update_lt. apply H0. rewrite <- contra. apply eqb_refl.
      rewrite H. eauto. }
    assert (sound α'' (C [|dy_c_lete x t ([||])|])
            (ST (t !-> Closure x0 e0 C0; mem) 
                (update C (ST mem t) x (Closure x0 e0 C0)))
            (abs_C [| dy_c_lete x (α' t) ([||]) |])
            (Abs.ST ((α' t) !#-> Closure x0 e0 abs_C'; mem'') 
                    (Abs.update abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C')))).
    { simpl. repeat split.
      - rewrite Heqα''. simpl. rewrite eqb_refl. eauto.
      - rewrite Heqα''. simpl. rewrite plugin_trans_ctx; simpl.
        assert (eqb t (update C (ST mem t) x (Closure x0 e0 C0)) = false). apply update_lt.
        rewrite H.
        assert (trans_ctx α'' C = abs_C). 
        simpl in SOUND. destruct SOUND as [? [RR ?]]. rewrite <- RR. symmetry.
        apply bound_trans_ctx_eq with (t := t0). destruct BOUND. eauto.
        red. intros. rewrite Heqα''. assert (eqb t'0 (update C (ST mem t) x (Closure x0 e0 C0)) = false).
        refl_bool. rewrite eqb_eq in contra.
        assert (leb t'0 t = true). lebt t0.
        assert (t = t'0) as RR'. apply leb_sym; try assumption. rewrite contra. apply update_lt.
        assert (t < t'0) as contra'. rewrite contra. apply update_lt.
        destruct contra' as [? contra']. rewrite RR' in contra'. rewrite eqb_refl in contra'. inversion contra'.
        rewrite H2. apply EQ'. eauto. rewrite <- Heqα''. rewrite H0. eauto.
      - intros. simpl in SOUND. destruct SOUND as [? [? ?]].
                simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?].
        unfold update_m. unfold Abs.update_m.
        remember (eqb p t) as b.
        destruct b. symmetry in Heqb. rewrite eqb_eq in Heqb.
        assert (α' t = α'' p). rewrite Heqb. apply EQ''. apply leb_refl.
        rewrite H6. rewrite eqb_refl. left.
        assert (abs_C' = trans_ctx α'' C0).
        rewrite <- H3. eapply bound_trans_ctx_eq. destruct BOUND'. eauto. eauto.
        rewrite H7. eauto. 
        pose proof (p_bound_or_not p t) as CASES.
        destruct BOUND' as [B1' [B2' B3']].
        destruct CASES as [L | R]; 
        try (specialize (B2' p R); rewrite B2'; eauto; fail).
        remember (mem p) as access eqn: ACCESS.
        destruct access; eauto; destruct e1; simpl.
        specialize (H4 p L) as HINT. rewrite <- ACCESS in HINT.
        assert (α'' p = α' p) as RR. 
        { symmetry. apply EQ''. apply L. } rewrite RR; clear RR.
        assert (trans_ctx α' C1 = trans_ctx α'' C1) as RR.
        { apply bound_trans_ctx_eq with (t := t); eauto.
          specialize (B3' p L). rewrite <- ACCESS in B3'. eauto. } rewrite <- RR; clear RR.
        remember (α' t) as p'.
        remember (eqb (α' p) p') as b.
        destruct b. 
        simpl. right. symmetry in Heqb0. rewrite eqb_eq in Heqb0.
        rewrite <- Heqb0. apply HINT; eauto. apply HINT; eauto.
    }
    specialize (IHEVAL2 (abs_C [|dy_c_lete x (α' t) ([||])|])
                (Abs.ST
                  (α' t !#-> Closure x0 e0 abs_C'; mem'')
                  (Abs.update abs_C (Abs.ST mem'' t'') x
                  (Closure x0 e0 abs_C'))) α'' H). clear H.
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α''' [EQ''' SOUND''']]]].
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND''' as [SOUND''' EVAL'''].
    exists (dy_c_lete x (α''' t) abs_C''). exists abs_st''. exists α'''. repeat split.
    red. intros. 
    assert (α t'0 = α' t'0) as RR. apply EQ'. eauto. rewrite RR; clear RR.
    assert (α' t'0 = α'' t'0) as RR. apply EQ''. lebt t0. rewrite RR; clear RR.
    apply EQ'''. lebt t. lebt t0.
    destruct abs_st''. simpl. repeat split; try apply SOUND'''.
    assert (trans_ctx α''' C_m = abs_C'') as RR.
    apply SOUND'''. rewrite RR. eauto.
    assert (α''' t = t'') as RR.
    { destruct SOUND' as [R ?]. rewrite <- R.
      assert (α' t = α'' t) as RR. apply EQ''. apply leb_refl. rewrite RR; clear RR.
      symmetry. apply EQ'''. apply update_lt. }
    eapply Abstract.Eval_lete; rewrite RR.
    exact EVAL'. 
    destruct SOUND' as [RR' [RR'' ?]]. rewrite RR' in EVAL'''.
    rewrite RR''. exact EVAL'''.
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
    specialize (IHEVAL1 abs_C abs_st α SOUND).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' SOUND']]]].
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
    assert (eq_bound_α t α' α') as EQ''.
    { red. intros; eauto. }
    specialize (IHEVAL2 (abs_C [|dy_c_letm M abs_C' ([||])|])
                        abs_st' α' H).
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α'' [EQ''' SOUND''']]]].
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND''' as [SOUND''' EVAL'''].
    destruct abs_st'. destruct SOUND' as [? [RR ?]].
    destruct abs_st''. destruct SOUND''' as [? [RR' ?]].
    assert (trans_ctx α' C' = trans_ctx α'' C') as RR''. 
    { apply bound_trans_ctx_eq with (t := t0). apply BOUND'. assumption. }
    exists (dy_c_letm M abs_C' abs_C''). exists (Abs.ST mem3 t3). exists α''. repeat split; eauto.
    red. intros. 
    assert (α t' = α' t') as RR'''. apply EQ'. eauto. rewrite RR'''.
    apply EQ'''. lebt t.
    simpl. rewrite <- RR''. rewrite RR'. rewrite RR. eauto.
    eapply Abstract.Eval_letm.
    rewrite <- RR in *. rewrite <- RR' in *. rewrite RR'' in *.
    exact EVAL'.
    rewrite <- RR in *. rewrite RR'' in *. exact EVAL'''.
Qed.
