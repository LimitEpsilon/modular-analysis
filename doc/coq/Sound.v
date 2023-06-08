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
      | Some (Closure _ _ C') => dy_ctx_bound C' t
      | _ => True
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
        | Some (Closure x e Cv) =>
          let l := abs_mem (map α p) in
          In (Abstract.Closure x e (trans_ctx α Cv)) l
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

Lemma trans_ctx_ctx_M :
  forall C α abs_C M C_M
        (ACCESS : ctx_M C M = Some C_M)
        (TRANS : trans_ctx α C = abs_C),
    Abstract.ctx_M abs_C M = Some (trans_ctx α C_M).
Proof.
  assert (forall C α M,
    match Abstract.ctx_M (trans_ctx α C) M with
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
    remember (Abstract.ctx_M (trans_ctx α C2) M0) as ctx';
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
    remember (Abstract.ctx_M (trans_ctx α C2) M0) as ctx1.
    destruct ctx1; try (inversion ACCESS; fail).
    + specialize (H C2 α M0).
      rewrite <- Heqctx1 in H.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion H; inversion ACCESS; subst.
      rewrite Heqctx1. apply IHC2; eauto.
    + specialize (H C2 α M0).
      rewrite <- Heqctx1 in H.
      remember (ctx_M C2 M0) as ctx2; destruct ctx2;
      inversion H; destruct (eq_mid M0 M);
      inversion ACCESS; subst; eauto.
Qed.

Lemma time_increase_e :
  forall C st e e' st'
         (EVAL : EvalR C st e e' st'),
    match st with
    | ST _ t =>
      match st' with
      | ST _ t' => t <= t'
      end
    end.
Proof.
  intros. 
  induction EVAL;
  intros; 
  destruct st; try destruct st'; try destruct st''; try destruct st_v; 
  try destruct st_m; try destruct st_lam;
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
         (EVAL : EvalR C st e e' st')
         (BOUND : time_bound C st),
    match e' with
    | EVal (Closure _ _ C') => time_bound C' st'
    | MVal C' => time_bound C' st'
    end.
Proof.
  intros. induction EVAL; intros; simpl; eauto.
  - destruct v. unfold time_bound in *.
    destruct st. destruct BOUND as [? [? RR]].
    specialize (RR (addr_x C x)) as RR'.
    assert (p_bound (addr_x C x) t0). apply time_bound_addr. eauto.
    apply RR' in H1. inversion STATE; subst. 
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
    assert (p_bound (t :: dy_level C_lam) (update_t C (ST mem t) x (Closure x1 e3 C1))).
    {
      simpl in IHEVAL1. destruct IHEVAL1 as [? [? ?]].
      simpl. split; unfold update_t; eauto.
      apply relax_p_bound with (t1 := t1).
      apply time_bound_level. eauto. nia.
    }
    apply IHEVAL3; simpl. split.
    rewrite plugin_ctx_bound. split.
    simpl in IHEVAL1. destruct IHEVAL1 as [? [? ?]].
    eapply relax_ctx_bound. eauto. nia.
    simpl. split; eauto.
    split; intros;
    unfold update_m; remember (eq_p p (t :: dy_level C_lam)) as b;
    destruct b; symmetry in Heqb; try rewrite eq_p_eq in Heqb.
    + assert (p_bound p (S t)) as contra. { rewrite Heqb. eauto. }
      apply NBOUND in contra. inversion contra.
    + simpl in IHEVAL2. destruct IHEVAL2 as [? [RR ?]].
      apply RR. unfold not. intros. 
      assert (p_bound p (S t)) as contra.
      apply relax_p_bound with (t1 := t); eauto. 
      apply NBOUND in contra. inversion contra.
    + apply relax_ctx_bound with (t1 := t); eauto.
      simpl in IHEVAL2. destruct IHEVAL2 as [? [? ?]]; eauto.
    + destruct IHEVAL2 as [? [? RR]]. 
      specialize (RR p). remember (mem p) as access eqn:ACCESS.
      destruct access; eauto. destruct e4.
      apply relax_ctx_bound with (t1 := t); eauto. apply RR.
      pose proof (p_bound_or_not p t) as CASES.
      destruct CASES as [? | contra]; eauto.
      specialize (H1 p contra). rewrite H1 in ACCESS. inversion ACCESS.
  - apply IHEVAL2. apply IHEVAL1. eauto.
  - destruct st. simpl in *. destruct BOUND as [? [? ?]].
    repeat split; eauto. eapply time_bound_ctx_M.
    symmetry. exact ACCESS. eauto.
  - specialize (IHEVAL1 BOUND).
    destruct v. 
    destruct st. destruct st_m.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (p_bound (t :: dy_level C) (update_t C (ST mem t) x (Closure x0 e0 C0))).
    {
      simpl in BOUND. destruct BOUND as [? [? ?]].
      simpl. split; unfold update_t; eauto.
      apply relax_p_bound with (t1 := t0).
      apply time_bound_level. eauto. nia.
    }
    simpl in BOUND. destruct BOUND as [B1 [B2 B3]].
    simpl in IHEVAL1. destruct IHEVAL1 as [HH1 [HH2 HH3]].
    apply IHEVAL2. simpl; split.
    rewrite plugin_ctx_bound; split.
    apply relax_ctx_bound with (t1 := t0); eauto. simpl; split; eauto.
    split; intros;
    unfold update_m; remember (eq_p p (t :: dy_level C)) as b;
    destruct b; symmetry in Heqb; try rewrite eq_p_eq in Heqb.
    + assert (p_bound p (S t)) as contra. { rewrite Heqb. eauto. }
      apply NBOUND in contra. inversion contra.
    + apply HH2. unfold not. intros. 
      assert (p_bound p (S t)) as contra.
      apply relax_p_bound with (t1 := t); eauto. 
      apply NBOUND in contra. inversion contra.
    + apply relax_ctx_bound with (t1 := t); eauto.
    + specialize (HH3 p). remember (mem p) as access eqn:ACCESS.
      destruct access; eauto. destruct e1.
      apply relax_ctx_bound with (t1 := t); eauto. apply HH3.
      pose proof (p_bound_or_not p t) as CASES.
      destruct CASES as [? | contra]; eauto.
      specialize (HH2 p contra). rewrite HH2 in ACCESS. inversion ACCESS.
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

(* Set Printing Implicit. *)

Lemma sound_eval :
  forall C st e v' st'
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
          Abstract.EvalR 
            abs_C abs_st e 
            (Abstract.EVal (Abstract.Closure x' e' (trans_ctx α' C')))
            abs_st'
        | MVal C' =>
          sound α' C' st' abs_C' abs_st' /\
          Abstract.EvalR 
            abs_C abs_st e 
            (Abstract.MVal (trans_ctx α' C'))
            abs_st' 
        end
      end.
Proof.
  intros. revert abs_C abs_st α SOUND. induction EVAL; intros; subst.
  - unfold sound in SOUND. destruct abs_st as [abs_mem abs_t].
    destruct SOUND as [? [? ?]].
    specialize (H1 (addr_x C x)) as HINT. rewrite <- ACCESS in HINT.
    destruct v as [v pf C'].
    exists (trans_ctx α C'). exists (Abstract.ST abs_mem abs_t). exists α.
    repeat split; try red; intros; eauto. apply H1. eauto.
    eapply Abstract.Eval_var_e; eauto.
    rewrite <- H0. rewrite trans_ctx_addr.
    destruct (addr_x C x). specialize (ADDR eq_refl). inversion ADDR.
    simpl; unfold not; intros contra; inversion contra.
    rewrite <- H0. rewrite trans_ctx_addr.
    apply HINT. simpl in BOUND. destruct BOUND. apply time_bound_addr. eauto.
  - exists abs_C. exists abs_st. exists α. repeat split; eauto using Abstract.EvalR.
    destruct st; simpl; repeat split; try red; intros; eauto.
    destruct abs_st. simpl in SOUND. destruct SOUND as [? [? ?]].
    rewrite H0. eauto using Abstract.EvalR.
  - pose proof (time_bound_e C st e1 (EVal (Closure x e C_lam)) st_lam EVAL1) as BOUND'.
    pose proof (time_bound_e C st_lam e2 (EVal arg) (ST mem t) EVAL2) as BOUND''.
    pose proof (time_bound_e (C_lam [|dy_c_lam x t ([||])|])
                             (ST (t :: dy_level C_lam !-> arg; mem) (update_t C (ST mem t) x arg))
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
             (ST (t :: dy_level C_lam !-> Closure x0 e0 C0; mem)
                (update_t C (ST mem t) x (Closure x0 e0 C0)))) as B2.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND'. destruct BOUND' as [BB1' [BB2' BB3']].
             simpl in BOUND''. destruct BOUND'' as [BB1'' [BB2'' BB3'']].
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
      apply BB2''. unfold not. intros contra.
      assert (p_bound p (S t)). apply relax_p_bound with (t1 := t); eauto.
      apply NBOUND in H. inversion H.
      (* bound, then access is bound *)
      intros. unfold update_m. remember (eq_p p (t :: dy_level C_lam)) as b.
      destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
      rewrite Heqb in BOUND. simpl in BOUND. destruct BOUND.
      apply relax_ctx_bound with (t1 := t); eauto.
      pose proof (p_bound_or_not p t) as CASES.
      remember (mem p) as access eqn:ACCESS.
      destruct CASES; destruct access; try destruct e4; eauto;
      try specialize (BB2'' p H); try specialize (BB3'' p H);
      try rewrite <- ACCESS in BB2''; try rewrite <- ACCESS in BB3'';
      try apply relax_ctx_bound with (t1 := t); eauto. inversion BB2''. }
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
    remember (fun (t' : nat) => if t' =? S t 
                        then Abstract.update_t abs_C (Abstract.ST mem'' t'') 
                                                x (Abstract.Closure x0 e0 abs_C'') 
                        else α'' t') as α'''.
    assert (sound α''' (C_lam [|dy_c_lam x t ([||])|])
            (ST (t :: dy_level C_lam !-> Closure x0 e0 C0; mem) 
                (update_t C (ST mem t) x (Closure x0 e0 C0)))
            (abs_C'[#| Abstract.dy_c_lam x (α'' t) ([#||#]) |#])
            (Abstract.ST ((α'' t) :: Abstract.dy_level abs_C' !#-> Abstract.Closure x0 e0 abs_C''; mem'') 
                         (Abstract.update_t abs_C (Abstract.ST mem'' t'') x (Abstract.Closure x0 e0 abs_C'')))).
    { simpl. unfold update_t in *. repeat split.
      - rewrite Heqα'''. simpl. assert (t =? t = true). rewrite Nat.eqb_eq. eauto. rewrite H. eauto.
      - rewrite Heqα'''. simpl. rewrite plugin_trans_ctx; simpl.
        assert (t =? S t = false). rewrite Nat.eqb_neq. eauto. rewrite H.
        assert (trans_ctx α''' C_lam = abs_C'). rewrite Heqα'''.
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?]. rewrite <- H1.
        apply bound_trans_ctx_eq with (t := t1). simpl in BOUND'. destruct BOUND'. eauto.
        red. intros. assert (t' <> S t). nia. rewrite <- Nat.eqb_neq in H4. rewrite H4.
        symmetry. apply EQ''. eauto. 
        rewrite Heqα''' in H0. simpl in H0. rewrite H0. eauto.
      - intros. simpl in SOUND''. destruct SOUND'' as [[? [? ?]] ?].
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?].
        unfold update_m. unfold Abstract.update_m.
        remember (eq_p p (t :: dy_level C_lam)) as b.
        destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
        assert (map α''' p =  α'' t :: Abstract.dy_level abs_C').
        rewrite Heqα'''. rewrite Heqb. simpl. assert (RR : t =? S t = false). 
        apply Nat.eqb_neq. eauto. rewrite RR. clear RR. rewrite <- H4.
        assert (Abstract.dy_level (trans_ctx α' C_lam) = map α''' (dy_level C_lam)) as RR.
        apply level_trans_ctx_eq with (t := t1). red. intros.
        assert (t' =? S t = false). rewrite Nat.eqb_neq. nia.
        rewrite Heqα'''. rewrite H7. apply EQ''. eauto.
        simpl in BOUND'. destruct BOUND'. eauto.
        rewrite RR. rewrite Heqα'''. simpl. eauto.
        (* A bug? in Coq : have to write explicitly the implicit parameters *)
        assert (Abstract.eq_p (@map time Abstract.time α''' p) (@map nat bool α''' p) = true).
        rewrite Abstract.eq_p_eq. eauto. rewrite <- H7. rewrite H8. simpl. left.
        assert (abs_C'' = trans_ctx α''' C0).
        rewrite <- H0. eapply bound_trans_ctx_eq. simpl in BOUND''. destruct BOUND''. eauto.
        rewrite Heqα'''. red. intros. assert (t' =? S t = false). rewrite Nat.eqb_neq. nia.
        rewrite H9. eauto. rewrite H9. eauto.
        pose proof (p_bound_or_not p t) as CASES.
        simpl in BOUND''. destruct BOUND'' as [B1'' [B2'' B3'']].
        destruct CASES as [L | R]; 
        try (specialize (B2'' p R); rewrite B2''; eauto; fail).
        remember (mem p) as access eqn: ACCESS.
        destruct access; eauto; destruct e4; simpl.
        specialize (H1 p L) as HINT. rewrite <- ACCESS in HINT.
        assert (@map time Abstract.time α''' p = map α'' p) as RR. 
        { clear HINT. clear BOUND0. clear Heqb. clear ACCESS.
          induction p; simpl; eauto. simpl in L; destruct L.
          rewrite IHp; eauto. rewrite Heqα'''. 
          assert (a =? S t = false). rewrite Nat.eqb_neq. nia.
          rewrite H9. eauto. } rewrite RR; clear RR.
        assert (trans_ctx α''' C2 = trans_ctx α'' C2) as RR.
        { apply bound_trans_ctx_eq with (t := t).
          specialize (B3'' p L). rewrite <- ACCESS in B3''. eauto.
          rewrite Heqα'''. red. intros. assert (t' =? S t = false).
          rewrite Nat.eqb_neq. nia. rewrite H7. eauto. } rewrite RR; clear RR.
        remember (α'' t :: Abstract.dy_level abs_C') as p'.
        remember (Abstract.eq_p (map α'' p) p') as b.
        destruct b. 
        simpl. right. symmetry in Heqb0. rewrite Abstract.eq_p_eq in Heqb0.
        rewrite <- Heqb0. apply HINT. apply HINT.
    }
    assert (eq_bound_α t α'' α''') as EQ'''.
    { red. intros. rewrite Heqα'''. assert (t' =? S t = false). rewrite Nat.eqb_neq. nia.
      rewrite H0. eauto. }
    specialize (IHEVAL3 (abs_C' [#|Abstract.dy_c_lam x (α'' t) ([#||#])|#])
                (Abstract.ST
                  (α'' t :: Abstract.dy_level abs_C'
                      !#-> Abstract.Closure x0 e0 abs_C''; mem'')
                  (Abstract.update_t abs_C (Abstract.ST mem'' t'') x
                  (Abstract.Closure x0 e0 abs_C''))) α''' H).
    destruct IHEVAL3 as [abs_C''' [abs_st''' [α'''' [EQ'''' SOUND''']]]].
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND'' as [SOUND'' EVAL''].
    destruct SOUND''' as [SOUND''' EVAL'''].
    exists abs_C'''. exists abs_st'''. exists α''''. repeat split; eauto.
    red. intros. 
    assert (α t' = α' t') as RR. apply EQ'. eauto. rewrite RR; clear RR.
    assert (α' t' = α'' t') as RR. apply EQ''. nia. rewrite RR; clear RR.
    assert (α'' t' = α''' t') as RR. apply EQ'''. nia. rewrite RR; clear RR.
    apply EQ''''. unfold update_t. nia.
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
    assert (α'' t' = α' t'). symmetry. apply EQ''. nia.
    rewrite H. apply EQ'. eauto.
    eapply Abstract.Eval_link. eauto.
    destruct abs_st'. simpl in SOUND'. destruct SOUND' as [? [RR ?]].
    rewrite RR. eauto.
  - exists abs_C. exists abs_st. exists α. destruct st.
    repeat split; eauto. unfold eq_bound_α; intros; eauto.
    destruct abs_st. simpl in SOUND. destruct SOUND as [? [RR ?]].
    rewrite RR. eauto using Abstract.EvalR.
  - exists (trans_ctx α C_M). exists abs_st. exists α. destruct st.
    destruct abs_st. destruct SOUND as [? [RR ?]].
    repeat split; eauto. rewrite <- RR.
    eapply Abstract.Eval_var_m. erewrite trans_ctx_ctx_M; eauto.
  - pose proof (time_bound_e C st e (EVal v) (ST mem t) EVAL1) as BOUND'.
    pose proof (time_bound_e (C [|dy_c_lete x t ([||])|]) 
                             (ST (t :: dy_level C !-> v; mem)
                                 (update_t C (ST mem t) x v)) m
                             (MVal C_m) st_m EVAL2) as BOUND''.
    specialize (BOUND' BOUND). simpl in BOUND'.
    destruct st. destruct st_m. destruct v.
    apply time_increase_e in EVAL1 as time_inc1.
    apply time_increase_e in EVAL2 as time_inc2.
    assert (time_bound (C [|dy_c_lete x t ([||])|])
            (ST (t :: dy_level C !-> (Closure x0 e0 C0); mem)
               (update_t C (ST mem t) x (Closure x0 e0 C0)))) as B1.
    { simpl. simpl in BOUND. destruct BOUND as [BB1 [BB2 BB3]].
             simpl in BOUND'. destruct BOUND' as [BB1' [BB2' BB3']].
      unfold update_t in *.
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. eauto. simpl. split; eauto. split.
      (* not bound, then None *)
      intros. unfold update_m. remember (eq_p p (t :: dy_level C)) as b.
      destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
      rewrite Heqb in NBOUND. simpl in NBOUND.
      assert (t < S t /\ p_bound (dy_level C) (S t)) as contra.
      split; eauto. apply time_bound_level. apply relax_ctx_bound with (t1 := t0). eauto. eauto.
      apply NBOUND in contra. inversion contra.
      apply BB2'. unfold not. intros contra.
      assert (p_bound p (S t)). apply relax_p_bound with (t1 := t); eauto.
      apply NBOUND in H. inversion H.
      (* bound, then access is bound *)
      intros. unfold update_m. remember (eq_p p (t :: dy_level C)) as b.
      destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
      rewrite Heqb in BOUND. simpl in BOUND. destruct BOUND.
      apply relax_ctx_bound with (t1 := t); eauto.
      pose proof (p_bound_or_not p t) as CASES.
      remember (mem p) as access eqn:ACCESS.
      destruct CASES; destruct access; try destruct e1; eauto;
      try specialize (BB2' p H); try specialize (BB3' p H);
      try rewrite <- ACCESS in BB2'; try rewrite <- ACCESS in BB3';
      try apply relax_ctx_bound with (t1 := t); eauto. inversion BB2'. }
    specialize (BOUND'' B1).
    specialize (IHEVAL1 BOUND). specialize (IHEVAL2 B1).
    specialize (IHEVAL1 abs_C abs_st α SOUND).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' SOUND']]]].
    remember (fun (t' : nat) => if t' =? S t 
                        then Abstract.update_t abs_C abs_st'
                                                x (Abstract.Closure x0 e0 abs_C') 
                        else α' t') as α''.
    destruct abs_st as [mem' t']. destruct abs_st' as [mem'' t''].
    assert (sound α'' (C [|dy_c_lete x t ([||])|])
            (ST (t :: dy_level C !-> Closure x0 e0 C0; mem) 
                (update_t C (ST mem t) x (Closure x0 e0 C0)))
            (abs_C [#| Abstract.dy_c_lete x (α' t) ([#||#]) |#])
            (Abstract.ST ((α' t) :: Abstract.dy_level abs_C !#-> Abstract.Closure x0 e0 abs_C'; mem'') 
                         (Abstract.update_t abs_C (Abstract.ST mem'' t'') x (Abstract.Closure x0 e0 abs_C')))).
    { simpl. unfold update_t in *. repeat split.
      - rewrite Heqα''. simpl. assert (t =? t = true). rewrite Nat.eqb_eq. eauto. rewrite H. eauto.
      - rewrite Heqα''. simpl. rewrite plugin_trans_ctx; simpl.
        assert (t =? S t = false). rewrite Nat.eqb_neq. eauto. rewrite H.
        assert (trans_ctx α'' C = abs_C). 
        simpl in SOUND. destruct SOUND as [? [RR ?]]. rewrite <- RR.
        apply bound_trans_ctx_eq with (t := t0). destruct BOUND. eauto.
        red. intros. rewrite Heqα''. assert (t'0 <> S t) as RR'. nia. rewrite <- Nat.eqb_neq in RR'. rewrite RR'.
        symmetry. apply EQ'. eauto. 
        rewrite Heqα'' in H0. simpl in H0. rewrite H0. eauto.
      - intros. simpl in SOUND. destruct SOUND as [? [? ?]].
                simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?].
        unfold update_m. unfold Abstract.update_m.
        remember (eq_p p (t :: dy_level C)) as b.
        destruct b. symmetry in Heqb. rewrite eq_p_eq in Heqb.
        assert (map α'' p =  α' t :: Abstract.dy_level abs_C).
        rewrite Heqα''. rewrite Heqb. simpl. assert (RR : t =? S t = false). 
        apply Nat.eqb_neq. eauto. rewrite RR. clear RR. rewrite <- H0.
        assert (Abstract.dy_level (trans_ctx α C) = map α'' (dy_level C)) as RR.
        apply level_trans_ctx_eq with (t := t0). red. intros.
        rewrite Heqα''. assert (t'0 =? S t = false). rewrite Nat.eqb_neq. nia.
        rewrite H6. apply EQ'. eauto.
        simpl in BOUND. destruct BOUND. eauto.
        rewrite RR. rewrite Heqα''. simpl. eauto.
        (* A bug? in Coq : have to write explicitly the implicit parameters *)
        assert (Abstract.eq_p (@map time Abstract.time α'' p) (@map nat bool α'' p) = true).
        rewrite Abstract.eq_p_eq. eauto. rewrite <- H6. rewrite H7. simpl. left.
        assert (abs_C' = trans_ctx α'' C0).
        rewrite <- H3. eapply bound_trans_ctx_eq. simpl in BOUND'. destruct BOUND'. eauto.
        rewrite Heqα''. red. intros. assert (t'0 =? S t = false). rewrite Nat.eqb_neq. nia.
        rewrite H8. eauto. rewrite H8. eauto.
        pose proof (p_bound_or_not p t) as CASES.
        destruct BOUND' as [B1' [B2' B3']].
        destruct CASES as [L | R]; 
        try (specialize (B2' p R); rewrite B2'; eauto; fail).
        remember (mem p) as access eqn: ACCESS.
        destruct access; eauto; destruct e1; simpl.
        specialize (H4 p L) as HINT. rewrite <- ACCESS in HINT.
        assert (@map time Abstract.time α'' p = map α' p) as RR.
        { clear HINT. clear BOUND0. clear Heqb. clear ACCESS.
          induction p; simpl; eauto. simpl in L; destruct L.
          rewrite IHp; eauto. rewrite Heqα''. 
          assert (a =? S t = false). rewrite Nat.eqb_neq. nia.
          rewrite H8. eauto. } rewrite RR; clear RR.
        assert (trans_ctx α'' C1 = trans_ctx α' C1) as RR.
        { apply bound_trans_ctx_eq with (t := t).
          specialize (B3' p L). rewrite <- ACCESS in B3'. eauto.
          rewrite Heqα''. red. intros. assert (t'0 =? S t = false).
          rewrite Nat.eqb_neq. nia. rewrite H6. eauto. } rewrite RR; clear RR.
        remember (α' t :: Abstract.dy_level abs_C) as p'.
        remember (Abstract.eq_p (map α' p) p') as b.
        destruct b. 
        simpl. right. symmetry in Heqb0. rewrite Abstract.eq_p_eq in Heqb0.
        rewrite <- Heqb0. apply HINT. apply HINT.
    }
    assert (eq_bound_α t α' α'') as EQ''.
    { red. intros. rewrite Heqα''. assert (t'0 =? S t = false). rewrite Nat.eqb_neq. nia.
      rewrite H0. eauto. }
    specialize (IHEVAL2 (abs_C [#|Abstract.dy_c_lete x (α' t) ([#||#])|#])
                (Abstract.ST
                  (α' t :: Abstract.dy_level abs_C
                      !#-> Abstract.Closure x0 e0 abs_C'; mem'')
                  (Abstract.update_t abs_C (Abstract.ST mem'' t'') x
                  (Abstract.Closure x0 e0 abs_C'))) α'' H).
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α''' [EQ''' SOUND''']]]].
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND''' as [SOUND''' EVAL'''].
    exists abs_C''. exists abs_st''. exists α'''. repeat split; eauto.
    red. intros. 
    assert (α t'0 = α' t'0) as RR. apply EQ'. eauto. rewrite RR; clear RR.
    assert (α' t'0 = α'' t'0) as RR. apply EQ''. nia. rewrite RR; clear RR.
    apply EQ'''. unfold update_t. nia.
    eapply Abstract.Eval_lete; eauto.
    destruct SOUND' as [? [RR ?]]. rewrite RR. 
    destruct abs_st''. destruct SOUND''' as [? [RR' ?]]. rewrite RR' in *.
    rewrite <- H2. rewrite <- H2 in EVAL'''.
    rewrite <- H0 in *. exact EVAL'''.
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
      unfold update_t in *.
      split. rewrite plugin_ctx_bound. split.
      eapply relax_ctx_bound. eauto. eauto. simpl. split; eauto. split; eauto. }
    specialize (BOUND'' B1).
    specialize (IHEVAL1 BOUND). specialize (IHEVAL2 B1).
    specialize (IHEVAL1 abs_C abs_st α SOUND).
    destruct IHEVAL1 as [abs_C' [abs_st' [α' [EQ' SOUND']]]].
    assert (sound α' (C [|dy_c_letm M C' ([||])|]) (ST mem0 t0)
            (abs_C [#| Abstract.dy_c_letm M abs_C' ([#||#]) |#]) abs_st').
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
    specialize (IHEVAL2 (abs_C [#|Abstract.dy_c_letm M abs_C' ([#||#])|#])
                        abs_st' α' H).
    destruct IHEVAL2 as [abs_C'' [abs_st'' [α'' [EQ''' SOUND''']]]].
    destruct SOUND' as [SOUND' EVAL'].
    destruct SOUND''' as [SOUND''' EVAL'''].
    exists abs_C''. exists abs_st''. exists α''. repeat split; eauto.
    red. intros. 
    assert (α t' = α' t') as RR. apply EQ'. eauto. rewrite RR; clear RR.
    apply EQ'''. unfold update_t. nia.
    eapply Abstract.Eval_letm; eauto.
    destruct abs_st'. destruct SOUND' as [? [RR ?]].
    destruct abs_st''. destruct SOUND''' as [? [RR' ?]].
    rewrite RR in *. rewrite RR' in *. eauto.
Qed.
