From MODULAR Require Export Sound.

Generalizable Variables T TT.

Definition equiv_st `{OrderT T} `{OrderT TT} (f : T -> TT)
  (st : @state T) (st' : @state TT) :=
  match st, st' with
  | ST mem t, ST mem' t' =>
    eqb (f t) t' = true /\
    forall addr,
      match mem addr, mem' (f addr) with
      | Some (Closure x e C), Some (Closure x' e' C') =>
        x = x' /\ e = e' /\ trans_ctx f C = C'
      | None, None => True
      | _, _ => False
      end
  end.

Definition in_dom {T} (t : T) (C : @dy_ctx T) (st : @state T) :=
  match st with
  | ST mem t' => t = t' \/ In_ctx t C \/ mem t <> None
  end.

Definition inc_on_dom `{OT : OrderT T} `{OTT : OrderT TT} (f : T -> TT) (C : @dy_ctx T) (st : @state T) :=
  forall (t t' : T) (INt : in_dom t C st) (INt' : in_dom t' C st),
    t < t' -> f t < f t'.

Lemma equiv_eval : 
  forall `{time T} `{time TT} 
         (C : @dy_ctx T) st e v st_v
         (BOUND : time_bound C st)
         (EVAL : EvalR C st e v st_v)
         (C' : @dy_ctx TT) st' f
         (BOUND' : time_bound C' st')
         (INC : inc_on_dom f C st)
         (EQC : trans_ctx f C = C')
         (EQS : equiv_st f st st'),
    exists C_v' st_v' f',
      match st with
      | ST _ t =>
        eq_bound t f f' /\
        time_bound C_v' st_v' /\
        match v with
        | EVal (Closure x e_v C_v) =>
          inc_on_dom f' C_v st_v /\
          trans_ctx f' C_v = C_v' /\
          equiv_st f' st_v st_v' /\
          EvalR C' st' e (EVal (Closure x e_v C_v')) st_v'
        | MVal C_v =>
          inc_on_dom f' C_v st_v /\
          trans_ctx f' C_v = C_v' /\
          equiv_st f' st_v st_v' /\
          EvalR C' st' e (MVal C_v') st_v'
        end
      end.
Proof.
  intros.
  rename H into ET. rename H0 into OT. rename H1 into tT.
  rename H2 into ETT. rename H3 into OTT. rename H4 into tTT.
  revert C' st' f BOUND' INC EQC EQS.
  induction EVAL; intros; simpl in *.
  - rewrite <- STATE in EQS.
    simpl in EQS. destruct st' as [mem' t'].
    destruct EQS as [? EQS].
    specialize (EQS addr) as EQS'. rewrite <- ACCESS in EQS'.
    destruct v as [x' e_v C_v].
    destruct (mem' (f addr)) eqn:ACCESS'; try inversion EQS'.
    destruct e as [x'' e_v' C_v'].
    exists C_v'. exists (ST mem' t'). exists f.
    unfold inc_on_dom in INC. rewrite <- STATE in *.
    repeat split; try assumption.
    destruct EQS' as [? [? RR]]. rewrite <- RR.
    rewrite eqb_eq in H. rewrite <- H.
    assert (dy_ctx_bound C_v t).
    { destruct BOUND as [? [? ?]].
      pose proof (p_bound_or_not addr t) as cases.
      destruct cases as [CASE | CASE].
      specialize (H4 addr CASE). rewrite <- ACCESS in H4. eauto.
      specialize (H3 addr CASE). rewrite <- ACCESS in H3. inversion H3. }
    apply INC; eauto. apply INC; eauto.
    apply EQS'. 
    apply Eval_var_e with (addr := f addr) (mem := mem') (t := t'); eauto.
    rewrite <- EQC. rewrite trans_ctx_addr. rewrite <- ADDR. eauto.
    rewrite ACCESS'. destruct EQS' as [EQx [EQe EQc]]. subst; eauto.
  - exists C'. exists st'. exists f.
    unfold inc_on_dom in *. destruct st. repeat split; try assumption.
    apply INC; eauto. apply INC; eauto. eauto.
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
      refl_bool. intros contra. rewrite eqb_eq in *.
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
    specialize (IHEVAL1 C' st' f INC EQC EQS).
    destruct IHEVAL1 as [C_v' [st_v' [f' [BB [INClam [EQClam [EQstlam EVALlam]]]]]]].
    assert (trans_ctx f' C = C') as EQC'.
    { rewrite <- EQC. symmetry. 
      apply bound_trans_ctx_eq with (t := t0); eauto. apply BOUND. }
    specialize (IHEVAL2 C' st_v' f' INClam EQC' EQstlam). 
    destruct IHEVAL2 as [C_v'' [st_v'' [f'' [BB' [INCarg [EQCarg [EQstarg EVALarg]]]]]]].
    assert (trans_ctx f'' (C_lam [|dy_c_lam x t ([||])|]) = (C_v' [|dy_c_lam x (f'' t) ([||])|])) as EQC''.
    { rewrite plugin_trans_ctx. simpl.
      rewrite <- EQClam.
      assert (trans_ctx f' C_lam = trans_ctx f'' C_lam) as RR.
      apply bound_trans_ctx_eq with (t := t1); eauto. apply BOUND'.
      rewrite RR. eauto. }
    destruct st_v'' as [mem'' t''].
    remember (fun t' => if eqb t' (update C (ST mem t) x (Closure x0 e0 C0))
                        then update C' (ST mem'' t'') x (Closure x0 e0 C_v'') 
                        else f'' t') as f'''.
    assert (eq_bound t f'' f''') as BB''.
    { red. intros. rewrite Heqf'''. 
      assert (eqb t' (update C (ST mem t) x (Closure x0 e0 C0)) = false) as RR.
      refl_bool. intros contra. rewrite eqb_eq in contra.
      assert (leb t t' = true). rewrite contra. apply update_lt. 
      assert (t = t') as RR. apply leb_sym; eauto. rewrite <- RR in contra.
      clear RR.
      assert (eqb t (update C (ST mem t) x (Closure x0 e0 C0)) <> true).
      refl_bool. apply update_lt. apply H0. rewrite <- contra. apply eqb_refl.
      rewrite RR. eauto. }
    assert (equiv_st f''' 
            (ST (t !-> Closure x0 e0 C0; mem)
                (update C (ST mem t) x (Closure x0 e0 C0)))
            (ST ((f'' t) !-> Closure x0 e0 C_v''; mem'')
                (update C' (ST mem'' t'') x (Closure x0 e0 C_v'')))).
    { simpl. split.
      - rewrite Heqf'''. rewrite eqb_refl. apply eqb_eq. eauto.
      - intros. unfold update_m.
        destruct (eqb addr t) eqn:ADDR.
        + rewrite eqb_eq in ADDR. rewrite ADDR.
          rewrite Heqf'''. rewrite eqb_update. rewrite eqb_refl; repeat split; eauto.
          rewrite <- EQCarg. symmetry. apply bound_trans_ctx_eq with (t := t).
          apply BOUND''. rewrite EQCarg. rewrite <- Heqf'''. apply BB''.
        + pose proof (p_bound_or_not addr t) as CASES.
          destruct BOUND'' as [B1'' [B2'' B3'']].
          destruct CASES as [L | R]; 
          try (specialize (B3'' addr L); try rewrite B3''; eauto);
          try (specialize (B2'' addr R); try rewrite B2''; eauto).
          assert (f''' addr = f'' addr) as RR. symmetry. apply BB''. apply L. rewrite RR; clear RR.
          destruct EQstarg as [? H].
          specialize (H addr) as HINT.
          destruct (mem addr) eqn: ACCESS'; eauto. 
          destruct e4; simpl.
          assert (f'' addr < f'' t) as RR.
          { apply INCarg; eauto.
            red. left. red. intros contra. rewrite ACCESS' in contra. inversion contra.
            red. right. eauto. }
          destruct RR as [RR RR']. rewrite RR'. clear RR RR'.
          assert (trans_ctx f'' C2 = trans_ctx f''' C2) as RR.
          { apply bound_trans_ctx_eq with (t := t); eauto. } rewrite <- RR; clear RR. eauto.
          destruct (eqb (f'' addr) (f'' t)) eqn:EQ; eauto.
          rewrite eqb_eq in EQ. rewrite EQ in HINT.
          destruct (mem t). destruct e5. rewrite  rewrite ACCESS in HINT'. rewrite ACCESS' in HINT.
          simpl. right. symmetry in Heqb0. rewrite eqb_eq in Heqb0.
          rewrite <- Heqb0. apply HINT; eauto. apply HINT; eauto.
    }
    {rewrite plugin_trans_ctx; simpl. rewrite Heqα'''.
        rewrite eqb_update. rewrite <- Heqα'''.
        assert (trans_ctx α''' C_lam = abs_C'). rewrite Heqα'''.
        destruct abs_st'. simpl in SOUND'. destruct SOUND' as [[? [? ?]] ?]. rewrite <- H0.
        apply bound_trans_ctx_eq with (t := t1). apply BOUND'.
        red. intros. assert (eqb t' (update C (ST mem t) x (Closure x0 e0 C0)) = false).
        refl_bool. intros contra. rewrite eqb_eq in contra.
        assert (leb t' t = true). lebt t1.
        assert (t = t') as RR. apply leb_sym; try assumption. rewrite contra. apply update_lt.
        assert (t < t') as contra'. rewrite contra. apply update_lt.
        destruct contra' as [? contra']. rewrite RR in contra'. rewrite eqb_refl in contra'. inversion contra'.
        rewrite H3. symmetry. apply EQ''. assumption. rewrite H. eauto.}
    specialize (IHEVAL3 (C_v' [|dy_c_lam x (f'' t) ([||])|]) (ST mem'' t'') f'' EQC'' EQstarg).

