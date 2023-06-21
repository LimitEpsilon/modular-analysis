From MODULAR Require Export Sound.

Generalizable Variables T TT.

Definition equiv_st `{time T} `{time TT} (f : T -> TT)
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

Lemma equiv_eval : 
  forall `{time T} `{time TT} 
         (C : @dy_ctx T) st e v st_v
         (EVAL : EvalR C st e v st_v)
         (BOUND : time_bound C st)
         (C' : @dy_ctx TT) st' f
         (EQC : trans_ctx f C = C')
         (EQS : equiv_st f st st'),
    exists C_v' st_v' f',
      match st with
      | ST _ t =>
        eq_bound t f f' /\
        match v with
        | EVal (Closure x e_v C_v) =>
          trans_ctx f' C_v = C_v' /\
          equiv_st f' st_v st_v' /\
          EvalR C' st' e (EVal (Closure x e_v C_v')) st_v'
        | MVal C_v =>
          trans_ctx f' C_v = C_v' /\
          equiv_st f' st_v st_v' /\
          EvalR C' st' e (MVal C_v') st_v'
        end
      end.
Proof.
  intros. 
  rename H into ET. rename H0 into OT. rename H1 into tT.
  rename H2 into ETT. rename H3 into OTT. rename H4 into tTT.
  revert BOUND C' st' f EQC EQS.
  induction EVAL; intros; simpl in *.
  - rewrite <- STATE in EQS.
    simpl in EQS. destruct st' as [mem' t'].
    destruct EQS as [? EQS].
    specialize (EQS addr) as EQS'. rewrite <- ACCESS in EQS'.
    destruct v as [x' e_v C_v].
    destruct (mem' (f addr)) eqn:ACCESS'; try inversion EQS'.
    destruct e as [x'' e_v' C_v'].
    exists C_v'. exists (ST mem' t'). exists f.
    rewrite <- STATE. repeat split; try assumption.
    apply EQS'. 
    apply Eval_var_e with (addr := f addr) (mem := mem') (t := t'); eauto.
    rewrite <- EQC. rewrite trans_ctx_addr. rewrite <- ADDR. eauto.
    rewrite ACCESS'. destruct EQS' as [EQx [EQe EQc]]. subst; eauto.
  - exists C'. exists st'. exists f.
    destruct st. repeat split; eauto.
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
    specialize (IHEVAL1 C' st' f EQC EQS).
    destruct IHEVAL1 as [C_v' [st_v' [f' [BB [EQClam [EQstlam EVALlam]]]]]].
    assert (trans_ctx f' C = C') as EQC'.
    { rewrite <- EQC. symmetry. 
      apply bound_trans_ctx_eq with (t := t0); eauto. apply BOUND. }
    specialize (IHEVAL2 C' st_v' f' EQC' EQstlam). 
    destruct IHEVAL2 as [C_v'' [st_v'' [f'' [BB' [EQCarg [EQstarg EVALarg]]]]]].
    assert (trans_ctx f'' (C_lam [|dy_c_lam x t ([||])|]) = (C_v' [|dy_c_lam x (f'' t) ([||])|])) as EQC''.
    { rewrite plugin_trans_ctx. simpl.
      rewrite <- EQClam.
      assert (trans_ctx f' C_lam = trans_ctx f'' C_lam) as RR.
      apply bound_trans_ctx_eq with (t := t1); eauto. apply BOUND'.
      rewrite RR. eauto. }
    remember (fun t' => if eqb t' (update C (ST mem t) x (Closure x0 e0 C0))
                        then Abs.update abs_C (Abs.ST mem'' t'') x (Closure x0 e0 abs_C'') 
                        else α'' t') as α'''.
    specialize (IHEVAL3 (C_v' [|dy_c_lam x (f'' t) ([||])|]) st_v'' f'' EQC'' EQstarg).

