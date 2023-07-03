From Simple Require Export Syntax.

Generalizable Variables T.

Inductive state {T : Type} :=
  | ST (mem : T -> option (@expr_value T))
       (t : T)
.

Class time `{OrderT T} :=
{  
  tick : T -> T;
  tick_lt : forall t, t < tick t
}.

Definition update_m {T X} `{Eq T} mem (t : T) (x : X) :=
  fun t' => if eqb t' t then Some x else mem t'.

Definition empty_mem {T X} (t : T) : option X := None.

Notation "p '!->' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Inductive EvalR `{time T} (C : @dy_ctx T) (st : @state T)
    : tm -> (@dy_value T) -> (@state T) -> Prop :=
  | Eval_var_e x v mem t addr
             (STATE : ST mem t = st)
             (ADDR : Some addr = addr_x C x)
             (ACCESS : Some v = mem addr)
    : EvalR C st (e_var x) (EVal v) (ST mem t)
  | Eval_lam x e
    : EvalR C st (e_lam x e)
            (EVal (Closure x e C)) st
  | Eval_app e1 e2
             x e C_lam st_lam
             arg mem t
             v st_v
             (FN : EvalR C st e1
                         (EVal (Closure x e C_lam)) st_lam)
             (ARG : EvalR C st_lam e2
                          (EVal arg) (ST mem t))
             (BODY : EvalR (C_lam [|dy_c_lam x t ([||])|])
                           (ST (t !-> arg ; mem) (tick t))
                           e (EVal v) st_v)
    : EvalR C st (e_app e1 e2) (EVal v) st_v
  | Eval_link m e C_m st_m v st_v
               (MOD : EvalR C st m (MVal C_m) st_m)
               (LINK : EvalR C_m st_m e v st_v)
    : EvalR C st (e_link m e) v st_v
  | Eval_empty
    : EvalR C st m_empty (MVal C) st
  | Eval_var_m M C_M (ACCESS : Some C_M = ctx_M C M)
    : EvalR C st (m_var M) (MVal C_M) st
  | Eval_lete x e v mem t
              m C_m st_m
               (EVALe : EvalR C st e (EVal v) (ST mem t))
               (EVALm : EvalR (C [|dy_c_lete x t ([||])|])
                        (ST (t !-> v ; mem) (tick t))
                        m (MVal C_m) st_m)
    : EvalR C st (m_lete x e m) (MVal C_m) st_m
  | Eval_letm M m' C' st'
              m'' C'' st''
              (EVALm' : EvalR C st m' (MVal C') st')
              (EVALm'' : EvalR (C [|dy_c_letm M C' ([||])|]) st'
                         m'' (MVal C'') st'')
    : EvalR C st (m_letm M m' m'') (MVal C'') st''
.

#[export] Hint Constructors EvalR : core.

Inductive config {T} :=
  | Config (C : @dy_ctx T) (st : @state T) (e : tm)
.

Inductive interpreter_state {T} :=
  | Pending (reached : list (@config T))
  | Error (reached : list (@config T)) (* Type error *)
  | Resolved (v : @dy_value T) (st : @state T) (reached : list (@config T))
.

Fixpoint eval `{time T} (C : @dy_ctx T) (st : @state T) 
              (e : tm) (reached : list config) (FUEL : nat) :=
  let reached := (Config C st e) :: reached in
  match FUEL with
  | 0 => Pending reached
  | S FUEL' =>
    match e with
    | e_var x =>
      match addr_x C x with
      | None => Error reached
      | Some addr =>
        match st with
        | ST mem _ =>
          match mem addr with
          | None => Pending reached
          | Some v => Resolved (EVal v) st reached
          end
        end
      end
    | e_lam x e' =>
      Resolved (EVal (Closure x e' C)) st reached
    | e_app e1 e2 =>
      match eval C st e1 reached FUEL' with
      | Resolved (EVal (Closure x e' C_lam)) st_lam reached' =>
        match eval C st_lam e2 reached' FUEL' with
        | Resolved (EVal arg) (ST mem t) reached'' =>
          match eval (C_lam [| dy_c_lam x t ([||]) |]) 
                     (ST (t !-> arg ; mem) (tick t)) 
                     e' reached'' FUEL' with
          | Resolved (EVal v) st' reached''' => Resolved (EVal v) st' reached'''
          | Resolved _ _ reached''' => Error reached'''
          | other => other
          end
        | Resolved _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved _ _ reached' => Error reached'
      | other => other
      end
    | e_link m e' =>
      match eval C st m reached FUEL' with
      | Resolved (MVal C_m) st_m reached' =>
        match eval C_m st_m e' reached' FUEL' with
        | Resolved v st' reached'' => Resolved v st' reached''
        | other => other
        end
      | Resolved _ _ reached' => Error reached'
      | other => other
      end
    | m_empty => Resolved (MVal C) st reached
    | m_var M =>
      match ctx_M C M with
      | None => Pending reached
      | Some C_M => Resolved (MVal C_M) st reached
      end
    | m_lete x e m =>
      match eval C st e reached FUEL' with
      | Resolved (EVal v) (ST mem t) reached' =>
        match eval (C[| dy_c_lete x t ([||]) |]) 
                   (ST (t !-> v ; mem) (tick t)) 
                   m reached' FUEL' with
        | Resolved (MVal C') st' reached'' => Resolved (MVal C') st' reached''
        | Resolved _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved _ _ reached' => Error reached'
      | other => other
      end
    | m_letm M m1 m2 =>
      match eval C st m1 reached FUEL' with
      | Resolved (MVal C') st' reached' =>
        match eval (C[| dy_c_letm M C' ([||]) |])
                   st' m2 reached' FUEL' with
        | Resolved (MVal C'') st'' reached'' => Resolved (MVal C'') st'' reached''
        | Resolved _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved _ _ reached' => Error reached'
      | other => other
      end
    end
  end.

Lemma relax_fuel :
  forall `{TIME : time T} (C : @dy_ctx T) st e l l' v st' FUEL FUEL' (LE : FUEL <= FUEL'),
    eval C st e l FUEL = Resolved v st' l' ->
    eval C st e l FUEL' = Resolved v st' l'.
Proof.
  intros. rename H into H'. rename H0 into H''. rename H1 into H.
  revert C st e l l' v st' H FUEL' LE.
  induction FUEL; intros.
  - inversion H.
  - simpl in H; destruct e; inversion LE; eauto.
    + remember (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      clear H3. destruct v1 as [x v1 C_lam].
      remember (eval C st1 e2 reached FUEL) as v2.
      destruct v2 as [ | | v2 st2]; inversion H;
      clear H3. destruct v2 as [v2 | ]; inversion H.
      clear H3. destruct st2 as [mem2 t2].
      remember (eval (C_lam [|dy_c_lam x t2 ([||])|]) 
                     (ST (t2 !-> v2; mem2) (tick t2))
                      v1 reached0 FUEL) as v3.
      destruct v3 as [ | | v3 st3]; inversion H.
      clear H3. destruct v3 as [v3 | ]; inversion H.
      subst. 
      assert (eval C st e1 (Config C st (e_app e1 e2) :: l) m = Resolved (EVal (Closure x v1 C_lam)) st1 reached) as RR1.
      apply IHFUEL; eauto. nia.
      assert (eval C st1 e2 reached m = Resolved (EVal v2) (ST mem2 t2) reached0) as RR2.
      apply IHFUEL; eauto. nia.
      assert (eval (C_lam [|dy_c_lam x t2 ([||])|])
                   (ST (t2 !-> v2; mem2) (tick t2)) v1 reached0 m = 
              Resolved (EVal v3) st' l') as RR3.
      apply IHFUEL; eauto. nia.
      simpl. rewrite RR1. rewrite RR2. rewrite RR3. eauto.
    + remember (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      remember (eval mv st1 e2 reached FUEL) as v2.
      clear H3. destruct v2 as [ | | v2 st2]; inversion H.
      clear H3. destruct v2 as [v2 | ]; inversion H; subst;
      assert (eval C st e1 (Config C st (e_link e1 e2) :: l) m = Resolved (MVal mv) st1 reached) as RR1;
      try (apply IHFUEL; eauto; nia).
      assert (eval mv st1 e2 reached m = Resolved (EVal v2) st' l') as RR2.
      apply IHFUEL; eauto; nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
      assert (eval mv st1 e2 reached m = Resolved (MVal mv0) st' l') as RR2.
      apply IHFUEL; eauto; nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
    + remember (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      clear H3. destruct st1 as [mem1 t1].
      remember (eval (C [|dy_c_lete x t1 ([||])|]) 
                     (ST (t1 !-> v1; mem1) (tick t1))
                      e2 reached FUEL) as v2.
      destruct v2 as [ | | v2 st2]; inversion H.
      clear H3. destruct v2 as [v2 | ]; inversion H.
      subst.
      assert (eval C st e1 (Config C st (m_lete x e1 e2) :: l) m = Resolved (EVal v1) (ST mem1 t1) reached) as RR1.
      apply IHFUEL; eauto. nia.
      assert (eval (C [|dy_c_lete x t1 ([||])|]) 
                   (ST (t1 !-> v1; mem1) (tick t1))
                   e2 reached m = Resolved (MVal mv) st' l') as RR2.
      apply IHFUEL; eauto. nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
    + remember (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      clear H3.
      remember (eval (C [|dy_c_letm M mv ([||])|]) st1
                      e2 reached FUEL) as v2.
      destruct v2 as [ | | v2 st2]; inversion H.
      clear H3. destruct v2 as [v2 | ]; inversion H.
      subst.
      assert (eval C st e1 (Config C st (m_letm M e1 e2) :: l) m = Resolved (MVal mv) st1 reached) as RR1.
      apply IHFUEL; eauto. nia.
      assert (eval (C [|dy_c_letm M mv ([||])|]) st1
                   e2 reached m = Resolved (MVal mv0) st' l') as RR2.
      apply IHFUEL; eauto. nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
Qed.
      
Lemma EvalR_well_defined_l :
  forall `{time T} (C : @dy_ctx T) st e l v st' (R : EvalR C st e v st'),
    exists FUEL, 
      match eval C st e l FUEL with
      | Resolved v' st'' _ => v = v' /\ st' = st''
      | _ => False
      end.
Proof.
  intros. revert l. induction R; intros.
  - exists 1; simpl. rewrite <- ADDR. rewrite <- STATE. rewrite <- ACCESS. eauto.
  - exists 1; simpl; eauto.
  - destruct (IHR1 (Config C st (e_app e1 e2) :: l)) as [FUEL' EQ']. clear IHR1.
    destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL') eqn:EVAL1; try (inversion EQ'; fail).
    destruct (IHR2 reached) as [FUEL'' EQ'']. clear IHR2.
    destruct (eval C st_lam e2 reached FUEL'') eqn:EVAL2; try (inversion EQ''; fail).
    destruct (IHR3 reached0) as [FUEL''' EQ''']. clear IHR3.
    destruct (eval (C_lam [|dy_c_lam x t ([||])|])
                   (ST (t !-> arg; mem) (tick t)) e reached0
                   FUEL''') eqn:EVAL3; try (inversion EQ'''; fail).
    exists (S (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))).
    simpl.
    destruct EQ' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct EQ'' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct EQ''' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    assert (eval C st e1 (Config C st (e_app e1 e2) :: l) (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))
            = Resolved (EVal (Closure x e C_lam)) st_lam reached) as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval C st_lam e2 reached (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))
            = Resolved (EVal arg) (ST mem t) reached0) as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR.
    assert (eval (C_lam [|dy_c_lam x t ([||])|]) 
                 (ST (t !-> arg; mem) (tick t)) e reached0
                 (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))
            = Resolved (EVal v) st_v reached1) as RR.
    apply relax_fuel with (FUEL := FUEL'''). nia. eauto.
    rewrite RR; clear RR. eauto.
  - destruct (IHR1 (Config C st (e_link m e) :: l)) as [FUEL' EQ']. clear IHR1.
    destruct (eval C st m (Config C st (e_link m e) :: l) FUEL') eqn:EVAL1; try (inversion EQ'; fail).
    destruct (IHR2 reached) as [FUEL'' EQ'']. clear IHR2.
    destruct (eval C_m st_m e reached FUEL'') eqn:EVAL2; try (inversion EQ''; fail).
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    destruct EQ' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct EQ'' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    assert (eval C st m (Config C st (e_link m e) :: l) (Nat.max FUEL' FUEL'')
            = Resolved (MVal C_m) st_m reached) as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval C_m st_m e reached (Nat.max FUEL' FUEL'')
            = Resolved v st_v reached0) as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR. eauto.
  - exists 1. simpl; eauto. 
  - exists 1; simpl. rewrite <- ACCESS. eauto.
  - destruct (IHR1 (Config C st (m_lete x e m) :: l)) as [FUEL' EQ']. clear IHR1.
    destruct (eval C st e (Config C st (m_lete x e m) :: l) FUEL') eqn:EVAL1; try (inversion EQ'; fail).
    destruct (IHR2 reached) as [FUEL'' EQ'']. clear IHR2.
    destruct (eval (C [|dy_c_lete x t ([||])|])
                   (ST (t !-> v; mem) (tick t)) m reached
                   FUEL'') eqn:EVAL2; try (inversion EQ''; fail).
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    destruct EQ' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct EQ'' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    assert (eval C st e (Config C st (m_lete x e m) :: l) (Nat.max FUEL' FUEL'')
            = Resolved (EVal v) (ST mem t) reached) as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval (C [|dy_c_lete x t ([||])|]) 
                 (ST (t !-> v; mem) (tick t)) m reached
                 (Nat.max FUEL' FUEL'')
            = Resolved (MVal C_m) st_m reached0) as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR. eauto.
  - destruct (IHR1 (Config C st (m_letm M m' m'') :: l)) as [FUEL' EQ']. clear IHR1.
    destruct (eval C st m' (Config C st (m_letm M m' m'') :: l) FUEL') eqn:EVAL1; try (inversion EQ'; fail).
    destruct (IHR2 reached) as [FUEL'' EQ'']. clear IHR2.
    destruct (eval (C [|dy_c_letm M C' ([||])|]) st' m'' reached FUEL'') eqn:EVAL2; try (inversion EQ''; fail).
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    destruct EQ' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct EQ'' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    assert (eval C st m' (Config C st (m_letm M m' m'') :: l) (Nat.max FUEL' FUEL'')
            = Resolved (MVal C') st' reached) as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval (C [|dy_c_letm M C' ([||])|]) st' m'' reached (Nat.max FUEL' FUEL'')
            = Resolved (MVal C'') st'' reached0) as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR. eauto.
Qed.

Lemma EvalR_well_defined_r :
  forall `{TIME : time T} FUEL (C : @dy_ctx T) st e l v st'
    (R : match eval C st e l FUEL with
         | Resolved v' st'' _ => v = v' /\ st' = st''
         | _ => False
         end),
    EvalR C st e v st'.
Proof.
  intros. rename H into H'. rename H0 into H''. generalize dependent T. revert e.
  induction FUEL; intros; simpl in *; try (inversion R; fail).
  destruct e.
  - destruct (addr_x C x) eqn:ADDR;
    destruct st; destruct (mem t) eqn:ACCESS; 
    inversion R. subst. eauto.
  - inversion R. subst. eauto.
  - remember (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL) as v1.
    destruct v1 as [ | | v1 st1]; try inversion R.
    destruct v1 as [v1 | ]; try inversion R.
    destruct v1 as [x v1 C_lam].
    remember (eval C st1 e2 reached FUEL) as v2.
    destruct v2 as [ | | v2 st2]; try inversion R.
    destruct v2 as [v2 | ]; try inversion R.
    destruct st2 as [mem2 t2].
    remember (eval (C_lam [|dy_c_lam x t2 ([||])|])
                   (ST (t2 !-> v2; mem2) (tick t2)) 
                   v1 reached0 FUEL) as v3.
    destruct v3 as [ | | v3 st3]; try inversion R.
    destruct v3 as [v3 | ]; try inversion R.
    subst.
    assert (EvalR C st e1 (EVal (Closure x v1 C_lam)) st1) as RR1. 
    eapply IHFUEL; rewrite <- Heqv1; eauto.
    assert (EvalR C st1 e2 (EVal v2) (ST mem2 t2)) as RR2.
    eapply IHFUEL; rewrite <- Heqv2; eauto.
    assert (EvalR (C_lam [|dy_c_lam x t2 ([||])|])
                  (ST (t2 !-> v2; mem2) (tick t2)) v1
            (EVal v3) st3) as RR3. 
    eapply IHFUEL; rewrite <- Heqv3; eauto. eauto.
  - remember (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL) as v1.
    destruct v1 as [ | | v1 st1]; try inversion R.
    destruct v1 as [v1 | ]; try inversion R.
    remember (eval mv st1 e2 reached FUEL) as v2.
    destruct v2 as [ | | v2 st2]; inversion R.
    assert (EvalR C st e1 (MVal mv) st1).
    eapply IHFUEL; rewrite <- Heqv1; eauto.
    assert (EvalR mv st1 e2 v2 st2).
    eapply IHFUEL; rewrite <- Heqv2; eauto.
    subst. eauto.
  - inversion R; subst. eapply Eval_empty; eauto.
  - remember (ctx_M C M) as ACCESS.
    destruct ACCESS; inversion R; subst. eapply Eval_var_m; eauto.
  - remember (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL) as v1.
    destruct v1 as [ | | v1 st1]; try inversion R.
    destruct v1 as [v1 | ]; try inversion R.
    destruct st1 as [mem1 t1].
    remember (eval (C [|dy_c_lete x t1 ([||])|])
                   (ST (t1 !-> v1; mem1) (tick t1)) 
                   e2 reached FUEL) as v2.
    destruct v2 as [ | | v2 st2]; try inversion R.
    destruct v2 as [v2 | ]; inversion R.
    assert (EvalR C st e1 (EVal v1) (ST mem1 t1)).
    eapply IHFUEL; rewrite <- Heqv1; eauto.
    assert (EvalR (C [|dy_c_lete x t1 ([||])|])
                  (ST (t1 !-> v1; mem1) (tick t1)) e2
            (MVal mv) st2).
    eapply IHFUEL; rewrite <- Heqv2; eauto.
    subst. eauto.
  - remember (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL) as v1.
    destruct v1 as [ | | v1 st1]; try inversion R.
    destruct v1 as [v1 | ]; try inversion R.
    remember (eval (C [|dy_c_letm M mv ([||])|]) st1 e2 reached FUEL) as v2.
    destruct v2 as [ | | v2 st2]; try inversion R.
    destruct v2 as [v2 | ]; inversion R.
    assert (EvalR C st e1 (MVal mv) st1).
    eapply IHFUEL; rewrite <- Heqv1; eauto.
    assert (EvalR (C [|dy_c_letm M mv ([||])|]) st1 e2 (MVal mv0) st2).
    eapply IHFUEL; rewrite <- Heqv2; eauto.
    subst. eauto.
Qed.

Theorem EvalR_well_defined :
  forall `{TIME : time T} l C st e v st',
    (exists FUEL, 
      match eval C st e l FUEL with 
      | Resolved v' st'' _ => v = v' /\ st' = st''
      | _ => False
      end) <->
    EvalR C st e v st'.
Proof.
  intros; split; try apply EvalR_well_defined_l.
  intros. destruct H1 as [FUEL EVAL].
  eapply EvalR_well_defined_r. eauto.
Qed.

(* Reachability relation *)
Inductive one_reach `{time T} (C : dy_ctx) (st : state)
    : tm -> (@dy_ctx T) -> (@state T) -> tm -> Prop :=
  | one_appl e1 e2
    : one_reach C st (e_app e1 e2) 
                C st e1
  | one_appr e1 e2 x e C_lam st_lam
             (FN : EvalR C st e1 
                  (EVal (Closure x e C_lam)) st_lam)
    : one_reach C st (e_app e1 e2)
                C st_lam e2
  | one_appbody e1 e2 x e C_lam st_lam
                arg mem t
                (FN : EvalR C st e1 
                            (EVal (Closure x e C_lam)) st_lam)
                (ARG : EvalR C st_lam e2
                             (EVal arg) (ST mem t))
    : one_reach C st (e_app e1 e2)
                (C_lam[|dy_c_lam x t ([||])|]) 
                (ST (t !-> arg ; mem) (tick t)) e
  | one_linkl m e
    : one_reach C st (e_link m e)
                C st m
  | one_linkr m e C_m st_m
              (MOD : EvalR C st m (MVal C_m) st_m)
    : one_reach C st (e_link m e)
                C_m st_m e
  | one_letel x e m
    : one_reach C st (m_lete x e m)
                C st e
  | one_leter x e m v mem t
              (EVALx : EvalR C st e (EVal v) (ST mem t))
    : one_reach C st (m_lete x e m)
                (C[|dy_c_lete x t ([||])|])
                (ST (t !-> v ; mem) (tick t)) m
  | one_letml M m1 m2
    : one_reach C st (m_letm M m1 m2)
                C st m1
  | one_letmr M m1 m2 C_M st_M
              (EVALM : EvalR C st m1 (MVal C_M) st_M)
    : one_reach C st (m_letm M m1 m2)
                (C[|dy_c_letm M C_M ([||])|]) st_M m2
.

Inductive multi_reach `{time T} (C : dy_ctx) (st : state)
    : tm -> (@dy_ctx T) -> (@state T) -> tm -> Prop :=
  | multi_refl e : multi_reach C st e C st e
  | multi_step e C' st' e' C'' st'' e''
               (REACHl : one_reach C st e C' st' e')
               (REACHr : multi_reach C' st' e' C'' st'' e'')
    : multi_reach C st e C'' st'' e''
.

Inductive ReachR `{time T} (C : @dy_ctx T) (st : @state T)
    : tm -> (@dy_ctx T) -> (@state T) -> tm -> Prop :=
  | r_refl e
    : ReachR C st e 
             C st e
  | r_app_left e1 e2 C' st' e'
               (REACHl : ReachR C st e1
                                C' st' e')
    : ReachR C st (e_app e1 e2) 
             C' st' e'
  | r_app_right e1 e2 x e C_lam st_lam C' st' e'
                (FN : EvalR C st e1 
                            (EVal (Closure x e C_lam)) st_lam)
                (REACHr : ReachR C st_lam e2
                                 C' st' e')
    : ReachR C st (e_app e1 e2)
             C' st' e'
  | r_app_body e1 e2 x e C_lam st_lam
                arg mem t
                C' st' e'
                (FN : EvalR C st e1 
                            (EVal (Closure x e C_lam)) st_lam)
                (ARG : EvalR C st_lam e2
                             (EVal arg) (ST mem t))
                (REACHb : ReachR (C_lam[|dy_c_lam x t ([||])|]) 
                                 (ST (t !-> arg ; mem) (tick t)) e
                                 C' st' e')
    : ReachR C st (e_app e1 e2)
             C' st' e'
  | r_link_m m e C' st' e'
              (REACHm : ReachR C st m
                               C' st' e')
    : ReachR C st (e_link m e)
             C' st' e'
  | r_link_e m e C_m st_m C' st' e'
             (MOD : EvalR C st m (MVal C_m) st_m)
             (REACHe : ReachR C_m st_m e
                              C' st' e')
    : ReachR C st (e_link m e)
             C' st' e'
  | r_lete_e x e m C' st' e'
             (REACHe : ReachR C st e
                              C' st' e')
    : ReachR C st (m_lete x e m)
             C' st' e'
  | r_lete_m x e m v mem t
             C' st' e'
             (EVALx : EvalR C st e (EVal v) (ST mem t))
             (REACHm : ReachR (C[|dy_c_lete x t ([||])|])
                              (ST (t !-> v ; mem) (tick t)) m
                              C' st' e')
    : ReachR C st (m_lete x e m)
             C' st' e'
  | r_letm_m1 M m1 m2 C' st' e'
              (REACHm : ReachR C st m1
                               C' st' e')
    : ReachR C st (m_letm M m1 m2)
             C' st' e'
  | r_letm_m2 M m1 m2 C_M st_M
              C' st' e'
              (EVALM : EvalR C st m1 (MVal C_M) st_M)
              (REACHm : ReachR (C[|dy_c_letm M C_M ([||])|]) st_M m2
                               C' st' e')
    : ReachR C st (m_letm M m1 m2)
             C' st' e'
.

#[export] Hint Constructors ReachR : core.

Notation "'<|' C1 st1 tm1 '~>' C2 st2 tm2 '|>'" := (ReachR C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

Notation "'<|' C1 st1 tm1 '~>*' C2 st2 tm2 '|>'" := (multi_reach C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

(* sanity check *)
Lemma reach_trans : forall {T} `{time T} (C1 : @dy_ctx T) st1 e1
                         C2 st2 e2
                         C3 st3 e3
                         (REACH1 : <| C1 st1 e1 ~> C2 st2 e2 |>)
                         (REACH2 : <| C2 st2 e2 ~> C3 st3 e3 |>),
                         <| C1 st1 e1 ~> C3 st3 e3 |>.
Proof.
  intros. generalize dependent e3.
  revert C3 st3.
  induction REACH1; eauto.
Qed.


Lemma reach_eq `{time T} :
  forall (C1 : @dy_ctx T) st1 e1 C2 st2 e2,
  <| C1 st1 e1 ~> C2 st2 e2 |> <-> <| C1 st1 e1 ~>* C2 st2 e2 |>.
Proof.
  intros; split; intro REACH; induction REACH; eauto;
  try apply multi_refl;
  try (eapply multi_step; eauto).
  - apply one_appl.
  - eapply one_appr; eauto.
  - eapply one_appbody; eauto.
  - eapply one_linkl; eauto.
  - eapply one_linkr; eauto.
  - eapply one_letel; eauto.
  - eapply one_leter; eauto.
  - eapply one_letml; eauto.
  - eapply one_letmr; eauto.
  - destruct REACHl; eauto.
Qed.

Definition extract_reached {T} (interp : @interpreter_state T) :=
  match interp with
  | Pending reached
  | Error reached
  | Resolved _ _ reached => reached
  end.

Lemma reach_myself :
  forall `{TIME : time T} (C : @dy_ctx T) st e l FUEL,
    In (Config C st e) (extract_reached (eval C st e l FUEL)) /\
    (forall cf, In cf l -> In cf (extract_reached (eval C st e l FUEL))).
Proof.
  intros. rename H into H'. rename H0 into H''.
  revert C st e l; induction FUEL; intros; try (simpl; eauto; fail).
  split.
  - simpl. destruct e.
    + destruct (addr_x C x) as [addr | ]; try destruct st;
      try destruct (mem addr); simpl; eauto.
    + simpl; eauto.
    + specialize (IHFUEL C st e1 (Config C st (e_app e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL);
      assert (In (Config C st (e_app e1 e2)) reached); try apply IH'; simpl; eauto.
      destruct v; simpl; eauto.
      destruct ev as [x e C']. clear IH IH'.
      specialize (IHFUEL C st0 e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st0 e2 reached FUEL); eauto.
      destruct v; eauto. destruct st1.
      assert (In (Config C st (e_app e1 e2)) reached0); eauto. clear IH IH'.
      specialize (IHFUEL (C' [|dy_c_lam x t ([||])|]) (ST (t !-> ev; mem) (tick t)) e reached0) as IH.
      destruct IH as [IH IH'].
      destruct (eval (C' [|dy_c_lam x t ([||])|])
                (ST (t !-> ev; mem) (tick t)) e reached0
                FUEL); eauto.
      destruct v; eauto.
    + specialize (IHFUEL C st e1 (Config C st (e_link e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL);
      assert (In (Config C st (e_link e1 e2)) reached); try apply IH'; simpl; eauto.
      destruct v; simpl; eauto. clear IH IH'.
      specialize (IHFUEL mv st0 e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval mv st0 e2 reached FUEL); eauto.
    + simpl. eauto.
    + destruct (ctx_M C M); simpl; eauto.
    + specialize (IHFUEL C st e1 (Config C st (m_lete x e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL);
      assert (In (Config C st (m_lete x e1 e2)) reached); try apply IH'; simpl; eauto.
      destruct v; simpl; eauto. destruct st0. clear IH IH'.
      specialize (IHFUEL (C [|dy_c_lete x t ([||])|]) (ST (t !-> ev; mem) (tick t)) e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e2 reached
                     FUEL); eauto.
      destruct v; eauto.
    + specialize (IHFUEL C st e1 (Config C st (m_letm M e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL);
      assert (In (Config C st (m_letm M e1 e2)) reached); try apply IH'; simpl; eauto.
      destruct v; simpl; eauto. clear IH IH'.
      specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached FUEL); eauto.
      destruct v; eauto.
  - intros. destruct e; simpl; eauto.
    + destruct (addr_x C x); simpl; eauto. destruct st. destruct (mem t); simpl; eauto.
    + specialize (IHFUEL C st e1 (Config C st (e_app e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL);
      assert (In cf reached); simpl in *; eauto.
      destruct v; simpl; eauto.
      destruct ev as [x e C']. clear IH IH'.
      specialize (IHFUEL C st0 e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st0 e2 reached FUEL); eauto.
      destruct v; eauto. destruct st1.
      assert (In cf reached0); simpl in *; eauto. clear IH IH'.
      specialize (IHFUEL (C' [|dy_c_lam x t ([||])|]) (ST (t !-> ev; mem) (tick t)) e reached0) as IH.
      destruct IH as [IH IH'].
      destruct (eval (C' [|dy_c_lam x t ([||])|])
                (ST (t !-> ev; mem) (tick t)) e reached0
                FUEL); eauto.
      destruct v; eauto.
    + specialize (IHFUEL C st e1 (Config C st (e_link e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL);
      assert (In cf reached); try apply IH'; simpl; eauto.
      destruct v; simpl; eauto. clear IH IH'.
      specialize (IHFUEL mv st0 e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval mv st0 e2 reached FUEL); eauto.
    + destruct (ctx_M C M); simpl; eauto.
    + specialize (IHFUEL C st e1 (Config C st (m_lete x e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL);
      assert (In cf reached); try apply IH'; simpl; eauto.
      destruct v; simpl; eauto. destruct st0. clear IH IH'.
      specialize (IHFUEL (C [|dy_c_lete x t ([||])|]) (ST (t !-> ev; mem) (tick t)) e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e2 reached
                     FUEL); eauto.
      destruct v; eauto.
    + specialize (IHFUEL C st e1 (Config C st (m_letm M e1 e2) :: l)) as IH.
      destruct IH as [IH IH'].
      destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL);
      assert (In cf reached); try apply IH'; simpl; eauto.
      destruct v; simpl; eauto. clear IH IH'.
      specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached) as IH.
      destruct IH as [IH IH'].
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached FUEL); eauto.
      destruct v; eauto.
Qed.

Lemma relax_fuel_reach :
  forall `{TIME : time T} (C : @dy_ctx T) st e l cf FUEL FUEL' (LE : FUEL <= FUEL'),
    In cf (extract_reached (eval C st e l FUEL)) ->
    In cf (extract_reached (eval C st e l FUEL')).
Proof.
  intros. rename H into H'. rename H0 into H''. rename H1 into H.
  revert C st e l FUEL' LE H.
  induction FUEL; intros.
  - pose proof (reach_myself C st e l FUEL') as [HINT HINT'].
    inversion H; eauto. rewrite <- H0; eauto.
  - simpl in H; destruct e; inversion LE; eauto; assert (FUEL <= m) as LE'; try nia.
    + specialize (IHFUEL C st e1 (Config C st (e_app e1 e2) :: l) m LE') as HINT.
      destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL) eqn:EVAL1; simpl;
      destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) m) eqn:EVAL1'; eauto;
      try (
        assert (In cf (extract_reached (eval C st0 e2 reached0 m))) as HINT';
        try (apply reach_myself; apply HINT; eauto);
        destruct v; eauto; destruct ev;
        destruct (eval C st0 e2 reached0 m); eauto;
        destruct v; eauto; destruct st1;
        assert (In cf (extract_reached (eval (C0 [|dy_c_lam x t ([||])|])
                                             (ST (t !-> ev; mem) (tick t)) e
                                             reached1 m))) as HINT'';
        try (apply reach_myself; apply HINT');
        destruct (eval (C0 [|dy_c_lam x t ([||])|])
                       (ST (t !-> ev; mem) (tick t)) e
                       reached1 m); eauto; destruct v; eauto; fail);
      pose proof (relax_fuel C st e1 (Config C st (e_app e1 e2) :: l) reached v st0 FUEL m LE' EVAL1) as RR;
      rewrite RR in EVAL1'; inversion EVAL1'; subst.
      destruct v0; eauto. destruct ev.
      specialize (IHFUEL C st1 e2 reached0 m LE') as HINT'.
      destruct (eval C st1 e2 reached0 FUEL) eqn:EVAL2;
      destruct (eval C st1 e2 reached0 m) eqn:EVAL2'; eauto;
      try (
        specialize (HINT' H); destruct v; eauto; destruct st0;
        assert (In cf (extract_reached (eval (C0 [|dy_c_lam x t ([||])|])
                                           (ST (t !-> ev; mem) (tick t)) e
                                           reached1 m))) as HINT'';
        try (apply reach_myself; apply HINT');
        destruct (eval (C0 [|dy_c_lam x t ([||])|])
                       (ST (t !-> ev; mem) (tick t)) e
                       reached1 m); eauto; destruct v; eauto);
      pose proof (relax_fuel C st1 e2 reached0 reached v st0 FUEL m LE' EVAL2) as RR';
      rewrite RR' in EVAL2'; inversion EVAL2'; subst.
      destruct v0; eauto. destruct st2.
      specialize (IHFUEL (C0 [|dy_c_lam x t ([||])|])
                         (ST (t !-> ev; mem) (tick t)) e
                         reached1 m LE') as HINT''.
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e
                     reached1 FUEL) eqn:EVAL3;
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e
                     reached1 m) eqn:EVAL3'; eauto;
      try (destruct v; eauto); destruct v0; eauto.
    + specialize (IHFUEL C st e1 (Config C st (e_link e1 e2) :: l) m LE') as HINT.
      destruct (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL) eqn:EVAL1; simpl;
      destruct (eval C st e1 (Config C st (e_link e1 e2) :: l) m) eqn:EVAL1'; eauto;
      try (
        destruct v; eauto;
        assert (In cf (extract_reached (eval mv st0 e2 reached0 m))) as HINT';
        try (apply reach_myself; apply HINT; eauto);
        destruct (eval mv st0 e2 reached0 m); eauto; fail);
      pose proof (relax_fuel C st e1 (Config C st (e_link e1 e2) :: l) reached v st0 FUEL m LE' EVAL1) as RR;
      rewrite RR in EVAL1'; inversion EVAL1'; subst.
      destruct v0; eauto.
      destruct (eval mv st1 e2 reached0 FUEL) eqn:EVAL2; simpl;
      destruct (eval mv st1 e2 reached0 m) eqn:EVAL2';
      try (
        assert (In cf (extract_reached (eval mv st1 e2 reached0 m))) as HINT';
        try (apply IHFUEL; eauto; rewrite EVAL2; eauto);
        rewrite EVAL2' in HINT'; eauto).
    + specialize (IHFUEL C st e1 (Config C st (m_lete x e1 e2) :: l) m LE') as HINT.
      destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL) eqn:EVAL1; simpl;
      destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l) m) eqn:EVAL1'; eauto;
      try (
        destruct v; eauto; destruct st0;
        assert (In cf (extract_reached (eval (C [|dy_c_lete x t ([||])|])
                                             (ST (t !-> ev; mem) (tick t)) e2
                                             reached0 m))) as HINT';
        try (apply reach_myself; apply HINT; eauto);
        destruct (eval (C [|dy_c_lete x t ([||])|])
                       (ST (t !-> ev; mem) (tick t)) e2
                       reached0 m); eauto; destruct v; eauto; fail);
      pose proof (relax_fuel C st e1 (Config C st (m_lete x e1 e2) :: l) reached v st0 FUEL m LE' EVAL1) as RR;
      rewrite RR in EVAL1'; inversion EVAL1'; subst.
      destruct v0; eauto. destruct st1.
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e2 reached0
                     FUEL) eqn:EVAL2; simpl;
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e2 reached0
                     m) eqn:EVAL2';
      try (
        assert (In cf (extract_reached (eval (C [|dy_c_lete x t ([||])|])
                                             (ST (t !-> ev; mem) (tick t)) e2 reached0
                                             m))) as HINT';
        try (apply IHFUEL; eauto; rewrite EVAL2; eauto);
        rewrite EVAL2' in HINT'; eauto; destruct v; eauto);
      pose proof (relax_fuel (C [|dy_c_lete x t ([||])|])
                             (ST (t !-> ev; mem) (tick t)) e2
                             reached0 reached v st0 FUEL m LE' EVAL2) as RR';
      rewrite RR' in EVAL2'; inversion EVAL2'; subst.
      destruct v0; eauto.
    + specialize (IHFUEL C st e1 (Config C st (m_letm M e1 e2) :: l) m LE') as HINT.
      destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL) eqn:EVAL1; simpl;
      destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l) m) eqn:EVAL1'; eauto;
      try (
        destruct v; eauto;
        assert (In cf (extract_reached (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 m))) as HINT';
        try (apply reach_myself; apply HINT; eauto);
        destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 m); eauto; destruct v; eauto; fail);
      pose proof (relax_fuel C st e1 (Config C st (m_letm M e1 e2) :: l) reached v st0 FUEL m LE' EVAL1) as RR;
      rewrite RR in EVAL1'; inversion EVAL1'; subst.
      destruct v0; eauto.
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st1 e2 reached0 FUEL) eqn:EVAL2; simpl;
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st1 e2 reached0 m) eqn:EVAL2';
      try (
        assert (In cf (extract_reached (eval (C [|dy_c_letm M mv ([||])|]) st1 e2 reached0 m))) as HINT';
        try (apply IHFUEL; eauto; rewrite EVAL2; eauto);
        rewrite EVAL2' in HINT'; eauto; destruct v; eauto; fail);
      pose proof (relax_fuel (C [|dy_c_letm M mv ([||])|]) st1 e2 reached0 reached v st0 FUEL m LE' EVAL2) as RR';
      rewrite RR' in EVAL2'; inversion EVAL2'; subst.
      destruct v0; eauto.
Qed.

Lemma reach_same :
  forall `{TIME : time T} FUEL (C : @dy_ctx T) st e l l'
          (CONTAINED : forall cf, In cf l -> In cf l'),
    match (eval C st e l FUEL), (eval C st e l' FUEL) with
    | Resolved v st_v reached, Resolved v' st_v' reached' => 
      v = v' /\ st_v = st_v' /\ (forall cf, In cf reached -> In cf reached')
    | Error reached, Error reached'
    | Pending reached, Pending reached' =>
      forall cf, In cf reached -> In cf reached'
    | _, _ => False
    end.
Proof.
  intros. rename H into ET. rename H0 into OT.
  revert C st e l l' CONTAINED. induction FUEL; intros.
  simpl. intros. destruct H; eauto.
  destruct e; simpl; eauto.
  - destruct (addr_x C x); destruct st; destruct (mem t); repeat split; intros; destruct H; simpl; eauto.
  - repeat split; intros; destruct H; eauto.
  - assert ((forall cf : config,
                    In cf (Config C st (e_app e1 e2) :: l) ->
                    In cf (Config C st (e_app e1 e2) :: l'))) as CONTAINED'.
    { intros. simpl in *. destruct H; eauto. }
    specialize (IHFUEL C st e1 (Config C st (e_app e1 e2) :: l) (Config C st (e_app e1 e2) :: l') CONTAINED') as IHl.
    clear CONTAINED'.
    destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL);
    destruct (eval C st e1 (Config C st (e_app e1 e2) :: l') FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHl as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct v; eauto. destruct ev.
    specialize (IHFUEL C st0 e2 reached reached0 CONTAINED') as IHr.
    clear CONTAINED'.
    destruct (eval C st0 e2 reached FUEL);
    destruct (eval C st0 e2 reached0 FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHr as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct v; eauto. destruct st2.
    specialize (IHFUEL (C0 [|dy_c_lam x t ([||])|])
                       (ST (t !-> ev; mem) (tick t))
                       e reached1 reached2 CONTAINED').
    clear CONTAINED'.
    destruct (eval (C0 [|dy_c_lam x t ([||])|])
                   (ST (t !-> ev; mem) (tick t))
                   e reached1 FUEL);
    destruct (eval (C0 [|dy_c_lam x t ([||])|])
                   (ST (t !-> ev; mem) (tick t))
                   e reached2 FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHFUEL as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct v; eauto.
  - assert ((forall cf : config,
                    In cf (Config C st (e_link e1 e2) :: l) ->
                    In cf (Config C st (e_link e1 e2) :: l'))) as CONTAINED'.
    { intros. simpl in *. destruct H; eauto. }
    specialize (IHFUEL C st e1 (Config C st (e_link e1 e2) :: l) (Config C st (e_link e1 e2) :: l') CONTAINED') as IHl.
    clear CONTAINED'.
    destruct (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL);
    destruct (eval C st e1 (Config C st (e_link e1 e2) :: l') FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHl as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct v; eauto.
    specialize (IHFUEL mv st0 e2 reached reached0 CONTAINED') as IHr. clear CONTAINED'.
    destruct (eval mv st0 e2 reached FUEL);
    destruct (eval mv st0 e2 reached0 FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
  - repeat split; eauto. intros; destruct H; eauto.
  - destruct (ctx_M C M); eauto; repeat split; intros; simpl in *; destruct H; eauto.
  - assert ((forall cf : config,
                    In cf (Config C st (m_lete x e1 e2) :: l) ->
                    In cf (Config C st (m_lete x e1 e2) :: l'))) as CONTAINED'.
    { intros. simpl in *. destruct H; eauto. }
    specialize (IHFUEL C st e1 (Config C st (m_lete x e1 e2) :: l) (Config C st (m_lete x e1 e2) :: l') CONTAINED') as IHl.
    clear CONTAINED'.
    destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL);
    destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l') FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHl as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct v; eauto. destruct st0.
    specialize (IHFUEL (C [|dy_c_lete x t ([||])|])
                       (ST (t !-> ev; mem) (tick t))
                       e2 reached reached0 CONTAINED'). clear CONTAINED'.
    destruct (eval (C [|dy_c_lete x t ([||])|])
                   (ST (t !-> ev; mem) (tick t))
                   e2 reached FUEL);
    destruct (eval (C [|dy_c_lete x t ([||])|])
                   (ST (t !-> ev; mem) (tick t))
                   e2 reached0 FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHFUEL as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *.
    destruct v; eauto.
  - assert ((forall cf : config,
                    In cf (Config C st (m_letm M e1 e2) :: l) ->
                    In cf (Config C st (m_letm M e1 e2) :: l'))) as CONTAINED'.
    { intros. simpl in *. destruct H; eauto. }
    specialize (IHFUEL C st e1 (Config C st (m_letm M e1 e2) :: l) (Config C st (m_letm M e1 e2) :: l') CONTAINED') as IHl.
    clear CONTAINED'.
    destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL);
    destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l') FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHl as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    destruct v; eauto.
    specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached reached0 CONTAINED'). clear CONTAINED'.
    destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached FUEL);
    destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 FUEL);
    try (assert False as contra; eauto; inversion contra); eauto.
    destruct IHFUEL as [RR [RR' CONTAINED']]. rewrite <- RR in *. rewrite <- RR' in *.
    destruct v; eauto.
Qed.

Lemma separate_reach :
  forall `{TIME : time T} FUEL (C : @dy_ctx T) st e l cf,
    In cf (extract_reached (eval C st e l FUEL)) <->
    In cf l \/ In cf (extract_reached (eval C st e [] FUEL)).
Proof.
  intros. rename H into ET. rename H0 into OT.
  revert C st e l cf. induction FUEL; intros; simpl; split; intros.
  - destruct H; eauto. 
  - destruct H as [?|[?|?]]; eauto. exfalso; eauto.
  - destruct e.
    + destruct (addr_x C x); destruct st; destruct (mem t); simpl in *;
      destruct H; eauto.
    + simpl in *; destruct H; eauto.
    + specialize (IHFUEL C st e1 (Config C st (e_app e1 e2) :: l) cf) as HINT1.
      specialize (IHFUEL C st e1 [Config C st (e_app e1 e2)] cf) as HINT1'.
      assert (forall cf, In cf [Config C st (e_app e1 e2)] ->
                         In cf (Config C st (e_app e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (e_app e1 e2)] (Config C st (e_app e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (e_app e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[?|?]|?]; eauto; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [[?|?]|?]; simpl in *; eauto).
      destruct ev. simpl in *.
      specialize (IHFUEL C st0 e2 reached cf) as HINT2.
      specialize (IHFUEL C st0 e2 reached0 cf) as HINT2'.
      pose proof (reach_same FUEL C st0 e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st0 e2 reached FUEL);
      destruct (eval C st0 e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[[?|?]|?]|?]; eauto; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT2 in H; rewrite HINT2'; rewrite HINT1 in H; rewrite HINT1';
          destruct H as [[[?|?]|?]|?]; simpl in *; eauto).
      destruct st2.
      specialize (IHFUEL (C0 [|dy_c_lam x t ([||])|])
                         (ST (t !-> ev; mem) (tick t)) 
                         e reached1 cf) as HINT3.
      specialize (IHFUEL (C0 [|dy_c_lam x t ([||])|])
                         (ST (t !-> ev; mem) (tick t)) 
                         e reached2 cf) as HINT3'.
      pose proof (reach_same FUEL (C0 [|dy_c_lam x t ([||])|])
                                  (ST (t !-> ev; mem) (tick t))
                                  e reached2 reached1 CONTAINED) as contra. clear CONTAINED.
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e
                     reached1 FUEL);
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e
                     reached2 FUEL);
      try (rewrite HINT3 in H); try rewrite HINT3';
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[[[?|?]|?]|?]|?]; eauto 7; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v; simpl in *;
      rewrite HINT3 in H; rewrite HINT3';
      rewrite HINT2 in H; rewrite HINT2';
      rewrite HINT1 in H; rewrite HINT1';
      destruct H as [[[[?|?]|?]|?]|?]; eauto 7.
    + specialize (IHFUEL C st e1 (Config C st (e_link e1 e2) :: l) cf) as HINT1.
      specialize (IHFUEL C st e1 [Config C st (e_link e1 e2)] cf) as HINT1'.
      assert (forall cf, In cf [Config C st (e_link e1 e2)] ->
                         In cf (Config C st (e_link e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (e_link e1 e2)] (Config C st (e_link e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (e_link e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[?|?]|?]; eauto; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [[?|?]|?]; simpl in *; eauto).
      specialize (IHFUEL mv st0 e2 reached cf) as HINT2.
      specialize (IHFUEL mv st0 e2 reached0 cf) as HINT2'.
      pose proof (reach_same FUEL mv st0 e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval mv st0 e2 reached FUEL);
      destruct (eval mv st0 e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[[?|?]|?]|?]; eauto; fail);
      try (inversion contra; fail).
    + simpl in *. destruct H; eauto.
    + destruct (ctx_M C M); simpl in *; destruct H; eauto.
    + specialize (IHFUEL C st e1 (Config C st (m_lete x e1 e2) :: l) cf) as HINT1.
      specialize (IHFUEL C st e1 [Config C st (m_lete x e1 e2)] cf) as HINT1'.
      assert (forall cf, In cf [Config C st (m_lete x e1 e2)] ->
                         In cf (Config C st (m_lete x e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (m_lete x e1 e2)] (Config C st (m_lete x e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (m_lete x e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[?|?]|?]; eauto; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [[?|?]|?]; simpl in *; eauto). destruct st0.
      specialize (IHFUEL (C [|dy_c_lete x t ([||])|])
                         (ST (t !-> ev; mem) (tick t))
                         e2 reached cf) as HINT2.
      specialize (IHFUEL (C [|dy_c_lete x t ([||])|])
                         (ST (t !-> ev; mem) (tick t))
                         e2 reached0 cf) as HINT2'.
      pose proof (reach_same FUEL (C [|dy_c_lete x t ([||])|])
                                  (ST (t !-> ev; mem) (tick t))
                                  e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e2 reached FUEL);
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[[?|?]|?]|?]; eauto; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v; rewrite HINT2 in H; try rewrite HINT2';
      rewrite HINT1 in H; try rewrite HINT1';
      simpl in *; destruct H as [[[?|?]|?]|?]; eauto.
    + specialize (IHFUEL C st e1 (Config C st (m_letm M e1 e2) :: l) cf) as HINT1.
      specialize (IHFUEL C st e1 [Config C st (m_letm M e1 e2)] cf) as HINT1'.
      assert (forall cf, In cf [Config C st (m_letm M e1 e2)] ->
                         In cf (Config C st (m_letm M e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (m_letm M e1 e2)] (Config C st (m_letm M e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (m_letm M e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[?|?]|?]; eauto; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [[?|?]|?]; simpl in *; eauto).
      specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached cf) as HINT2.
      specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 cf) as HINT2'.
      pose proof (reach_same FUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached FUEL);
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [[[?|?]|?]|?]; eauto; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v; rewrite HINT2 in H; rewrite HINT2';
      rewrite HINT1 in H; rewrite HINT1';
      simpl in *; destruct H as [[[?|?]|?]|?]; eauto.
  - destruct e.
    + destruct (addr_x C x); destruct st; destruct (mem t); simpl in *; destruct H as [?|[?|?]]; eauto; inversion H.
    + simpl in *; destruct H as [?|[?|?]]; eauto; inversion H.
    + specialize (IHFUEL C st e1 (Config C st (e_app e1 e2) :: l) cf) as HINT1'.
      specialize (IHFUEL C st e1 [Config C st (e_app e1 e2)] cf) as HINT1.
      assert (forall cf, In cf [Config C st (e_app e1 e2)] ->
                         In cf (Config C st (e_app e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (e_app e1 e2)] (Config C st (e_app e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (e_app e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (e_app e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[?|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [?|[[?|?]|?]]; simpl in *; eauto; inversion H).
      destruct ev. simpl in *.
      specialize (IHFUEL C st0 e2 reached cf) as HINT2'.
      specialize (IHFUEL C st0 e2 reached0 cf) as HINT2.
      pose proof (reach_same FUEL C st0 e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st0 e2 reached FUEL);
      destruct (eval C st0 e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[[?|?]|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT2 in H; rewrite HINT2'; rewrite HINT1 in H; rewrite HINT1';
          destruct H as [?|[[[?|?]|?]|?]]; simpl in *; eauto; inversion H).
      destruct st2.
      specialize (IHFUEL (C0 [|dy_c_lam x t ([||])|])
                         (ST (t !-> ev; mem) (tick t)) 
                         e reached1 cf) as HINT3'.
      specialize (IHFUEL (C0 [|dy_c_lam x t ([||])|])
                         (ST (t !-> ev; mem) (tick t)) 
                         e reached2 cf) as HINT3.
      pose proof (reach_same FUEL (C0 [|dy_c_lam x t ([||])|])
                                  (ST (t !-> ev; mem) (tick t))
                                  e reached2 reached1 CONTAINED) as contra. clear CONTAINED.
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e
                     reached1 FUEL);
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t)) e
                     reached2 FUEL);
      try (rewrite HINT3 in H); try rewrite HINT3';
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[[[?|?]|?]|?]|?]]; eauto 7; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v; simpl in *;
      rewrite HINT3 in H; rewrite HINT3';
      rewrite HINT2 in H; rewrite HINT2';
      rewrite HINT1 in H; rewrite HINT1';
      destruct H as [?|[[[[?|?]|?]|?]|?]]; eauto 7; inversion H.
    + specialize (IHFUEL C st e1 (Config C st (e_link e1 e2) :: l) cf) as HINT1'.
      specialize (IHFUEL C st e1 [Config C st (e_link e1 e2)] cf) as HINT1.
      assert (forall cf, In cf [Config C st (e_link e1 e2)] ->
                         In cf (Config C st (e_link e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (e_link e1 e2)] (Config C st (e_link e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (e_link e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (e_link e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[?|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [?|[[?|?]|?]]; simpl in *; eauto; inversion H).
      specialize (IHFUEL mv st0 e2 reached cf) as HINT2'.
      specialize (IHFUEL mv st0 e2 reached0 cf) as HINT2.
      pose proof (reach_same FUEL mv st0 e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval mv st0 e2 reached FUEL);
      destruct (eval mv st0 e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[[?|?]|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
    + simpl in *. destruct H as [?|[?|?]]; eauto; inversion H.
    + destruct (ctx_M C M); simpl in *; destruct H as [?|[?|?]]; eauto; inversion H.
    + specialize (IHFUEL C st e1 (Config C st (m_lete x e1 e2) :: l) cf) as HINT1'.
      specialize (IHFUEL C st e1 [Config C st (m_lete x e1 e2)] cf) as HINT1.
      assert (forall cf, In cf [Config C st (m_lete x e1 e2)] ->
                         In cf (Config C st (m_lete x e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (m_lete x e1 e2)] (Config C st (m_lete x e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (m_lete x e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (m_lete x e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[?|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [?|[[?|?]|?]]; simpl in *; eauto; inversion H). destruct st0.
      specialize (IHFUEL (C [|dy_c_lete x t ([||])|])
                         (ST (t !-> ev; mem) (tick t))
                         e2 reached cf) as HINT2'.
      specialize (IHFUEL (C [|dy_c_lete x t ([||])|])
                         (ST (t !-> ev; mem) (tick t))
                         e2 reached0 cf) as HINT2.
      pose proof (reach_same FUEL (C [|dy_c_lete x t ([||])|])
                                  (ST (t !-> ev; mem) (tick t))
                                  e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e2 reached FUEL);
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[[?|?]|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v; rewrite HINT2 in H; try rewrite HINT2';
      rewrite HINT1 in H; try rewrite HINT1';
      simpl in *; destruct H as [?|[[[?|?]|?]|?]]; eauto; inversion H.
    + specialize (IHFUEL C st e1 (Config C st (m_letm M e1 e2) :: l) cf) as HINT1'.
      specialize (IHFUEL C st e1 [Config C st (m_letm M e1 e2)] cf) as HINT1.
      assert (forall cf, In cf [Config C st (m_letm M e1 e2)] ->
                         In cf (Config C st (m_letm M e1 e2) :: l)) as CONTAINED.
      { intros; simpl in *; destruct H0; eauto. inversion H0. }
      pose proof (reach_same FUEL C st e1 [Config C st (m_letm M e1 e2)] (Config C st (m_letm M e1 e2) :: l) CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval C st e1 (Config C st (m_letm M e1 e2) :: l) FUEL);
      destruct (eval C st e1 [Config C st (m_letm M e1 e2)] FUEL);
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[?|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v;
      try (rewrite HINT1 in H; rewrite HINT1'; destruct H as [?|[[?|?]|?]]; simpl in *; eauto; inversion H).
      specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached cf) as HINT2'.
      specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 cf) as HINT2.
      pose proof (reach_same FUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 reached CONTAINED) as contra.
      clear CONTAINED.
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached FUEL);
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached0 FUEL);
      try (rewrite HINT2 in H); try rewrite HINT2';
      try (rewrite HINT1 in H); try rewrite HINT1';
      try (simpl in *; destruct H as [?|[[[?|?]|?]|?]]; eauto; inversion H; fail);
      try (inversion contra; fail).
      destruct contra as [RR [RR' CONTAINED]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct v; rewrite HINT2 in H; rewrite HINT2';
      rewrite HINT1 in H; rewrite HINT1';
      simpl in *; destruct H as [?|[[[?|?]|?]|?]]; eauto; inversion H.
Qed.

Lemma ReachR_well_defined_l :
  forall `{TIME : time T} (C : @dy_ctx T) st e C' st' e' (R : <| C st e ~> C' st' e' |>),
    exists FUEL,
      In (Config C' st' e') (extract_reached (eval C st e [] FUEL)).
Proof.
  intros. rename H into ET. rename H0 into OT.
  induction R.
  - exists 1. destruct e; simpl; eauto.
    destruct (addr_x C x); destruct st; destruct (mem t); simpl; eauto.
    destruct (ctx_M C M); simpl; eauto.
  - destruct IHR as [FUEL CONTAINED].
    exists (S FUEL). simpl.
    destruct (eval C st e1 [Config C st (e_app e1 e2)] FUEL) eqn:EVAL1;
    try (rewrite <- EVAL1; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v st0 reached))).
    { rewrite <- EVAL1; rewrite separate_reach; eauto. }
    destruct v; simpl in *; eauto. destruct ev.
    destruct (eval C st0 e2 reached FUEL) eqn:EVAL2;
    try (rewrite <- EVAL2; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v st1 reached0))).
    { rewrite <- EVAL2; rewrite separate_reach; eauto. }
    destruct v; simpl in *; eauto. destruct st1.
    destruct (eval (C0 [|dy_c_lam x t ([||])|])
                   (ST (t !-> ev; mem) (tick t))
                   e reached0 FUEL) eqn:EVAL3;
    try (rewrite <- EVAL3; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v st1 reached1))).
    { rewrite <- EVAL3; rewrite separate_reach; eauto. }
    destruct v; simpl in *; eauto.
  - destruct IHR as [FUEL CONTAINED].
    pose proof (EvalR_well_defined_l C st e1 [Config C st (e_app e1 e2)] (EVal (Closure x e C_lam)) st_lam FN).
    destruct H as [FUEL' CONTAINED'].
    exists (S (Nat.max FUEL FUEL')). simpl.
    destruct (eval C st e1 [Config C st (e_app e1 e2)] FUEL') eqn:EVAL1;
    try (inversion CONTAINED'; fail).
    destruct CONTAINED' as [RR RR']. rewrite <- RR in *. rewrite RR' in *. clear RR RR'.
    assert (eval C st e1 [Config C st (e_app e1 e2)] (Nat.max FUEL FUEL') = Resolved (EVal (Closure x e C_lam)) st0 reached) as RR.
    { apply relax_fuel with (FUEL := FUEL'). nia. eauto. }
    rewrite RR. clear RR.
    destruct (eval C st0 e2 reached (Nat.max FUEL FUEL')) eqn:EVAL2;
    try (rewrite <- EVAL2; rewrite separate_reach; right; 
        apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto).    
    assert (In (Config C' st' e') (extract_reached (Resolved v0 st1 reached0))).
    { rewrite <- EVAL2; rewrite separate_reach.
      right. apply relax_fuel_reach with (FUEL := FUEL). nia. eauto. }
    destruct v0; simpl in *; eauto. destruct st1.
    destruct (eval (C_lam [|dy_c_lam x t ([||])|])
                   (ST (t !-> ev; mem) (tick t))
                   e reached0 (Nat.max FUEL FUEL')) eqn:EVAL3;
    try (rewrite <- EVAL3; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v0 st1 reached1))).
    { rewrite <- EVAL3; rewrite separate_reach; eauto. }
    destruct v0; simpl in *; eauto.
  - destruct IHR as [FUEL CONTAINED].
    pose proof (EvalR_well_defined_l C st e1 [Config C st (e_app e1 e2)] (EVal (Closure x e C_lam)) st_lam FN).
    destruct H as [FUEL' CONTAINED'].
    destruct (eval C st e1 [Config C st (e_app e1 e2)] FUEL') eqn:EVAL1;
    try (inversion CONTAINED'; fail).
    destruct CONTAINED' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    pose proof (EvalR_well_defined_l C st_lam e2 reached (EVal arg) (ST mem t) ARG).
    destruct H as [FUEL'' CONTAINED''].
    destruct (eval C st_lam e2 reached FUEL'') eqn:EVAL2;
    try (inversion CONTAINED''; fail).
    destruct CONTAINED'' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    exists (S (Nat.max FUEL (Nat.max FUEL' FUEL''))).
    simpl.
    assert (eval C st e1 [Config C st (e_app e1 e2)]
                (Nat.max FUEL (Nat.max FUEL' FUEL'')) = Resolved (EVal (Closure x e C_lam)) st_lam reached) as RR.
    { apply relax_fuel with (FUEL := FUEL'). nia. eauto. } 
    rewrite RR. clear RR.
    assert (eval C st_lam e2 reached (Nat.max FUEL (Nat.max FUEL' FUEL'')) = Resolved (EVal arg) (ST mem t) reached0) as RR.
    { apply relax_fuel with (FUEL := FUEL''). nia. eauto. }
    rewrite RR. clear RR.
    destruct (eval (C_lam [|dy_c_lam x t ([||])|])
                   (ST (t !-> arg; mem) (tick t))
                   e reached0 (Nat.max FUEL (Nat.max FUEL' FUEL''))) eqn:EVAL3;
    try (rewrite <- EVAL3; apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto;
         rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v1 st2 reached1))).
    { rewrite <- EVAL3; rewrite separate_reach; eauto. right.
      apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto. }
    destruct v1; simpl in *; eauto.
  - destruct IHR as [FUEL CONTAINED].
    exists (S FUEL). simpl.
    assert (In (Config C' st' e') (extract_reached (eval C st m [Config C st (e_link m e)] FUEL))).
    { rewrite separate_reach. eauto. }
    destruct (eval C st m [Config C st (e_link m e)] FUEL) eqn:EVAL; eauto.
    destruct v; eauto.
    assert (In (Config C' st' e') (extract_reached (eval mv st0 e reached FUEL))).
    { rewrite separate_reach. simpl in *. eauto. }
    destruct (eval mv st0 e reached FUEL) eqn:EVAL2; eauto.
  - destruct IHR as [FUEL CONTAINED].
    pose proof (EvalR_well_defined_l C st m [Config C st (e_link m e)] (MVal C_m) st_m MOD).
    destruct H as [FUEL' CONTAINED'].
    destruct (eval C st m [Config C st (e_link m e)] FUEL') eqn:EVAL1;
    try (inversion CONTAINED'; fail).
    destruct CONTAINED' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    exists (S (Nat.max FUEL FUEL')).
    assert (eval C st m [Config C st (e_link m e)] (Nat.max FUEL FUEL') = Resolved (MVal C_m) st_m reached) as RR.
    { apply relax_fuel with (FUEL := FUEL'). nia. eauto. }
    simpl. rewrite RR. clear RR.
    destruct (eval C_m st_m e reached (Nat.max FUEL FUEL')) eqn:EVAL2;
    try (rewrite <- EVAL2; rewrite separate_reach; right;
        apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto).
  - destruct IHR as [FUEL CONTAINED].
    exists (S FUEL). simpl.
    destruct (eval C st e [Config C st (m_lete x e m)] FUEL) eqn:EVAL1;
    try (rewrite <- EVAL1; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v st0 reached))).
    { rewrite <- EVAL1; rewrite separate_reach; eauto. }
    destruct v; simpl in *; eauto. destruct st0.
    destruct (eval (C [|dy_c_lete x t ([||])|])
                   (ST (t !-> ev; mem) (tick t))
                   m reached FUEL) eqn:EVAL2;
    try (rewrite <- EVAL2; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v st0 reached0))).
    { rewrite <- EVAL2; rewrite separate_reach; eauto. }
    destruct v; simpl in *; eauto.
  - destruct IHR as [FUEL CONTAINED].
    pose proof (EvalR_well_defined_l C st e [Config C st (m_lete x e m)] (EVal v) (ST mem t) EVALx).
    destruct H as [FUEL' CONTAINED'].
    destruct (eval C st e [Config C st (m_lete x e m)] FUEL') eqn:EVAL1;
    try (inversion CONTAINED'; fail).
    destruct CONTAINED' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    exists (S (Nat.max FUEL FUEL')).
    assert (eval C st e [Config C st (m_lete x e m)] (Nat.max FUEL FUEL') = Resolved (EVal v) (ST mem t) reached) as RR.
    { apply relax_fuel with (FUEL := FUEL'). nia. eauto. }
    simpl. rewrite RR. clear RR.
    destruct (eval (C [|dy_c_lete x t ([||])|])
                   (ST (t !-> v; mem) (tick t))
                   m reached (Nat.max FUEL FUEL')) eqn:EVAL2;
    try (rewrite <- EVAL2; apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto;
         rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v1 st1 reached0))).
    { rewrite <- EVAL2; rewrite separate_reach; eauto. right.
      apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto. }
    destruct v1; simpl in *; eauto.
  - destruct IHR as [FUEL CONTAINED].
    exists (S FUEL). simpl.
    destruct (eval C st m1 [Config C st (m_letm M m1 m2)] FUEL) eqn:EVAL1;
    try (rewrite <- EVAL1; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v st0 reached))).
    { rewrite <- EVAL1; rewrite separate_reach; eauto. }
    destruct v; simpl in *; eauto. destruct st0.
    destruct (eval (C [|dy_c_letm M mv ([||])|]) (ST mem t) m2 reached FUEL) eqn:EVAL2;
    try (rewrite <- EVAL2; rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v st0 reached0))).
    { rewrite <- EVAL2; rewrite separate_reach; eauto. }
    destruct v; simpl in *; eauto.
  - destruct IHR as [FUEL CONTAINED].
    pose proof (EvalR_well_defined_l C st m1 [Config C st (m_letm M m1 m2)] (MVal C_M) st_M EVALM).
    destruct H as [FUEL' CONTAINED'].
    destruct (eval C st m1 [Config C st (m_letm M m1 m2)] FUEL') eqn:EVAL1;
    try (inversion CONTAINED'; fail).
    destruct CONTAINED' as [RR RR']. rewrite <- RR in *. rewrite <- RR' in *. clear RR RR'.
    exists (S (Nat.max FUEL FUEL')).
    assert (eval C st m1 [Config C st (m_letm M m1 m2)] (Nat.max FUEL FUEL') = Resolved (MVal C_M) st_M reached) as RR.
    { apply relax_fuel with (FUEL := FUEL'). nia. eauto. }
    simpl. rewrite RR. clear RR.
    destruct (eval (C [|dy_c_letm M C_M ([||])|]) st_M m2 reached (Nat.max FUEL FUEL')) eqn:EVAL2;
    try (rewrite <- EVAL2; apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto;
         rewrite separate_reach; eauto).
    assert (In (Config C' st' e') (extract_reached (Resolved v0 st1 reached0))).
    { rewrite <- EVAL2; rewrite separate_reach; eauto. right.
      apply relax_fuel_reach with (FUEL := FUEL); try nia; eauto. }
    destruct v0; simpl in *; eauto.
Qed.

Lemma ReachR_well_defined_r :
  forall `{TIME : time T} FUEL (C : @dy_ctx T) st e C' st' e'
         (R : In (Config C' st' e') (extract_reached (eval C st e [] FUEL))),
  <| C st e ~> C' st' e' |>.
Proof.
  intros. rename H into ET. rename H0 into OT.
  revert C st e C' st' e' R.
  induction FUEL; intros; simpl in *.
  - destruct R as [R | R]; inversion R; eauto.
  - destruct e.
    + destruct (addr_x C x); destruct st; destruct (mem t); simpl in *;
      destruct R as [R | R]; inversion R; eauto.
    + simpl in *. destruct R as [R | R]; inversion R; eauto.
    + destruct (eval C st e1 [Config C st (e_app e1 e2)] FUEL) eqn:EVAL1;
      try (rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
      destruct v. all:cycle 1.
      simpl in *. replace reached with (extract_reached (Resolved (MVal mv) st0 reached)) in R by reflexivity.
      rewrite <- EVAL1 in R. rewrite separate_reach in R. simpl in *.
      destruct R as [[R|R]|R]; try inversion R; eauto.
      destruct ev.
      pose proof (EvalR_well_defined_r FUEL C st e1 [Config C st (e_app e1 e2)] (EVal (Closure x e C0)) st0).
      rewrite EVAL1 in H. 
      assert (EvalR C st e1 (EVal (Closure x e C0)) st0) as FN. 
      eauto. clear H.
      destruct (eval C st0 e2 reached FUEL) eqn:EVAL2;
      try (rewrite <- EVAL2 in R; eauto; rewrite separate_reach in R; simpl in *;
           destruct R as [R|R]; eauto;
           replace reached with (extract_reached (Resolved (EVal (Closure x e C0)) st0 reached)) in R by reflexivity;
           rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
      destruct v. all:cycle 1.
      simpl in *. replace reached0 with (extract_reached (Resolved (MVal mv) st1 reached0)) in R by reflexivity.
      rewrite <- EVAL2 in R. rewrite separate_reach in R. simpl in *.
      replace reached with (extract_reached (Resolved (EVal (Closure x e C0)) st0 reached)) in R by reflexivity.
      rewrite <- EVAL1 in R. rewrite separate_reach in R. simpl in *.
      destruct R as [[[R|R]|R]|R]; try inversion R; eauto.
      destruct st1.
      pose proof (EvalR_well_defined_r FUEL C st0 e2 reached (EVal ev) (ST mem t)).
      rewrite EVAL2 in H.
      assert (EvalR C st0 e2 (EVal ev) (ST mem t)) as ARG.
      eauto. clear H.
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e reached0 FUEL) eqn:EVAL3;
      try (rewrite <- EVAL3 in R; eauto; rewrite separate_reach in R; simpl in *;
           destruct R as [R|R]; eauto;
           replace reached0 with (extract_reached (Resolved (EVal ev) (ST mem t) reached0)) in R by reflexivity;
           rewrite <- EVAL2 in R; rewrite separate_reach in R; simpl in *;
           replace reached with (extract_reached (Resolved (EVal (Closure x e C0)) st0 reached)) in R by reflexivity;
           rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[[R|R]|R]|R]; try inversion R; eauto).
      replace reached1 with (extract_reached (Resolved v st1 reached1)) in R by reflexivity;
      rewrite <- EVAL3 in R.
      destruct v; simpl in *; rewrite separate_reach in R;
      replace reached0 with (extract_reached (Resolved (EVal ev) (ST mem t) reached0)) in R by reflexivity;
      rewrite <- EVAL2 in R; rewrite separate_reach in R; simpl in *;
      replace reached with (extract_reached (Resolved (EVal (Closure x e C0)) st0 reached)) in R by reflexivity;
      rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
      destruct R as [[[[R|R]|R]|R]|R]; try inversion R; eauto.
    + destruct (eval C st e1 [Config C st (e_link e1 e2)] FUEL) eqn:EVAL1;
      try (rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
      destruct v.
      simpl in *. replace reached with (extract_reached (Resolved (EVal ev) st0 reached)) in R by reflexivity.
      rewrite <- EVAL1 in R. rewrite separate_reach in R. simpl in *.
      destruct R as [[R|R]|R]; try inversion R; eauto.
      pose proof (EvalR_well_defined_r FUEL C st e1 [Config C st (e_link e1 e2)] (MVal mv) st0).
      rewrite EVAL1 in H.
      assert (EvalR C st e1 (MVal mv) st0) as MOD. 
      eauto. clear H.
      destruct (eval mv st0 e2 reached FUEL) eqn:EVAL2;
      try (rewrite <- EVAL2 in R; eauto; rewrite separate_reach in R; simpl in *;
           destruct R as [R|R]; eauto;
           replace reached with (extract_reached (Resolved (MVal mv) st0 reached)) in R by reflexivity;
           rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
    + simpl in *. destruct R as [R|R]; inversion R; eauto.
    + destruct (ctx_M C M); simpl in *; destruct R as [R|R]; inversion R; eauto.
    + destruct (eval C st e1 [Config C st (m_lete x e1 e2)] FUEL) eqn:EVAL1;
      try (rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
      destruct v. all:cycle 1.
      simpl in *. replace reached with (extract_reached (Resolved (MVal mv) st0 reached)) in R by reflexivity.
      rewrite <- EVAL1 in R. rewrite separate_reach in R. simpl in *.
      destruct R as [[R|R]|R]; try inversion R; eauto.
      destruct ev.
      pose proof (EvalR_well_defined_r FUEL C st e1 [Config C st (m_lete x e1 e2)] (EVal (Closure x0 e C0)) st0).
      rewrite EVAL1 in H. 
      assert (EvalR C st e1 (EVal (Closure x0 e C0)) st0) as EVALx.
      eauto. clear H. destruct st0.
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> Closure x0 e C0; mem) (tick t))
                     e2 reached FUEL) eqn:EVAL2;
      try (rewrite <- EVAL2 in R; eauto; rewrite separate_reach in R; simpl in *;
           destruct R as [R|R]; eauto;
           replace reached with (extract_reached (Resolved (EVal (Closure x0 e C0)) (ST mem t) reached)) in R by reflexivity;
           rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
      destruct v; simpl in *;
      try (replace reached0 with (extract_reached (Resolved (EVal ev) st0 reached0)) in R by reflexivity);
      try (replace reached0 with (extract_reached (Resolved (MVal mv) st0 reached0)) in R by reflexivity);
      rewrite <- EVAL2 in R; rewrite separate_reach in R; simpl in *;
      replace reached with (extract_reached (Resolved (EVal (Closure x0 e C0)) (ST mem t) reached)) in R by reflexivity;
      rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
      destruct R as [[[R|R]|R]|R]; try inversion R; eauto.
    + destruct (eval C st e1 [Config C st (m_letm M e1 e2)] FUEL) eqn:EVAL1;
      try (rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
      destruct v.
      simpl in *. replace reached with (extract_reached (Resolved (EVal ev) st0 reached)) in R by reflexivity.
      rewrite <- EVAL1 in R. rewrite separate_reach in R. simpl in *.
      destruct R as [[R|R]|R]; try inversion R; eauto.
      pose proof (EvalR_well_defined_r FUEL C st e1 [Config C st (m_letm M e1 e2)] (MVal mv) st0).
      rewrite EVAL1 in H. 
      assert (EvalR C st e1 (MVal mv) st0) as EVALm.
      eauto. clear H.
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached FUEL) eqn:EVAL2;
      try (rewrite <- EVAL2 in R; eauto; rewrite separate_reach in R; simpl in *;
           destruct R as [R|R]; eauto;
           replace reached with (extract_reached (Resolved (MVal mv) st0 reached)) in R by reflexivity;
           rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
           destruct R as [[R|R]|R]; try inversion R; eauto).
      destruct v; simpl in *;
      try (replace reached0 with (extract_reached (Resolved (EVal ev) st1 reached0)) in R by reflexivity);
      try (replace reached0 with (extract_reached (Resolved (MVal mv0) st1 reached0)) in R by reflexivity);
      rewrite <- EVAL2 in R; rewrite separate_reach in R; simpl in *;
      replace reached with (extract_reached (Resolved (MVal mv) st0 reached)) in R by reflexivity;
      rewrite <- EVAL1 in R; rewrite separate_reach in R; simpl in *;
      destruct R as [[[R|R]|R]|R]; try inversion R; eauto.
Qed.

Theorem ReachR_well_defined :
  forall `{TIME : time T} (C : @dy_ctx T) st e C' st' e',
    (exists FUEL, In (Config C' st' e') (extract_reached (eval C st e [] FUEL))) <->
    <| C st e ~> C' st' e' |>.
Proof.
  intros. rename H into ET. rename H0 into OT.
  split; try apply ReachR_well_defined_l.
  intros. destruct H as [FUEL CONTAINED].
  apply ReachR_well_defined_r with (FUEL := FUEL). eauto.
Qed.

Lemma eval_then_reach :
  forall `{TIME : time T} FUEL C st e,
    match eval C st e [] FUEL with
    | Resolved v st' reached =>
      exists C' e',
      In (Config C' st' e') reached /\
      eval C' st' e' [] 1 = Resolved v st' [Config C' st' e']
    | _ => True
    end.
Proof.
  assert (forall {X} (l : list X) cf, In cf [] -> In cf l) as HINT.
  simpl; intros; inversion H.
  intros. rename H into ET. rename H0 into OT.
  revert C st e. induction FUEL.
  - intros. simpl. eauto.
  - intros. destruct e; simpl.
    + destruct (addr_x C x) eqn:ADDR; destruct st; destruct (mem t) eqn:ACCESS; eauto.
      exists C. exists (e_var x). split; simpl; eauto.
      rewrite ADDR. rewrite ACCESS. eauto.
    + exists C. exists (e_lam x e). eauto.
    + destruct (eval C st e1 [Config C st (e_app e1 e2)] FUEL) eqn:FN; eauto.
      destruct v; eauto. destruct ev.
      destruct (eval C st0 e2 reached FUEL) eqn:ARG; eauto.
      destruct v; eauto. destruct st1.
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e reached0 FUEL) eqn:BODY; eauto.
      destruct v; eauto.
      pose proof (reach_same FUEL (C0 [|dy_c_lam x t ([||])|])
                                  (ST (t !-> ev; mem) (tick t))
                                  e [] reached0 (HINT _ reached0)) as R.
      rewrite BODY in R.
      destruct (eval (C0 [|dy_c_lam x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e [] FUEL) eqn:BODY'; try (inversion R; fail).
      specialize (IHFUEL (C0 [|dy_c_lam x t ([||])|])
                         (ST (t !-> ev; mem) (tick t))
                         e). rewrite BODY' in IHFUEL.
      destruct R as [RR [RR' R]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct IHFUEL as [C' [e' [CONTAINED EVAL]]].
      exists C'. exists e'. eauto.
    + destruct (eval C st e1 [Config C st (e_link e1 e2)] FUEL) eqn:MOD; eauto.
      destruct v; eauto.
      destruct (eval mv st0 e2 reached FUEL) eqn:BODY; eauto.
      pose proof (reach_same FUEL mv st0 e2 [] reached (HINT _ reached)) as R.
      rewrite BODY in R.
      destruct (eval mv st0 e2 []) eqn:BODY'; try (inversion R; fail).
      specialize (IHFUEL mv st0 e2). rewrite BODY' in IHFUEL.
      destruct R as [RR [RR' R]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct IHFUEL as [C' [e' [CONTAINED EVAL]]].
      exists C'. exists e'. eauto.
    + exists C. exists m_empty. eauto.
    + destruct (ctx_M C M) eqn:ACCESS; eauto.
      exists C. exists (m_var M). rewrite ACCESS. simpl in *; eauto.
    + destruct (eval C st e1 [Config C st (m_lete x e1 e2)] FUEL) eqn:EVALx; eauto.
      destruct v; eauto. destruct st0.
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e2 reached FUEL) eqn:BODY; eauto.
      pose proof (reach_same FUEL (C [|dy_c_lete x t ([||])|])
                                  (ST (t !-> ev; mem) (tick t))
                                  e2 [] reached (HINT _ reached)) as R.
      rewrite BODY in R.
      destruct (eval (C [|dy_c_lete x t ([||])|])
                     (ST (t !-> ev; mem) (tick t))
                     e2 []) eqn:BODY'; try (inversion R; fail).
      specialize (IHFUEL (C [|dy_c_lete x t ([||])|])
                         (ST (t !-> ev; mem) (tick t))
                         e2). rewrite BODY' in IHFUEL.
      destruct R as [RR [RR' R]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct IHFUEL as [C' [e' [CONTAINED EVAL]]].
      destruct v; eauto.
    + destruct (eval C st e1 [Config C st (m_letm M e1 e2)] FUEL) eqn:EVALM; eauto.
      destruct v; eauto.
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 reached FUEL) eqn:BODY; eauto.
      pose proof (reach_same FUEL (C [|dy_c_letm M mv ([||])|]) st0 e2 [] reached (HINT _ reached)) as R.
      rewrite BODY in R.
      destruct (eval (C [|dy_c_letm M mv ([||])|]) st0 e2 []) eqn:BODY'; try (inversion R; fail).
      specialize (IHFUEL (C [|dy_c_letm M mv ([||])|]) st0 e2). rewrite BODY' in IHFUEL.
      destruct R as [RR [RR' R]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct IHFUEL as [C' [e' [CONTAINED EVAL]]].
      destruct v; eauto.
Qed.

(* well-definedness *)
Corollary EvalR_then_ReachR :
  forall `{TIME : time T} C st e v st'
         (R : EvalR C st e v st'),
    exists C' e',
      <| C st e ~> C' st' e' |> /\
      eval C' st' e' [] 1 = Resolved v st' [Config C' st' e'].
Proof.
  intros. rewrite <- (EvalR_well_defined []) in R.
  destruct R as [FUEL R].
  destruct (eval C st e [] FUEL) eqn:EVAL;
  try (inversion R; fail).
  destruct R as [RR RR']. rewrite RR in *. rewrite RR' in *. clear RR RR'.
  pose proof (eval_then_reach FUEL C st e) as EXACT.
  rewrite EVAL in EXACT. destruct EXACT as [C' [e' [REACH EXACT]]].
  replace reached with (extract_reached (Resolved v0 st0 reached)) in REACH by reflexivity.
  rewrite <- EVAL in REACH.
  assert (<| C st e ~> C' st0 e' |>).
  { rewrite <- ReachR_well_defined. exists FUEL. eauto. }
  exists C'. exists e'. eauto.
Qed. 

Lemma value_reach_only_itself :
  forall `{TIME : time T} C st v (pf : value v)
         C' st' e'
         (REACH : <| C st v ~> C' st' e' |>),
         C = C' /\ st = st' /\ v = e'.
Proof.
  intros; repeat split; inversion pf; inversion REACH; subst; eauto;
  try inversion H2.
Qed.
