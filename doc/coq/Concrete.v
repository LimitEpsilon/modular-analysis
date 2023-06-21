From MODULAR Require Export Syntax.

Generalizable Variables T.

Inductive state {T : Type} :=
  | ST (mem : T -> option (@expr_value T))
       (t : T)
.

Class time `{OrderT T} :=
{  
  update : (@dy_ctx T) -> (@state T) -> expr_id -> (@expr_value T) -> T;
  update_lt : forall C mem t x v, let t' := update C (ST mem t) x v in
                                  leb t t' = true /\ eqb t t' = false
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
                           (ST (t !-> arg ; mem) 
                               (update C (ST mem t) x arg))
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
                        (ST (t !-> v ; mem) 
                            (update C (ST mem t) x v))
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

Inductive interpreter_state {T} :=
  | Pending (C : @dy_ctx T) (st : @state T) (e : tm)
  | Error (C : @dy_ctx T) (st : @state T) (e : tm) (* Type error *)
  | Resolved (v : @dy_value T) (st : @state T)
.

Fixpoint eval `{time T} (C : @dy_ctx T) (st : @state T) 
              (e : tm) (FUEL : nat) :=
  match FUEL with
  | 0 => Pending C st e
  | S FUEL' =>
    match e with
    | e_var x =>
      match addr_x C x with
      | None => Error C st e
      | Some addr => 
        match st with
        | ST mem _ =>
          match mem addr with
          | None => Pending C st e
          | Some v => Resolved (EVal v) st
          end
        end
      end
    | e_lam x e' =>
      Resolved (EVal (Closure x e' C)) st
    | e_app e1 e2 =>
      match eval C st e1 FUEL' with
      | Resolved (EVal (Closure x e' C_lam)) st_lam =>
        match eval C st_lam e2 FUEL' with
        | Resolved (EVal arg) (ST mem t) =>
          match eval (C_lam [| dy_c_lam x t ([||]) |]) 
                     (ST (t !-> arg ; mem) 
                         (update C (ST mem t) x arg)) 
                     e' FUEL' with
          | Resolved (EVal v) st' => Resolved (EVal v) st'
          | Resolved _ _ => Error C st e
          | other => other
          end
        | Resolved _ _ => Error C st e
        | other => other
        end
      | Resolved _ _ => Error C st e
      | other => other
      end
    | e_link m e' =>
      match eval C st m FUEL' with
      | Resolved (MVal C_m) st_m =>
        match eval C_m st_m e' FUEL' with
        | Resolved v st' => Resolved v st'
        | other => other
        end
      | Resolved _ _ => Error C st e
      | other => other
      end
    | m_empty => Resolved (MVal C) st
    | m_var M =>
      match ctx_M C M with
      | None => Pending C st e
      | Some C_M => Resolved (MVal C_M) st
      end
    | m_lete x e m =>
      match eval C st e FUEL' with
      | Resolved (EVal v) (ST mem t) =>
        match eval (C[| dy_c_lete x t ([||]) |]) 
                   (ST (t !-> v ; mem) 
                       (update C (ST mem t) x v)) 
                   m FUEL' with
        | Resolved (MVal C') st' => Resolved (MVal C') st'
        | Resolved _ _ => Error C st e 
        | other => other
        end
      | Resolved _ _ => Error C st e
      | other => other
      end
    | m_letm M m1 m2 =>
      match eval C st m1 FUEL' with
      | Resolved (MVal C') st' =>
        match eval (C[| dy_c_letm M C' ([||]) |])
                   st' m2 FUEL' with
        | Resolved (MVal C'') st'' => Resolved (MVal C'') st''
        | Resolved _ _ => Error C st e
        | other => other
        end
      | Resolved _ _ => Error C st e
      | other => other
      end
    end
  end.

Lemma relax_fuel :
  forall `{TIME : time T} (C : @dy_ctx T) st e v st' FUEL FUEL' (LE : FUEL <= FUEL'),
    eval C st e FUEL = Resolved v st' ->
    eval C st e FUEL' = Resolved v st'.
Proof.
  intros. rename H into H'. rename H0 into H''. rename H1 into H.
  revert C st e v st' H FUEL' LE.
  induction FUEL; intros.
  - inversion H.
  - simpl in H; destruct e; inversion LE; eauto.
    + remember (eval C st e1 FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      clear H3. destruct v1 as [x v1 C_lam].
      remember (eval C st1 e2 FUEL) as v2.
      destruct v2 as [ | | v2 st2]; inversion H;
      clear H3. destruct v2 as [v2 | ]; inversion H.
      clear H3. destruct st2 as [mem2 t2].
      remember (eval (C_lam [|dy_c_lam x t2 ([||])|]) 
                     (ST (t2 !-> v2; mem2) (update C (ST mem2 t2) x v2))
                      v1 FUEL) as v3.
      destruct v3 as [ | | v3 st3]; inversion H.
      clear H3. destruct v3 as [v3 | ]; inversion H.
      subst. 
      assert (eval C st e1 m = Resolved (EVal (Closure x v1 C_lam)) st1) as RR1.
      apply IHFUEL; eauto. nia.
      assert (eval C st1 e2 m = Resolved (EVal v2) (ST mem2 t2)) as RR2.
      apply IHFUEL; eauto. nia.
      assert (eval (C_lam [|dy_c_lam x t2 ([||])|])
                   (ST (t2 !-> v2; mem2) (update C (ST mem2 t2) x v2)) v1 m = 
              Resolved (EVal v3) st') as RR3.
      apply IHFUEL; eauto. nia.
      simpl. rewrite RR1. rewrite RR2. rewrite RR3. eauto.
    + remember (eval C st e1 FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      remember (eval mv st1 e2 FUEL) as v2.
      clear H3. destruct v2 as [ | | v2 st2]; inversion H.
      clear H3. destruct v2 as [v2 | ]; inversion H; subst;
      assert (eval C st e1 m = Resolved (MVal mv) st1) as RR1;
      try (apply IHFUEL; eauto; nia).
      assert (eval mv st1 e2 m = Resolved (EVal v2) st') as RR2.
      apply IHFUEL; eauto; nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
      assert (eval mv st1 e2 m = Resolved (MVal mv0) st') as RR2.
      apply IHFUEL; eauto; nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
    + remember (eval C st e1 FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      clear H3. destruct st1 as [mem1 t1].
      remember (eval (C [|dy_c_lete x t1 ([||])|]) 
                     (ST (t1 !-> v1; mem1) (update C (ST mem1 t1) x v1))
                      e2 FUEL) as v2.
      destruct v2 as [ | | v2 st2]; inversion H.
      clear H3. destruct v2 as [v2 | ]; inversion H.
      subst.
      assert (eval C st e1 m = Resolved (EVal v1) (ST mem1 t1)) as RR1.
      apply IHFUEL; eauto. nia.
      assert (eval (C [|dy_c_lete x t1 ([||])|]) 
                   (ST (t1 !-> v1; mem1) (update C (ST mem1 t1) x v1))
                   e2 m = Resolved (MVal mv) st') as RR2.
      apply IHFUEL; eauto. nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
    + remember (eval C st e1 FUEL) as v1.
      destruct v1 as [ | | v1 st1]; inversion H.
      clear H3. destruct v1 as [v1 | ]; inversion H.
      clear H3.
      remember (eval (C [|dy_c_letm M mv ([||])|]) st1
                      e2 FUEL) as v2.
      destruct v2 as [ | | v2 st2]; inversion H.
      clear H3. destruct v2 as [v2 | ]; inversion H.
      subst.
      assert (eval C st e1 m = Resolved (MVal mv) st1) as RR1.
      apply IHFUEL; eauto. nia.
      assert (eval (C [|dy_c_letm M mv ([||])|]) st1
                   e2 m = Resolved (MVal mv0) st') as RR2.
      apply IHFUEL; eauto. nia.
      simpl. rewrite RR1. rewrite RR2. eauto.
Qed.
      
Lemma EvalR_well_defined_l :
  forall `{time T} (C : @dy_ctx T) st e v st' (R : EvalR C st e v st'),
    exists FUEL, eval C st e FUEL = Resolved v st'.
Proof.
  intros. induction R.
  - exists 1; simpl. rewrite <- ADDR. rewrite <- STATE. rewrite <- ACCESS. eauto.
  - exists 1; simpl; eauto.
  - destruct IHR1 as [FUEL' EQ'].
    destruct IHR2 as [FUEL'' EQ''].
    destruct IHR3 as [FUEL''' EQ'''].
    exists (S (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))).
    simpl.
    assert (eval C st e1 (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))
            = Resolved (EVal (Closure x e C_lam)) st_lam) as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval C st_lam e2 (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))
            = Resolved (EVal arg) (ST mem t)) as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR.
    assert (eval (C_lam [|dy_c_lam x t ([||])|]) 
                 (ST (t !-> arg; mem) (update C (ST mem t) x arg)) e
                 (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))
            = Resolved (EVal v) st_v) as RR.
    apply relax_fuel with (FUEL := FUEL'''). nia. eauto.
    rewrite RR; clear RR. eauto.
  - destruct IHR1 as [FUEL' EQ'].
    destruct IHR2 as [FUEL'' EQ''].
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    assert (eval C st m (Nat.max FUEL' FUEL'')
            = Resolved (MVal C_m) st_m) as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval C_m st_m e (Nat.max FUEL' FUEL'')
            = Resolved v st_v) as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR. eauto. 
  - exists 1. simpl; eauto. 
  - exists 1; simpl. rewrite <- ACCESS. eauto. 
  - destruct IHR1 as [FUEL' EQ'].
    destruct IHR2 as [FUEL'' EQ''].
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    assert (eval C st e (Nat.max FUEL' FUEL'')
            = Resolved (EVal v) (ST mem t)) as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval (C [|dy_c_lete x t ([||])|]) 
                 (ST (t !-> v; mem) (update C (ST mem t) x v)) m
                 (Nat.max FUEL' FUEL'')
            = Resolved (MVal C_m) st_m) as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR. eauto.
  - destruct IHR1 as [FUEL' EQ'].
    destruct IHR2 as [FUEL'' EQ''].
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    assert (eval C st m' (Nat.max FUEL' FUEL'')
            = Resolved (MVal C') st') as RR.
    apply relax_fuel with (FUEL := FUEL'). nia. eauto.
    rewrite RR; clear RR.
    assert (eval (C [|dy_c_letm M C' ([||])|]) st' m'' (Nat.max FUEL' FUEL'')
            = Resolved (MVal C'') st'') as RR.
    apply relax_fuel with (FUEL := FUEL''). nia. eauto.
    rewrite RR; clear RR. eauto.
Qed.

Lemma EvalR_well_defined_r :
  forall `{TIME : time T} FUEL (C : @dy_ctx T) st e v st' (R : eval C st e FUEL = Resolved v st'),
    EvalR C st e v st'.
Proof.
  intros. rename H into H'. rename H0 into H''. generalize dependent T. revert e.
  induction FUEL; intros; simpl in *; try (inversion R; fail).
  destruct e.
  - remember (addr_x C x) as addr. destruct addr; inversion R. clear H0.
    destruct st.
    remember (mem t) as access.
    destruct access; inversion R. subst. eauto.
  - inversion R. eauto.
  - remember (eval C st e1 FUEL) as v1.
    destruct v1 as [ | | v1 st1]; inversion R.
    clear H0. destruct v1 as [v1 | ]; inversion R.
    clear H0. destruct v1 as [x v1 C_lam].
    remember (eval C st1 e2 FUEL) as v2.
    destruct v2 as [ | | v2 st2]; inversion R.
    clear H0. destruct v2 as [v2 | ]; inversion R.
    clear H0. destruct st2 as [mem2 t2].
    remember (eval (C_lam [|dy_c_lam x t2 ([||])|])
                   (ST (t2 !-> v2; mem2) (update C (ST mem2 t2) x v2)) 
                   v1 FUEL) as v3.
    destruct v3 as [ | | v3 st3]; inversion R.
    clear H0. destruct v3 as [v3 | ]; inversion R.
    subst.
    assert (EvalR C st e1 (EVal (Closure x v1 C_lam)) st1) as RR1. eauto.
    assert (EvalR C st1 e2 (EVal v2) (ST mem2 t2)) as RR2. eauto.
    assert (EvalR (C_lam [|dy_c_lam x t2 ([||])|])
                  (ST (t2 !-> v2; mem2) (update C (ST mem2 t2) x v2)) v1
            (EVal v3) st') as RR3. eauto. eauto.
  - remember (eval C st e1 FUEL) as v1.
    destruct v1 as [ | | v1 st1]; inversion R.
    clear H0. destruct v1 as [v1 | ]; inversion R.
    clear H0. remember (eval mv st1 e2 FUEL) as v2.
    destruct v2 as [ | | v2 st2]; inversion R.
    clear H0. destruct v2 as [v2 | ]; inversion R; subst;
    eapply Eval_link; eauto.
  - inversion R; subst. eapply Eval_empty; eauto.
  - remember (ctx_M C M) as ACCESS.
    destruct ACCESS; inversion R; subst. eapply Eval_var_m; eauto.
  - remember (eval C st e1 FUEL) as v1.
    destruct v1 as [ | | v1 st1]; inversion R.
    clear H0. destruct v1 as [v1 | ]; inversion R.
    clear H0. destruct st1 as [mem1 t1].
    remember (eval (C [|dy_c_lete x t1 ([||])|])
                   (ST (t1 !-> v1; mem1) (update C (ST mem1 t1) x v1)) 
                   e2 FUEL) as v2.
    destruct v2 as [ | | v2 st2]; inversion R.
    clear H0. destruct v2 as [v2 | ]; inversion R.
    subst.
    assert (EvalR C st e1 (EVal v1) (ST mem1 t1)) as RR1. eauto.
    assert (EvalR (C [|dy_c_lete x t1 ([||])|])
                  (ST (t1 !-> v1; mem1) (update C (ST mem1 t1) x v1)) e2
            (MVal mv) st') as RR2. eauto.
    eapply Eval_lete; eauto.
  - remember (eval C st e1 FUEL) as v1.
    destruct v1 as [ | | v1 st1]; inversion R.
    clear H0. destruct v1 as [v1 | ]; inversion R.
    clear H0.
    remember (eval (C [|dy_c_letm M mv ([||])|]) st1 e2 FUEL) as v2.
    destruct v2 as [ | | v2 st2]; inversion R.
    clear H0. destruct v2 as [v2 | ]; inversion R.
    subst.
    assert (EvalR C st e1 (MVal mv) st1) as RR1. eauto.
    assert (EvalR (C [|dy_c_letm M mv ([||])|])
                  st1 e2 (MVal mv0) st') as RR2. eauto.
    eapply Eval_letm; eauto.
Qed.

Theorem EvalR_well_defined :
  forall `{TIME : time T} C st e v st',
    (exists FUEL, eval C st e FUEL = Resolved v st') <->
    EvalR C st e v st'.
Proof.
  intros; split; try apply EvalR_well_defined_l.
  intros. destruct H1 as [FUEL EVAL].
  eapply EvalR_well_defined_r. eauto.
Qed.

(* Reachability relation *)
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
                                 (ST (t !-> arg ; mem) 
                                     (update C (ST mem t) x arg)) e
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
                              (ST (t !-> v ; mem) 
                                  (update C (ST mem t) x v)) m
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

Lemma value_reach_only_itself :
  forall `{TIME : time T} C st v (pf : value v)
         C' st' e'
         (REACH : <| C st v ~> C' st' e' |>),
         C = C' /\ st = st' /\ v = e'.
Proof.
  intros; repeat split; inversion pf; inversion REACH; subst; eauto;
  try inversion H2.
Qed.

Lemma Meval_then_collect :
  forall `{TIME : time T} C st m v st_m
         (EVAL : EvalR C st m v st_m)
         C_m (MVAL : v = MVal C_m),
        match collect_ctx (dy_to_st C) m with
        | (Some C_m', _) => C_m' = dy_to_st C_m
        | (None, _) => False
        end.
Proof.
  intros. rename H into H'. revert C_m MVAL.
  induction EVAL; intros; simpl; try inversion MVAL; subst; eauto.
  - specialize (IHEVAL1 C_m eq_refl). 
    specialize (IHEVAL2 C_m0 eq_refl). 
    destruct (collect_ctx (dy_to_st C) m). destruct o.
    rewrite <- IHEVAL1 in IHEVAL2.
    destruct (collect_ctx s e). exact IHEVAL2. 
    exact IHEVAL1.
  - pose proof (mod_is_static_some C M) as H.
    destruct H as [A B]. specialize (A C_m).
    symmetry in ACCESS. specialize (A ACCESS).
    rewrite A. eauto.
  - rewrite dy_to_st_plugin in IHEVAL2.
    simpl in IHEVAL2.
    remember (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m) as ol.
    destruct ol. apply IHEVAL2; eauto.
  - rewrite dy_to_st_plugin in IHEVAL2. simpl in IHEVAL2.
    specialize (IHEVAL1 C' eq_refl). specialize (IHEVAL2 C_m eq_refl).
    destruct (collect_ctx (dy_to_st C) m'). destruct o; try apply IHEVAL1.
    rewrite <- IHEVAL1 in IHEVAL2.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m'').
    apply IHEVAL2.
Qed.

(* finite ctx predicate *)
Definition ctx_bound_st {T} ub (st : @state T):=
  match st with
  | ST mem t =>
    forall addr,
      match mem addr with
      | Some (Closure x e C_v) =>
        let (o, ctxs) := collect_ctx (dy_to_st C_v) (e_lam x e) in
        forall sC (IN : In sC ctxs),
               In sC ub
      | None => True
      end
  end.

Definition ctx_bound_tm {T} ub (C : @dy_ctx T) (st : @state T) e :=
  ctx_bound_st ub st /\
  let (o, ctxs) := collect_ctx (dy_to_st C) e in
  forall sC (IN : In sC ctxs),
         In sC ub.

Lemma eval_ctx_bound :
  forall `{TIME : time T} ub
         (C : @dy_ctx T) st e
         v st'
         (INIT : ctx_bound_tm ub C st e)
         (EVAL : EvalR C st e v st'),
    match v with
    | EVal (Closure x e' C_lam) =>
      ctx_bound_tm ub C_lam st' (e_lam x e')
    | MVal C_m =>
      ctx_bound_st ub st'
    (* | _ => ctx_bound_st ub st' *)
    end.
Proof.
  intros. rename H into H'. rename H0 into H''.
  induction EVAL; try destruct v as [x' e' C_lam'];
  destruct INIT as [A B]; eauto.
  - rewrite <- STATE in *. split; eauto.
    specialize (A addr). rewrite <- ACCESS in A. eauto.
  - destruct st. split; eauto.
  - apply IHEVAL3. clear IHEVAL3.
    simpl in B. 
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) e1)) -> In sC ub).
    { intros. specialize (B sC). apply B. rewrite in_app_iff.
      left. eauto. }
    assert (ctx_bound_tm ub C st e1). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) e1); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    destruct IHEVAL1 as [A' B'].
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) e2)) -> In sC ub).
    { intros. specialize (B sC). apply B. rewrite in_app_iff.
      right. eauto. }
    assert (ctx_bound_tm ub C st_lam e2).
    { split; eauto. destruct (collect_ctx (dy_to_st C) e2); eauto. }
    specialize (IHEVAL2 H0). clear H H0.
    simpl in B'. split; 
    try (rewrite dy_to_st_plugin; simpl;
         (destruct (collect_ctx (dy_to_st C_lam [[|st_c_lam x ([[||]])|]]) e));
         simpl in B'; intros; apply B'; eauto).
    simpl. intros. unfold update_m. 
    destruct arg as [x'' e'' C_lam''].
    destruct IHEVAL2 as [A'' B''].
    destruct (eqb addr t); eauto.
    simpl in A''. apply A''.
  - apply IHEVAL2. clear IHEVAL2.
    simpl in B.
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) m)) -> In sC ub).
    { intros. destruct (collect_ctx (dy_to_st C) m).
      destruct o; try destruct (collect_ctx s e); apply B;
      try rewrite in_app_iff; try left; eauto. }
    assert (ctx_bound_tm ub C st m). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) m); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    split; eauto. eapply Meval_then_collect in EVAL1; eauto.
    destruct (collect_ctx (dy_to_st C) m). 
    destruct o; try (inversion EVAL1; fail).
    rewrite <- EVAL1. destruct (collect_ctx s e).
    simpl in B. intros. apply B. rewrite in_app_iff. right; eauto.
  - apply IHEVAL2. clear IHEVAL2.
    simpl in B. 
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) e)) -> In sC ub).
    { intros. destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m).
      destruct o; apply B; rewrite in_app_iff; left; eauto. }
    assert (ctx_bound_tm ub C st e). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) e); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    destruct IHEVAL1 as [A' B'].
    split;
    try (rewrite dy_to_st_plugin; simpl;
         (destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m));
         destruct o; intros; apply B; rewrite in_app_iff; right; eauto).
    simpl. unfold update_m. intros.
    destruct (eqb addr t); eauto.
    apply A'.
  - apply IHEVAL2. clear IHEVAL2.
    simpl in B. 
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) m')) -> In sC ub).
    { intros. destruct (collect_ctx (dy_to_st C) m'). 
      destruct o; eauto. destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m'').
      destruct o; apply B; rewrite in_app_iff; left; eauto. }
    assert (ctx_bound_tm ub C st m'). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) m'); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    split; eauto.
    rewrite dy_to_st_plugin; simpl.
    eapply Meval_then_collect in EVAL1; eauto.
    destruct (collect_ctx (dy_to_st C) m'). 
    destruct o; try inversion EVAL1. clear H. rewrite <- EVAL1.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m'').
    intros. destruct o; apply B; rewrite in_app_iff; right; eauto.
Qed.

Lemma reach_ctx_bound :
  forall `{TIME : time T} ub
         (C : @dy_ctx T) st e
         C' st' e'
         (INIT : ctx_bound_tm ub C st e)
         (REACH : <| C st e ~> C' st' e' |>),
    ctx_bound_tm ub C' st' e'.
Proof.
  intros. rename H into H'. rename H0 into H''. induction REACH; eauto; 
          apply IHREACH; destruct INIT as [A B].
  - simpl in B. split; eauto.
    destruct (collect_ctx (dy_to_st C) e1).
    intros; apply B. simpl in *. rewrite in_app_iff. left; eauto.
  - apply eval_ctx_bound with (ub := ub) in FN.
    destruct FN as [A' B'].
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e2).
    intros; apply B. simpl in *. rewrite in_app_iff. right; eauto.
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e1).
    intros; apply B. simpl in *. rewrite in_app_iff. left; eauto.
  - apply eval_ctx_bound with (ub := ub) in FN.
    apply eval_ctx_bound with (ub := ub) in ARG. destruct arg as [x'' e'' C''].
    destruct FN as [A' B']. destruct ARG as [A'' B''].
    split. simpl. intros. unfold update_m.
    destruct (eqb addr t).
    simpl in B''. apply B''.
    simpl in A''. apply A''.
    rewrite dy_to_st_plugin. simpl. simpl in B'.
    destruct (collect_ctx (dy_to_st C_lam [[|st_c_lam x ([[||]])|]]) e).
    simpl in B'. intros; apply B'. right; eauto.
    destruct FN as [A' B'].
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e2).
    intros; apply B. simpl in *. rewrite in_app_iff. right; eauto.
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e1).
    intros; apply B. simpl in *. rewrite in_app_iff. left; eauto.
  - split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m). 
    intros. destruct o; try destruct (collect_ctx s e); apply B; eauto.
    rewrite in_app_iff. left; eauto.
  - eapply Meval_then_collect in MOD as MOD'; eauto.
    apply eval_ctx_bound with (ub := ub) in MOD.
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m).
    destruct o; inversion MOD'. clear H. rewrite <- MOD'.
    destruct (collect_ctx s e). 
    intros; apply B; simpl; rewrite in_app_iff; right; eauto.
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m). 
    intros. destruct o; try destruct (collect_ctx s e); apply B; eauto.
    rewrite in_app_iff. left; eauto.
  - split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e).
    destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m). 
    destruct o0; intros; apply B; simpl; rewrite in_app_iff; left; eauto.
  - apply eval_ctx_bound with (ub := ub) in EVALx; eauto. 
    destruct v as [x'' e'' C_lam''].
    destruct EVALx as [A' B'].
    split. simpl. unfold update_m. intros.
    destruct (eqb addr t); eauto. apply A'.
    simpl in B. rewrite dy_to_st_plugin. simpl.
    destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m).
    destruct o; intros; apply B; rewrite in_app_iff; right; eauto.
    (* copy of the goal before *)
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e).
    destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m). 
    destruct o0; intros; apply B; simpl; rewrite in_app_iff; left; eauto.
  - split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m1). destruct o; eauto.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2). 
    destruct o; intros; apply B; simpl; rewrite in_app_iff; left; eauto.
  - eapply Meval_then_collect in EVALM as EVALM'; eauto.
    apply eval_ctx_bound with (ub := ub) in EVALM.
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m1). destruct o; inversion EVALM'.
    clear H. rewrite dy_to_st_plugin; simpl. rewrite <- EVALM'.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2).
    destruct o; intros; apply B; rewrite in_app_iff; right; eauto.
    (* copy of the goal before *)
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m1). destruct o; eauto.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2). 
    destruct o; intros; apply B; simpl; rewrite in_app_iff; left; eauto.
Qed.

Theorem expr_ctx_bound :
  forall `{TIME : time T} t e (C' : @dy_ctx T) st' e'
         (REACH : <| ([||]) (ST empty_mem t) e ~> C' st' e' |>),
         In (dy_to_st C') (snd (collect_ctx ([[||]]) e)).
Proof.
  intros. rename H into H'. rename H0 into H''.
  pose proof (reach_ctx_bound (snd (collect_ctx st_c_hole e)) ([||]) (ST empty_mem t) e C' st' e') as H.
  assert (ctx_bound_tm (snd (collect_ctx ([[||]]) e)) 
                       ([||]) (ST empty_mem t) e) as FINAL.
  - split; simpl; eauto. destruct (collect_ctx ([[||]]) e); eauto.
  - apply H in FINAL; try apply REACH. 
    destruct FINAL as [MEM KILLER].
    remember (collect_ctx (dy_to_st C') e') as ol.
    destruct ol. apply KILLER. 
    assert (l = (snd (collect_ctx (dy_to_st C') e'))) as RR.
    rewrite <- Heqol; eauto.
    rewrite RR. apply collect_ctx_refl.
Qed.