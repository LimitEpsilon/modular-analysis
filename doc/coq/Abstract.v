From MODULAR Require Export Syntax.

Generalizable Variables T.

Inductive state {T : Type} :=
  | ST (mem : T -> list (@expr_value T))
       (t : T)
.

Class time `{Eq T} :=
{  
  update : (@dy_ctx T) -> (@state T) -> expr_id -> (@expr_value T) -> T;
}.

Definition update_m {X} `{time T} mem (t : T) (x : X) :=
  fun t' => 
  if eqb t' t then
    x :: (mem t)
  else mem t'.

Definition empty_mem {X T} (t : T) : list X := [].

Notation "p '!#->' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Inductive EvalR `{time T} (C : @dy_ctx T) (st : @state T)
    : tm -> dy_value -> state -> Prop :=
  | Eval_var_e x v mem t addr
             (STATE : ST mem t = st)
             (ADDR : Some addr = addr_x C x)
             (ACCESS : In v (mem addr))
    : EvalR C st (e_var x) (EVal v) st
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
                           (ST (t !#-> arg ; mem) 
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
                        (ST (t !#-> v ; mem) 
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

(* Reachability relation *)
Inductive ReachR `{time T} (C : dy_ctx) (st : state)
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
                                 (ST (t !#-> arg ; mem) 
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
                              (ST (t !#-> v ; mem) 
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

Notation "'<|' C1 st1 tm1 '~#>' C2 st2 tm2 '|>'" := (ReachR C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

(* sanity check *)
Lemma reach_trans : forall `{time T} (C1 : @dy_ctx T) st1 e1
                         C2 st2 e2
                         C3 st3 e3
                         (REACH1 : <| C1 st1 e1 ~#> C2 st2 e2 |>)
                         (REACH2 : <| C2 st2 e2 ~#> C3 st3 e3 |>),
                         <| C1 st1 e1 ~#> C3 st3 e3 |>.
Proof.
  intros. generalize dependent e3.
  revert C3 st3.
  induction REACH1; eauto.
Qed.

Lemma value_reach_only_itself_e :
  forall `{time T} (C : @dy_ctx T) st v (pf : value v)
         C' st' e'
         (REACH : <| C st v ~#> C' st' e' |>),
         C = C' /\ st = st' /\ v = e'.
Proof.
  intros; repeat split; inversion pf; inversion REACH; subst; eauto;
  try inversion H2.
Qed.

Lemma Meval_then_collect :
  forall `{time T} C st m v st_m
         (EVAL : EvalR C st m v st_m)
         C_m (MVAL : v = MVal C_m),
        match collect_ctx (dy_to_st C) m with
        | (Some C_m', _) => C_m' = dy_to_st C_m
        | (None, _) => False
        end.
Proof.
  intros. rename H into H'. rename H0 into H0'. revert C_m MVAL.
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

Definition ctx_bound_st {T} ub (st : @state T) :=
  match st with
  | ST mem t =>
    forall addr x e C_v (INvl : In (Closure x e C_v) (mem addr))
           sC (IN : In sC (snd (collect_ctx (dy_to_st C_v) (e_lam x e)))),
      In sC ub
  end.

Definition ctx_bound_tm {T} ub (C : @dy_ctx T) (st : @state T) e :=
  ctx_bound_st ub st /\
  let (o, ctxs) := collect_ctx (dy_to_st C) e in
  forall sC (IN : In sC ctxs),
         In sC ub.

Lemma eval_ctx_bound :
  forall `{time T} ub
         (C : @dy_ctx T) st e
         v st'
         (INIT : ctx_bound_tm ub C st e)
         (EVAL : EvalR C st e v st'),
    match v with
    | EVal (Closure x e' C_lam) =>
      ctx_bound_tm ub C_lam st' (e_lam x e')
    | _ => ctx_bound_st ub st'
    end.
Proof.
  intros. rename H into H'. rename H0 into H0'.
  induction EVAL; try destruct v as [x' e' C_lam'];
  destruct INIT as [A B]; eauto.
  - rewrite <- STATE in *. split; eauto.
    specialize (A addr x' e' C_lam' ACCESS). eauto.
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
    simpl. unfold update_m. intros.
    destruct arg as [x'' e'' C_lam''].
    destruct IHEVAL2 as [A'' B''].
    destruct (eqb addr t); eauto.
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B''. eauto.
    simpl in A''. specialize (A'' t x0 e0 C_v H). eauto.
  - apply IHEVAL2. clear IHEVAL2.
    simpl in B.
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) m)) -> In sC ub).
    { intros. destruct (collect_ctx (dy_to_st C) m).
      destruct o; try destruct (collect_ctx s e); apply B;
      try rewrite in_app_iff; try left; eauto. }
    assert (ctx_bound_tm ub C st m). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) m); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    eapply Meval_then_collect in EVAL1; eauto.
    destruct (collect_ctx (dy_to_st C) m). 
    destruct o; try (inversion EVAL1; fail).
    split; eauto.
    rewrite <- EVAL1. destruct (collect_ctx s e).
    intros. apply B. rewrite in_app_iff; right; eauto.
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
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B'. eauto.
    simpl in A'. specialize (A' t x0 e0 C_v H). eauto.
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
  forall `{time T} ub
         (C : @dy_ctx T) st e
         C' st' e'
         (INIT : ctx_bound_tm ub C st e)
         (REACH : <| C st e ~#> C' st' e' |>),
    ctx_bound_tm ub C' st' e'.
Proof.
  intros. rename H into H'. rename H0 into H0'.
  induction REACH; eauto; apply IHREACH; destruct INIT as [A B].
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
    split. simpl. unfold update_m. intros.
    destruct (eqb addr t).
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B''. eauto.
    simpl in A''. specialize (A'' t x0 e0 C_v H). eauto.
    simpl in A''. specialize (A'' addr x0 e0 C_v INvl). eauto.
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
  - apply eval_ctx_bound with (ub := ub) in EVALx. destruct v as [x'' e'' C_lam''].
    destruct EVALx as [A' B'].
    split. simpl. unfold update_m. intros.
    destruct (eqb addr t).
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B'. eauto.
    simpl in A'. specialize (A' t x0 e0 C_v H). eauto.
    simpl in A'. specialize (A' addr x0 e0 C_v INvl). eauto.
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
  forall `{time T} init e C' st' e'
         (REACH : <| ([||]) (ST empty_mem init) e ~#> C' st' e' |>),
         In (dy_to_st C') (snd (collect_ctx ([[||]]) e)).
Proof.
  intros. rename H into H'. rename H0 into H0'.
  pose proof (reach_ctx_bound (snd (collect_ctx st_c_hole e)) ([||]) (ST empty_mem init) e C' st' e') as H.
  assert (ctx_bound_tm (snd (collect_ctx ([[||]]) e)) 
                       ([||]) (ST empty_mem init) e) as FINAL.
  - split; simpl; eauto. intros. inversion INvl. 
    destruct (collect_ctx ([[||]]) e); eauto.
  - apply H in FINAL; try apply REACH. 
    destruct FINAL as [MEM KILLER].
    remember (collect_ctx (dy_to_st C') e') as ol.
    destruct ol. apply KILLER. 
    assert (l = (snd (collect_ctx (dy_to_st C') e'))) as RR.
    rewrite <- Heqol; eauto.
    rewrite RR. apply collect_ctx_refl.
Qed.
