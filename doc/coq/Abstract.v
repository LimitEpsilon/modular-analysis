From MODULAR Require Export Syntax.

Definition time := bool.

Definition path := list time.

Definition eq_t (t1 t2 : time) := Bool.eqb t1 t2.

Fixpoint eq_p (p1 p2 : path) :=
  match p1, p2 with
  | [], [] => true
  | hd1 :: tl1, [] => false
  | [], hd2 :: tl2 => false
  | hd1 :: tl1, hd2 :: tl2 =>
    if eq_t hd1 hd2 then eq_p tl1 tl2
                    else false
  end.

Definition len_p (p : path) := List.length p.

Lemma eq_t_eq :
  forall t1 t2, eq_t t1 t2 = true <-> t1 = t2.
Proof.
  unfold eq_t. apply Bool.eqb_true_iff.
Qed.

Lemma eq_t_neq :
  forall t1 t2, eq_t t1 t2 = false <-> t1 <> t2.
Proof.
  unfold eq_t. apply Bool.eqb_false_iff.
Qed.

Inductive dy_ctx :=
  | dy_c_hole
  | dy_c_lam (x: expr_id) (tx : time) (C : dy_ctx)
  | dy_c_lete (x : expr_id) (tx : time) (C : dy_ctx)
  | dy_c_letm (M : mod_id) (CM : dy_ctx) (C : dy_ctx)
.

Fixpoint dy_plugin_c Cout Cin :=
  match Cout with
  | dy_c_hole => Cin
  | dy_c_lam x tx C' => dy_c_lam x tx (dy_plugin_c C' Cin)
  | dy_c_lete x tx C' => dy_c_lete x tx (dy_plugin_c C' Cin)
  | dy_c_letm M CM C' => dy_c_letm M CM (dy_plugin_c C' Cin)
  end.

Fixpoint dy_level (C : dy_ctx) : path :=
  match C with
  | dy_c_hole => []
  | dy_c_lam _ t C'
  | dy_c_lete _ t  C' => dy_level C' ++ [t]
  | dy_c_letm _ _  C' => dy_level C'
  end.

Fixpoint addr_x (C : dy_ctx) (x : expr_id) :=
  match C with
  | dy_c_hole => []
  | dy_c_lam x' tx' C'
  | dy_c_lete x' tx' C' =>
    match addr_x C' x with
    | [] => if eq_eid x x' then [tx'] else []
    | addr => addr ++ [tx']
    end
  | dy_c_letm _ _ C' => addr_x C' x
  end.

Fixpoint ctx_M (C : dy_ctx) (M : mod_id) :=
  match C with
  | dy_c_hole => None
  | dy_c_lam _ _ C'
  | dy_c_lete _ _ C' => ctx_M C' M
  | dy_c_letm M' CM' C' =>
    match ctx_M C' M with
    | Some CM => Some CM
    | None => if eq_mid M M' then Some CM' else None
    end
  end.

(* a term, a context *)
Inductive expr_value :=
  | Closure (x : expr_id) (e : tm) (C : dy_ctx)
.

Inductive dy_value :=
  | EVal (ev : expr_value)
  | MVal (mv : dy_ctx)
.

Inductive state :=
  | ST (mem : path -> list expr_value)
       (t : time)
.

Definition update_t (C : dy_ctx) (st : state) 
                    (x : expr_id) (v : expr_value) :=
  match st with
  | ST mem t => negb t
  end.

Definition update_m {X} mem (p : path) (x : X) :=
  fun p1 => 
  if eq_p p1 p then
    x :: (mem p)
  else mem p1.

Definition empty_mem {X} (p : path) : list X := [].

Notation "p '!#->' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Notation "Cout '[#|' Cin '|#]'" := (dy_plugin_c Cout Cin)
                              (at level 100, Cin at next level, right associativity).
Notation "'[#||#]'" := (dy_c_hole) (at level 100).

Inductive EvalR (C : dy_ctx) (st : state)
    : tm -> dy_value -> state -> Prop :=
  | Eval_var_e x v mem t
             (STATE : ST mem t = st)
             (ADDR : [] <> addr_x C x)
             (ACCESS : In v (mem (addr_x C x)))
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
             (BODY : EvalR (C_lam [#|dy_c_lam x t ([#||#])|#])
                           (ST (t :: (dy_level C_lam) !#-> arg ; mem) 
                               (update_t C (ST mem t) x arg))
                           e (EVal v) st_v)
    : EvalR C st (e_app e1 e2) (EVal v) st_v
  | Eval_link m e C_m st_m v st_v
              (MOD : EvalR C st m (MVal C_m) st_m)
              (LINK : EvalR C_m st_m e (EVal v) st_v)
    : EvalR C st (e_link m e) (EVal v) st_v
  | Eval_empty
    : EvalR C st m_empty (MVal C) st
  | Eval_var_m M C_M (ACCESS : Some C_M = ctx_M C M)
    : EvalR C st (m_var M) (MVal C_M) st
  | Eval_lete x e v mem t
              m C_m st_m
               (EVALe : EvalR C st e (EVal v) (ST mem t))
               (EVALm : EvalR (C [#|dy_c_lete x t ([#||#])|#])
                        (ST (t :: (dy_level C) !#-> v ; mem) 
                            (update_t C (ST mem t) x v))
                        m (MVal C_m) st_m)
    : EvalR C st (m_lete x e m) (MVal C_m) st_m
  | Eval_letm M m' C' st'
              m'' C'' st''
              (EVALm' : EvalR C st m' (MVal C') st')
              (EVALm'' : EvalR (C [#|dy_c_letm M C' ([#||#])|#]) st'
                         m'' (MVal C'') st'')
    : EvalR C st (m_letm M m' m'') (MVal C'') st''
.

Definition Reach (tm1 tm2 : Type) := tm1 -> dy_ctx -> state -> tm2 -> Prop.

(* Reachability relation *)
Inductive ReachR (C : dy_ctx) (st : state)
    : Reach tm tm :=
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
                (REACHb : ReachR (C_lam[#|dy_c_lam x t ([#||#])|#]) 
                                 (ST (t :: (dy_level C_lam) !#-> arg ; mem) 
                                     (update_t C (ST mem t) x arg)) e
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
             (REACHm : ReachR (C[#|dy_c_lete x t ([#||#])|#])
                              (ST (t :: (dy_level C) !#-> v ; mem) 
                                  (update_t C (ST mem t) x v)) m
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
              (REACHm : ReachR (C[#|dy_c_letm M C_M ([#||#])|#]) st_M m2
                               C' st' e')
    : ReachR C st (m_letm M m1 m2)
             C' st' e'
.

Notation "'<|' C1 st1 tm1 '~#>' C2 st2 tm2 '|>'" := (ReachR C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

(* sanity check *)
Lemma reach_trans : forall C1 st1 e1
                         C2 st2 e2
                         C3 st3 e3
                         (REACH1 : <| C1 st1 e1 ~#> C2 st2 e2 |>)
                         (REACH2 : <| C2 st2 e2 ~#> C3 st3 e3 |>),
                         <| C1 st1 e1 ~#> C3 st3 e3 |>.
Proof.
  intros. generalize dependent e3.
  revert C3 st3.
  induction REACH1; eauto using ReachR.
Qed.

Lemma c_plugin_assoc : forall C1 C2 C3, C1[#| C2[#| C3 |#] |#] = ((C1[#|C2|#])[#|C3|#]).
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
  rewrite IHC1_2. eauto.
Qed.

Lemma eq_p_eq : forall p1 p2, eq_p p1 p2 = true <-> p1 = p2.
Proof.
  induction p1; induction p2;
  intros; simpl;
  try rewrite IHp1; try rewrite IHp2;
  eauto.
  - split; eauto.
  - split; intros contra; inversion contra.
  - split; intros contra; inversion contra.
  - simpl. remember (eq_t a a0) as eqa.
    destruct eqa; symmetry in Heqeqa;
    try rewrite eq_t_eq in Heqeqa;
    try rewrite eq_t_neq in Heqeqa.
    + split; intros. rewrite Heqeqa in *.
      apply IHp1 in H. rewrite H. eauto.
      eapply IHp1. inversion H; eauto.
    + split; intros contra; inversion contra.
      apply Heqeqa in H0; inversion H0.
Qed.

Lemma c_plugin_adds_level : forall C1 C2, eq_p (dy_level(C1 [#|C2|#] )) (dy_level C2 ++ dy_level C1) = true.
Proof.
  induction C1;
  intros; try rewrite IHC1;
  try apply Nat.eqb_eq; try rewrite app_nil_r in *; 
  try rewrite c_plugin_assoc in *; simpl in *; 
  eauto; try apply eq_p_eq; eauto;
  specialize (IHC1 C2); rewrite eq_p_eq in IHC1;
  rewrite IHC1; rewrite app_assoc; eauto.
Qed.

Fixpoint dy_to_st C :=
  match C with
  | ([#||#]) => st_c_hole
  | dy_c_lam x _ C' => st_c_lam x (dy_to_st C')
  | dy_c_lete x _ C' => st_c_lete x (dy_to_st C')
  | dy_c_letm M CM C' => st_c_letm M (dy_to_st CM) (dy_to_st C')
  end.

Lemma dy_to_st_plugin :
  forall Cout Cin,
    dy_to_st (Cout[#|Cin|#]) = st_c_plugin (dy_to_st Cout) (dy_to_st Cin).
Proof.
  induction Cout; intros; simpl; try rewrite IHCout; eauto.
  rewrite IHCout2. eauto.
Qed. 

Lemma mod_is_static_none : forall (dC : dy_ctx) (M : mod_id),
  (ctx_M dC M = None <-> st_ctx_M (dy_to_st dC) M = None).
Proof. 
  intros. repeat split. 
  - induction dC; simpl; eauto.
    destruct (ctx_M dC2 M). intros H; inversion H.
    specialize (IHdC2 eq_refl). rewrite IHdC2.
    destruct (eq_mid M M0). intros H; inversion H. eauto.
  - induction dC; simpl; eauto.
    destruct (st_ctx_M (dy_to_st dC2) M). intros H; inversion H.
    specialize (IHdC2 eq_refl). rewrite IHdC2.
    destruct (eq_mid M M0). intros H; inversion H. eauto.
Qed.

Lemma mod_is_static_some : forall (dC : dy_ctx) (M : mod_id),
  (forall v, ctx_M dC M = Some v -> st_ctx_M (dy_to_st dC) M = Some (dy_to_st v)) /\
  (forall v, st_ctx_M (dy_to_st dC) M = Some v -> exists dv, dy_to_st dv = v /\ ctx_M dC M = Some dv).
Proof.
  intros; split. 
  - induction dC; simpl; intros; eauto.
    + inversion H.
    + remember (ctx_M dC2 M) as v2. destruct v2.
      specialize (IHdC2 v H). rewrite IHdC2. eauto.
      symmetry in Heqv2. rewrite mod_is_static_none in Heqv2.
      rewrite Heqv2. destruct (eq_mid M M0); inversion H; eauto.
  - induction dC; simpl; intros; eauto.
    + inversion H.
    + remember (st_ctx_M (dy_to_st dC2) M) as v2. destruct v2.
      specialize (IHdC2 v H). inversion IHdC2. exists x.
      destruct H0. split. assumption. rewrite H1. eauto.
      remember (ctx_M dC2 M) as v2. destruct v2;
      symmetry in Heqv2; rewrite <- mod_is_static_none in Heqv2.
      rewrite Heqv2 in Heqv0. inversion Heqv0.
      destruct (eq_mid M M0). inversion H.
      exists dC1. eauto. inversion H.
Qed.

Lemma value_reach_only_itself_e :
  forall C st v (pf : value v)
         C' st' e'
         (REACH : <| C st v ~#> C' st' e' |>),
         C = C' /\ st = st' /\ v = e'.
Proof.
  intros; repeat split; inversion pf; inversion REACH; subst; eauto using ReachR;
  try inversion H0.
Qed.

Lemma Meval_then_collect :
  forall C st m v st_m
         (EVAL : EvalR C st m v st_m)
         C_m (MVAL : v = MVal C_m),
        match collect_ctx (dy_to_st C) m with
        | (Some C_m', _) => C_m' = dy_to_st C_m
        | (None, _) => False
        end.
Proof.
  intros. revert C_m MVAL.
  induction EVAL; intros; simpl; try inversion MVAL; subst; eauto.
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

Definition ctx_bound_st ub st:=
  match st with
  | ST mem t =>
    forall addr x e C_v (INvl : In (Closure x e C_v) (mem addr))
           sC (IN : In sC (snd (collect_ctx (dy_to_st C_v) (e_lam x e)))),
      In sC ub
  end.

Definition ctx_bound_tm ub C st e :=
  ctx_bound_st ub st /\
  let (o, ctxs) := collect_ctx (dy_to_st C) e in
  forall sC (IN : In sC ctxs),
         In sC ub.

Lemma eval_ctx_bound :
  forall ub
         C st e
         v st'
         (INIT : ctx_bound_tm ub C st e)
         (EVAL : EvalR C st e v st'),
    match v with
    | EVal (Closure x e' C_lam) =>
      ctx_bound_tm ub C_lam st' (e_lam x e')
    | MVal C_m =>
      ctx_bound_tm ub C_m st' m_empty
    (* | _ => ctx_bound_st ub st' *)
    end.
Proof.
  intros. 
  induction EVAL; try destruct v as [x' e' C_lam'];
  destruct INIT as [A B].
  - rewrite <- STATE in *. split; eauto.
    specialize (A (addr_x C x) x' e' C_lam' ACCESS). eauto.
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
    destruct (eq_p addr (t :: dy_level C_lam)); eauto.
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B''. eauto.
    simpl in A''. specialize (A'' (t :: dy_level C_lam) x0 e0 C_v H). eauto.
  - apply IHEVAL2. clear IHEVAL2.
    simpl in B.
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) m)) -> In sC ub).
    { intros. destruct (collect_ctx (dy_to_st C) m). 
      destruct o; specialize (B sC); apply B. 
      rewrite in_app_iff. left; eauto. eauto. }
    assert (ctx_bound_tm ub C st m). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) m); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    destruct IHEVAL1 as [A' B'].
    split; eauto. eapply Meval_then_collect in EVAL1; eauto.
    destruct (collect_ctx (dy_to_st C) m). 
    destruct o; try (inversion EVAL1; fail).
    rewrite <- EVAL1. destruct (collect_ctx s e).
    simpl in B. intros. apply B. rewrite in_app_iff. right; eauto.
  - split; eauto.
  - split; eauto. simpl in *.
    pose proof (mod_is_static_some C M) as H.
    destruct H as [A' B']. symmetry in ACCESS. 
    specialize (A' C_M ACCESS). rewrite A' in B.
    intros. destruct IN as [IN | contra]; try inversion contra.
    apply B. simpl. right. left. eauto.
  - apply IHEVAL2. clear IHEVAL2.
    simpl in B. 
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) e)) -> In sC ub).
    { intros. destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m).
      specialize (B sC). apply B. rewrite in_app_iff.
      left. eauto. }
    assert (ctx_bound_tm ub C st e). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) e); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    destruct IHEVAL1 as [A' B'].
    split;
    try (rewrite dy_to_st_plugin; simpl;
         (destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m));
         simpl in B; intros; apply B; rewrite in_app_iff; right; 
         eauto).
    simpl. unfold update_m. intros.
    destruct (eq_p addr (t :: dy_level C)); eauto.
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B'. eauto.
    simpl in A'. specialize (A' (t :: dy_level C) x0 e0 C_v H). eauto.
  - apply IHEVAL2. clear IHEVAL2.
    simpl in B. 
    assert (forall sC : st_ctx, In sC (snd (collect_ctx (dy_to_st C) m')) -> In sC ub).
    { intros. destruct (collect_ctx (dy_to_st C) m'). 
      destruct o; eauto. destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m'').
      specialize (B sC). apply B. rewrite in_app_iff.
      left. eauto. }
    assert (ctx_bound_tm ub C st m'). 
    { split; eauto. destruct (collect_ctx (dy_to_st C) m'); eauto. }
    specialize (IHEVAL1 H0). clear H H0.
    destruct IHEVAL1 as [A' B'].
    split; eauto.
    rewrite dy_to_st_plugin; simpl.
    eapply Meval_then_collect in EVAL1; eauto.
    destruct (collect_ctx (dy_to_st C) m'). 
    destruct o; try inversion EVAL1. clear H. rewrite <- EVAL1.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m'').
    intros. apply B. rewrite in_app_iff. right; eauto.
Qed.

Lemma reach_ctx_bound :
  forall ub
         C st e
         C' st' e'
         (INIT : ctx_bound_tm ub C st e)
         (REACH : <| C st e ~#> C' st' e' |>),
    ctx_bound_tm ub C' st' e'.
Proof.
  intros. induction REACH; eauto; 
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
    split. simpl. unfold update_m. intros.
    destruct (eq_p addr (t :: dy_level C_lam)).
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B''. eauto.
    simpl in A''. specialize (A'' (t :: dy_level C_lam) x0 e0 C_v H). eauto.
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
    intros. destruct o; apply B; eauto.
    rewrite in_app_iff. left; eauto.
  - eapply Meval_then_collect in MOD as MOD'; eauto.
    apply eval_ctx_bound with (ub := ub) in MOD.
    destruct MOD as [A' B'].
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m).
    destruct o; inversion MOD'. clear H. rewrite <- MOD'.
    destruct (collect_ctx s e). 
    intros; apply B; simpl; rewrite in_app_iff; right; eauto.
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m). 
    intros. destruct o; apply B; eauto.
    rewrite in_app_iff. left; eauto.
  - split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e).
    destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m). 
    intros; apply B; simpl; rewrite in_app_iff; left; eauto.
  - apply eval_ctx_bound with (ub := ub) in EVALx. destruct v as [x'' e'' C_lam''].
    destruct EVALx as [A' B'].
    split. simpl. unfold update_m. intros.
    destruct (eq_p addr (t :: dy_level C)).
    simpl in INvl. destruct INvl.
    inversion H; subst. simpl in B'. eauto.
    simpl in A'. specialize (A' (t :: dy_level C) x0 e0 C_v H). eauto.
    simpl in A'. specialize (A' addr x0 e0 C_v INvl). eauto.
    simpl in B. rewrite dy_to_st_plugin. simpl.
    destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m).
    intros; apply B. rewrite in_app_iff; right; eauto.
    (* copy of the goal before *)
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) e).
    destruct (collect_ctx (dy_to_st C [[|st_c_lete x ([[||]])|]]) m). 
    intros; apply B; simpl; rewrite in_app_iff; left; eauto.
  - split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m1). destruct o; eauto.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2). 
    intros; apply B; simpl; rewrite in_app_iff; left; eauto.
  - eapply Meval_then_collect in EVALM as EVALM'; eauto.
    apply eval_ctx_bound with (ub := ub) in EVALM.
    destruct EVALM as [A' B'].
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m1). destruct o; inversion EVALM'.
    clear H. rewrite dy_to_st_plugin; simpl. rewrite <- EVALM'.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2).
    intros; apply B; rewrite in_app_iff; right; eauto.
    (* copy of the goal before *)
    split; eauto. simpl in B.
    destruct (collect_ctx (dy_to_st C) m1). destruct o; eauto.
    destruct (collect_ctx (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2). 
    intros; apply B; simpl; rewrite in_app_iff; left; eauto.
Qed.

Theorem expr_ctx_bound :
  forall e C' st' e'
         (REACH : <| ([#||#]) (ST empty_mem true) e ~#> C' st' e' |>),
         In (dy_to_st C') (snd (collect_ctx ([[||]]) e)).
Proof.
  intros.
  pose proof (reach_ctx_bound (snd (collect_ctx st_c_hole e)) ([#||#]) (ST empty_mem true) e C' st' e') as H.
  assert (ctx_bound_tm (snd (collect_ctx ([[||]]) e)) 
                       ([#||#]) (ST empty_mem true) e) as FINAL.
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
