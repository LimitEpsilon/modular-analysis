From Simple Require Export Syntax.

Generalizable Variables T.

Class time `{Eq T} :=
{ 
  tick : @dy_ctx T -> @amemory T -> T -> ID -> @expr_value T -> T;
}.

Definition update_m {T X} `{Eq T} mem (t : T) (x : X) :=
  fun t' => if eqb t' t then x :: (mem t) else mem t'.

Definition empty_mem {T X} (t : T) : list X := [].

Notation "p '!-#>' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Inductive step `{time T} : (@aconfig T) -> (@aconfig T) -> Prop :=
  | ExprID x C m t v addr
    (ADDR : addr_x C x = Some addr)
    (ACCESS : In v (m addr))
    : step (ACf (e_var x) C m t) (ARs (EVal v) m t)

  | Fn x e C m t
    : step (ACf (e_lam x e) C m t) (ARs (EVal (Closure x e C)) m t)

  | AppL e1 e2 C m t
    : step (ACf (e_app e1 e2) C m t) (ACf e1 C m t)

  | AppR e1 e2 C m t x e C_f m_f t_f
    (FN : step (ACf e1 C m t) (ARs (EVal (Closure x e C_f)) m_f t_f))
    : step (ACf (e_app e1 e2) C m t) (ACf e2 C m_f t_f)

  | AppBody e1 e2 C m t x e C_f m_f t_f v m_a t_a
    (FN : step (ACf e1 C m t) (ARs (EVal (Closure x e C_f)) m_f t_f))
    (ARG : step (ACf e2 C m_f t_f) (ARs (EVal v) m_a t_a))
    : step (ACf (e_app e1 e2) C m t) (ACf e (dy_binde x t_a C_f) (t_a !-#> v; m_a) (tick C m_a t_a x v))

  | App e1 e2 C m t x e C_f m_f t_f v m_a t_a v' m' t'
    (FN : step (ACf e1 C m t) (ARs (EVal (Closure x e C_f)) m_f t_f))
    (ARG : step (ACf e2 C m_f t_f) (ARs (EVal v) m_a t_a))
    (BODY : step (ACf e (dy_binde x t_a C_f) (t_a !-#> v; m_a) (tick C m_a t_a x v)) (ARs (EVal v') m' t'))
    : step (ACf (e_app e1 e2) C m t) (ARs (EVal v') m' t')

  | LinkL e1 e2 C m t
    : step (ACf (e_link e1 e2) C m t) (ACf e1 C m t)
  
  | LinkR e1 e2 C m t C' m' t'
    (MOD : step (ACf e1 C m t) (ARs (MVal C') m' t'))
    : step (ACf (e_link e1 e2) C m t) (ACf e2 C' m' t')
  
  | Link e1 e2 C m t C' m' t' V m'' t''
    (MOD : step (ACf e1 C m t) (ARs (MVal C') m' t'))
    (LINK : step (ACf e2 C' m' t') (ARs V m'' t''))
    : step (ACf (e_link e1 e2) C m t) (ARs V m'' t'')
  
  | Empty C m t
    : step (ACf m_empty C m t) (ARs (MVal C) m t)
  
  | ModID M C m t C_M
    (ACCESS : ctx_M C M = Some C_M)
    : step (ACf (m_var M) C m t) (ARs (MVal C_M) m t)
  
  | LetEL x e1 e2 C m t
    : step (ACf (m_lete x e1 e2) C m t) (ACf e1 C m t)
  
  | LetER x e1 e2 C m t v m' t'
    (EVALx : step (ACf e1 C m t) (ARs (EVal v) m' t'))
    : step (ACf (m_lete x e1 e2) C m t) (ACf e2 (dy_binde x t' C) (t' !-#> v; m') (tick C m' t' x v))
  
  | LetE x e1 e2 C m t v m' t' C' m'' t''
    (EVALx : step (ACf e1 C m t) (ARs (EVal v) m' t'))
    (EVALm : step (ACf e2 (dy_binde x t' C) (t' !-#> v; m') (tick C m' t' x v)) (ARs (MVal C') m'' t''))
    : step (ACf (m_lete x e1 e2) C m t) (ARs (MVal C') m'' t'')
  
  | LetML M e1 e2 C m t
    : step (ACf (m_letm M e1 e2) C m t) (ACf e1 C m t)
  
  | LetMR M e1 e2 C m t C' m' t'
    (EVALM : step (ACf e1 C m t) (ARs (MVal C') m' t'))
    : step (ACf (m_letm M e1 e2) C m t) (ACf e2 (dy_bindm M C' C) m' t')

  | LetM M e1 e2 C m t C' m' t' C'' m'' t''
    (EVALM : step (ACf e1 C m t) (ARs (MVal C') m' t'))
    (EVALm : step (ACf e2 (dy_bindm M C' C) m' t') (ARs (MVal C'') m'' t''))
    : step (ACf (m_letm M e1 e2) C m t) (ARs (MVal C'') m'' t'')
.

#[export] Hint Constructors step : core.

Inductive multi_step `{time T} : (aconfig T) -> (aconfig T) -> Prop :=
  | Refl cf : multi_step cf cf
  | Trans cf cf' cf''
    (REACHl : step cf cf')
    (REACHr : multi_step cf' cf'')
    : multi_step cf cf''
.

#[export] Hint Constructors multi_step : core.

Notation "'{|' ll '~#>' rr '|}'" := 
  (step ll rr) 
  (at level 10, ll at next level, rr at next level).

Notation "'{|' ll '~#>*' rr '|}'" := 
  (multi_step ll rr) 
  (at level 10, ll at next level, rr at next level).

Lemma Meval_then_collect `{time T} :
  forall e C m t mv m' t'       
        (EVAL : {|(ACf e C m t) ~#> (ARs (MVal mv) m' t')|}),
        match collect_ctx (dy_to_st C) e with
        | (Some mv', _) => mv' = dy_to_st mv
        | (None, _) => False
        end.
Proof.
  intros.
  remember (ACf e C m t) as acf eqn:INIT.
  remember (ARs (MVal mv) m' t') as ars eqn:MVAL.
  ginduction EVAL; intros; simpl; try inversion MVAL; subst; eauto;
  repeat match goal with
  | H : forall e C m t mv m' t',
    ACf ?e' ?C' ?m'' ?t'' = ACf _ _ _ _ ->
    ARs (MVal ?mv') ?m''' ?t''' = ARs _ _ _ -> _ |- _ =>
    specialize (H e' C' m'' t'' mv' m''' t''' eq_refl eq_refl)
  end;
  repeat des_hyp; clarify; simpl in *;
  repeat match goal with
  | RR : collect_ctx ?C ?e = _ |- context [collect_ctx ?C ?e] =>
    rewrite RR
  end; eauto.
  match goal with
  | H : ctx_M ?C ?M = Some ?mv |- _ =>
    let RR := fresh "RR" in
    assert (st_ctx_M (dy_to_st C) M = Some (dy_to_st mv)) as RR;
    try (apply mod_is_static_some; assumption);
    rewrite RR; eauto
  end.
Qed.

Definition ctx_bound_m {T} ub (m : amemory T) :=
  forall t x e C_v (INvl : In (Closure x e C_v) (m t))
         sC (IN : In sC (snd (collect_ctx (dy_to_st C_v) (e_lam x e)))),
  In sC ub.

Definition ctx_bound_cf {T} ub (cf : aconfig T) :=
  match cf with
  | ACf e C m t =>
    ctx_bound_m ub m /\
    forall sC (IN : In sC (snd (collect_ctx (dy_to_st C) e))), In sC ub
  | ARs (EVal (Closure x e C)) m t =>
    ctx_bound_m ub m /\
    forall sC (IN : In sC (snd (collect_ctx (dy_to_st C) (e_lam x e)))), In sC ub
  | ARs _ m t =>
    ctx_bound_m ub m
  end.

Lemma step_ctx_bound `{time T} :
  forall ub e (C : dy_ctx T) m t cf'
         (INIT : ctx_bound_cf ub (ACf e C m t))
         (STEP : {|(ACf e C m t) ~#> cf'|}),
    ctx_bound_cf ub cf'.
Proof.
  intros. remember (ACf e C m t) as cf eqn:CF.
  ginduction STEP; intros; clarify; destruct INIT as [BOUNDm BOUNDe];
  simpl; repeat des_goal;
  try (eauto; split; fail);
  repeat match goal with
  | IH : forall _ e C m t, _ -> _ -> _ |- _ =>
    specialize (IH ub)
  | IH : forall e C m t, _ -> _ -> ?P |- _ =>
    let BD := fresh "BD" in
    assert P as BD;
    [eapply IH; eauto; split; eauto; intros;
    match goal with
    | H : _ |- _ => apply H; fail
    | H : _ |- _ => 
      apply H; simpl; repeat des_goal;
      try rewrite in_app_iff;
      first [try left; eauto; fail | try right; eauto; fail]
    end | clear IH]
  end;
  match goal with
  | H : _ |- _ => eapply H; eauto; clear H
  | _ => idtac
  end;
  split; eauto;
  repeat match goal with
  | H : {|_ ~#> (ARs (MVal _) _ _)|} |- _ =>
    apply Meval_then_collect in H
  end; intros;
  match goal with
  | H : _ |- _ => apply H; simpl; right; eauto; fail
  | H : _ |- _ => apply H;
    simpl; repeat des_goal; clarify;
    repeat match goal with
    | RR : ?E = _ |- _ => rewrite RR in *; clear RR
    end;
    simpl in *; repeat des_hyp; clarify;
    rewrite in_app_iff; 
    first [right; eauto; fail | left; eauto; fail]
  | |- ctx_bound_m ub (?t !-#> ?v; ?m) =>
    red; unfold update_m;
    intros; simpl in *; 
    repeat des_hyp;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    | _ => idtac
    end; clarify;
    match goal with
    | H : _ |- _ => apply H; eauto; fail
    | H : _ |- _ =>
      destruct H as [H ?];
      red in H; eapply H; simpl; eauto; fail
    end
  end.
Qed.

Ltac inv_rs :=
  match goal with
  | H : {|(ARs _ _ _) ~#> _|} |- _ => inversion H
  end.

Lemma reach_ctx_bound `{time T} :
  forall ub e (C : dy_ctx T) m t cf'
         (INIT : ctx_bound_cf ub (ACf e C m t))
         (REACH : {| (ACf e C m t) ~#>* cf' |}),
    ctx_bound_cf ub cf'.
Proof.
  intros.
  remember (ACf e C m t) as cf.
  ginduction REACH; eauto; intros.
  destruct cf; try inv_rs.
  eapply step_ctx_bound in REACHl; eauto.
  destruct cf'; try (eapply IHREACH; eauto; fail).
  inversion REACH; eauto.
  inv_rs.
Qed.

Definition collect_ctx_val `{time T} (v : @expr_value T) :=
  match v with
  | Closure x e C => snd (collect_ctx (dy_to_st C) (e_lam x e))
  end.

Fixpoint collect_ctx_mem `{time T} (l : list T) (m : amemory T) :=
  match l with
  | [] => []
  | t :: tl =>
      (fold_left 
        (fun acc val => (collect_ctx_val val) ++ acc) 
        (m t) []) ++ (collect_ctx_mem tl m)
  end.

Lemma fold_left_in :
  forall {A B} (l : list A) (a : A) (b : B) (f : A -> list B) (INa : In a l) (INb : In b (f a)),
  In b (fold_left (fun acc x => f x ++ acc) l []).
Proof.
  assert (forall {A B} (f : A -> list B) (la : list A) (lb : list B),
    fold_left (fun acc x => f x ++ acc) la lb = (fold_left (fun acc x => f x ++ acc) la []) ++ lb) as RR.
  { intros A B f. induction la; eauto.
    intros. simpl. rewrite app_nil_r. rewrite IHla.
    rewrite (IHla (f a)). rewrite app_assoc. eauto. }
  intros A B l. induction l; intros; eauto.
  simpl in *. rewrite app_nil_r. rewrite RR.
  rewrite in_app_iff.
  destruct INa as [EQ | NEQ].
  - rewrite EQ. right; eauto.
  - left. eapply IHl; eauto.
Qed.

Lemma finite_m_then_bound `{time T} :
  forall l (m : @amemory T)
         (FINITE : forall t, m t <> [] -> In t l),
    ctx_bound_m (collect_ctx_mem l m) m.
Proof.
  intros l. induction l; intros; simpl; red; intros.
  - assert (In t []) as contra.
    apply FINITE. red. intros RR.
    rewrite RR in *. inversion INvl.
    inversion contra.
  - assert (In sC (collect_ctx_val (Closure x e C_v))) as IN'.
    { apply IN. } clear IN. rename IN' into IN.
    assert (a = t \/ (a <> t /\ In t l)) as CASES.
    { assert (a = t \/ a <> t) as CASES.
      { rewrite <- eqb_eq. destruct (eqb a t); eauto. }
      destruct CASES as [EQ | NEQ]; eauto. right. split; eauto.
      assert (In t (a :: l)) as CASES.
      apply FINITE. red; intros contra. rewrite contra in INvl; inversion INvl.
      simpl in CASES. destruct CASES; eauto. contradict. }
    destruct CASES as [EQ | [NEQ IN']]; rewrite in_app_iff.
    + rewrite EQ. left. eapply fold_left_in; eauto.
    + right.
      remember (fun t' => if eqb t' a then [] else m t') as m'.
      assert (forall t : T, m' t <> [] -> In t l) as FINITE'.
      { rewrite Heqm'. intros. des_hyp.
        contradict. exploit FINITE; eauto.
        intros [? | ?]; eauto. rewrite eqb_neq in *. contradict. }
      specialize (IHl m' FINITE'). rewrite Heqm' in IHl.
      clear Heqm' m' FINITE'. specialize (IHl t x e C_v).
      simpl in IHl.
      replace (eqb t a) with false in IHl; try (symmetry; apply eqb_neq; eauto).
      specialize (IHl INvl sC IN).
      clear t x e C_v FINITE INvl IN NEQ IN'. rename IHl into IN.
      revert a m sC IN.
      induction l; simpl; eauto.
      intros. rewrite in_app_iff in *.
      destruct IN.
      * left. des_hyp; simpl in *; eauto.
      * right. eapply IHl; eauto.
Qed.

(* Finite state space *)
Theorem expr_ctx_bound `{time T} :
  forall e C m t cf' l
         (FINITE : forall addr, m addr <> [] -> In addr l)
         (REACH : {|(ACf e C m t) ~#>* cf'|}),
  ctx_bound_cf ((snd (collect_ctx (dy_to_st C) e)) ++ (collect_ctx_mem l m)) cf'.
Proof.
  intros.
  eapply reach_ctx_bound; eauto.
  split; simpl; eauto.
  red. intros addr x body C_v INvl sC IN.
  rewrite in_app_iff. right.
  revert addr x body C_v INvl sC IN.
  assert (ctx_bound_m (collect_ctx_mem l m) m) as HINT.
  { apply finite_m_then_bound; eauto. }
  apply HINT.
  intros. rewrite in_app_iff. eauto.
Qed.
