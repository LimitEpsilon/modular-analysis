From Simple Require Export Syntax.

Generalizable Variables T.

Class time `{TotalOrder T} :=
{
  tick : @dy_ctx T -> @memory T -> T -> ID -> @expr_value T -> T;
  tick_lt : forall C mem t x v, t < tick C mem t x v
}.

Definition update_m {T X} `{Eq T} mem (t : T) (x : X) :=
  fun t' => if eqb t' t then Some x else mem t'.

Definition empty_mem {T X} (t : T) : option X := None.

Notation "p '!->' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Inductive step `{time T} : (@config T) -> (@config T) -> Prop :=
  | ExprID x C m t v addr
    (ADDR : addr_x C x = Some addr)
    (ACCESS : m addr = Some v)
    : step (Cf (e_var x) C m t) (Rs (EVal v) m t)

  | Fn x e C m t
    : step (Cf (e_lam x e) C m t) (Rs (EVal (Closure x e C)) m t)

  | AppL e1 e2 C m t
    : step (Cf (e_app e1 e2) C m t) (Cf e1 C m t)

  | AppR e1 e2 C m t x e C_f m_f t_f
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure x e C_f)) m_f t_f))
    : step (Cf (e_app e1 e2) C m t) (Cf e2 C m_f t_f)

  | AppBody e1 e2 C m t x e C_f m_f t_f v m_a t_a
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    : step (Cf (e_app e1 e2) C m t) (Cf e (dy_binde x t_a C_f) (t_a !-> v; m_a) (tick C m_a t_a x v))

  | App e1 e2 C m t x e C_f m_f t_f v m_a t_a v' m' t'
    (FN : step (Cf e1 C m t) (Rs (EVal (Closure x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    (BODY : step (Cf e (dy_binde x t_a C_f) (t_a !-> v; m_a) (tick C m_a t_a x v)) (Rs (EVal v') m' t'))
    : step (Cf (e_app e1 e2) C m t) (Rs (EVal v') m' t')

  | LinkL e1 e2 C m t
    : step (Cf (e_link e1 e2) C m t) (Cf e1 C m t)
  
  | LinkR e1 e2 C m t C' m' t'
    (MOD : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    : step (Cf (e_link e1 e2) C m t) (Cf e2 C' m' t')
  
  | Link e1 e2 C m t C' m' t' V m'' t''
    (MOD : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    (LINK : step (Cf e2 C' m' t') (Rs V m'' t''))
    : step (Cf (e_link e1 e2) C m t) (Rs V m'' t'')
  
  | Empty C m t
    : step (Cf m_empty C m t) (Rs (MVal C) m t)
  
  | ModID M C m t C_M
    (ACCESS : ctx_M C M = Some C_M)
    : step (Cf (m_var M) C m t) (Rs (MVal C_M) m t)
  
  | LetEL x e1 e2 C m t
    : step (Cf (m_lete x e1 e2) C m t) (Cf e1 C m t)
  
  | LetER x e1 e2 C m t v m' t'
    (EVALx : step (Cf e1 C m t) (Rs (EVal v) m' t'))
    : step (Cf (m_lete x e1 e2) C m t) (Cf e2 (dy_binde x t' C) (t' !-> v; m') (tick C m' t' x v))
  
  | LetE x e1 e2 C m t v m' t' C' m'' t''
    (EVALx : step (Cf e1 C m t) (Rs (EVal v) m' t'))
    (EVALm : step (Cf e2 (dy_binde x t' C) (t' !-> v; m') (tick C m' t' x v)) (Rs (MVal C') m'' t''))
    : step (Cf (m_lete x e1 e2) C m t) (Rs (MVal C') m'' t'')
  
  | LetML M e1 e2 C m t
    : step (Cf (m_letm M e1 e2) C m t) (Cf e1 C m t)
  
  | LetMR M e1 e2 C m t C' m' t'
    (EVALM : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    : step (Cf (m_letm M e1 e2) C m t) (Cf e2 (dy_bindm M C' C) m' t')

  | LetM M e1 e2 C m t C' m' t' C'' m'' t''
    (EVALM : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    (EVALm : step (Cf e2 (dy_bindm M C' C) m' t') (Rs (MVal C'') m'' t''))
    : step (Cf (m_letm M e1 e2) C m t) (Rs (MVal C'') m'' t'')
.

#[export] Hint Constructors step : core.

Inductive multi_step `{time T} : (@config T) -> (@config T) -> Prop :=
  | Refl cf : multi_step cf cf
  | Trans cf cf' cf''
    (REACHl : step cf cf')
    (REACHr : multi_step cf' cf'')
    : multi_step cf cf''
.

Notation "'{|' ll '~>' rr '|}'" := 
  (step ll rr) 
  (at level 10, ll at next level, rr at next level).

Notation "'{|' ll '~>*' rr '|}'" := 
  (multi_step ll rr) 
  (at level 10, ll at next level, rr at next level).

Inductive interpreter_state `{time T} :=
  | Pending (reached : list (@config T))
  | Error (reached : list (@config T)) (* Type error *)
  | Resolved (V : @dy_value T) (m : @memory T) (t : T) (reached : list (@config T))
.

Fixpoint eval `{time T} e C m t (reached : list (@config T)) (FUEL : nat) :=
  let reached := (Cf e C m t) :: reached in
  match FUEL with
  | 0 => Pending reached
  | S FUEL' =>
    match e with
    | e_var x =>
      match addr_x C x with
      | None => Error reached
      | Some addr =>
        match m addr with
        | None => Error reached
        | Some v => Resolved (EVal v) m t ((Rs (EVal v) m t) :: reached)
        end
      end
    | e_lam x e =>
      let v := Closure x e C in
      Resolved (EVal v) m t ((Rs (EVal v) m t) :: reached)
    | e_app e1 e2 =>
      match eval e1 C m t reached FUEL' with
      | Resolved (EVal (Closure x e C_f)) m_f t_f reached' =>
        match eval e2 C m_f t_f reached' FUEL' with
        | Resolved (EVal v) m_a t_a reached'' =>
          match eval e (dy_binde x t_a C_f) (t_a !-> v; m_a) (tick C m_a t_a x v) reached'' FUEL' with
          | Resolved (EVal v') m' t' reached''' => Resolved (EVal v') m' t' reached'''
          | Resolved _ _ _ reached''' => Error reached'''
          | other => other
          end
        | Resolved _ _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved _ _ _ reached' => Error reached'
      | other => other
      end
    | e_link e1 e2 =>
      match eval e1 C m t reached FUEL' with
      | Resolved (MVal C') m' t' reached' =>
        match eval e2 C' m' t' reached' FUEL' with
        | Resolved V m'' t'' reached'' => Resolved V m'' t'' reached''
        | other => other
        end
      | Resolved _ _ _ reached' => Error reached'
      | other => other
      end
    | m_empty => Resolved (MVal C) m t ((Rs (MVal C) m t) :: reached)
    | m_var M =>
      match ctx_M C M with
      | None => Error reached
      | Some C_M => Resolved (MVal C_M) m t ((Rs (MVal C_M) m t) :: reached)
      end
    | m_lete x e1 e2 =>
      match eval e1 C m t reached FUEL' with
      | Resolved (EVal v) m' t' reached' =>
        match eval e2 (dy_binde x t' C) (t' !-> v; m') (tick C m' t' x v) reached' FUEL' with
        | Resolved (MVal C') m'' t'' reached'' => Resolved (MVal C') m'' t'' reached''
        | Resolved _ _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved _ _ _ reached' => Error reached'
      | other => other
      end
    | m_letm M e1 e2 =>
      match eval e1 C m t reached FUEL' with
      | Resolved (MVal C') m' t' reached' =>
        match eval e2 (dy_bindm M C' C) m' t' reached' FUEL' with
        | Resolved (MVal C'') m'' t'' reached'' => Resolved (MVal C'') m'' t'' reached''
        | Resolved _ _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved _ _ _ reached' => Error reached'
      | other => other
      end
    end
  end.

Ltac rep_eval SOLVER :=
  match goal with
  | [RR : eval ?e ?C ?m ?t ?l ?n = _ |- 
          context [eval ?e ?C ?m ?t ?l ?n]] =>
    (* trivial case *)
    rewrite RR;
    move RR at top
  | [RR : eval ?e ?C ?m ?t ?l ?n = _ |-
      context [eval ?e ?C ?m ?t ?l ?n0]] =>
    (* relaxation *)
    replace (eval e C m t l n0) with (eval e C m t l n);
    rewrite RR;
    (* IHFUEL *)
    try (symmetry; apply SOLVER; eauto; fail);
    (* relax_fuel *)
    try (symmetry; apply SOLVER with (FUEL := n); try nia; eauto; fail);
    move RR at top
  | [RR : eval ?e ?C ?m ?t ?l ?n = _ |-
      context [eval ?e ?C ?m ?t ?l0 ?n0]] =>
    (* relaxation, l is an evar *)
    replace (eval e C m t l0 n0) with (eval e C m t l n);
    rewrite RR;
    (* IHFUEL *)
    try (symmetry; apply SOLVER; eauto; fail);
    (* relax_fuel *)
    try (symmetry; apply SOLVER with (FUEL := n); try nia; eauto; fail);
    move RR at top
  | _ => fail
  end.

Lemma relax_fuel `{time T} :
  forall FUEL FUEL' (LE : FUEL <= FUEL') e C m t l l' V m' t'
    (EVAL : eval e C m t l FUEL = Resolved V m' t' l'),
    eval e C m t l FUEL' = Resolved V m' t' l'.
Proof.
  rename H into ET. rename H0 into OT. rename H1 into TT.
  induction FUEL; intros.
  - inversion EVAL.
  - inversion LE; eauto. 
    assert (FUEL <= m0) as HINT. { nia. }
    specialize (IHFUEL m0 HINT).
    destruct e; simpl in *; eauto; repeat des_hyp;
    rep_eval IHFUEL;
    rep_eval IHFUEL; eauto.
    rep_eval IHFUEL. eauto.
Qed.

Lemma relax_fuel_err `{time T} :
  forall FUEL FUEL' (LE : FUEL <= FUEL') e C m t l l'
    (EVAL : eval e C m t l FUEL = Error l'),
    eval e C m t l FUEL' = Error l'.
Proof.
  rename H into ET. rename H0 into OT. rename H1 into TT.
  induction FUEL; intros.
  inversion EVAL.
  inversion LE; eauto. 
  assert (FUEL <= m0) as HINT. { nia. }
  specialize (IHFUEL m0 HINT).
  destruct e; simpl in *; eauto; repeat des_hyp;
  try (erewrite IHFUEL; eauto; fail);
  try (erewrite relax_fuel; eauto);
  simpl; eauto;
  try (rep_eval IHFUEL; eauto; fail);
  try (rep_eval relax_fuel; eauto; fail).
  rep_eval relax_fuel. rep_eval IHFUEL. eauto.
  rep_eval relax_fuel. rep_eval relax_fuel. eauto.
Qed.

Lemma Eval_well_defined_l :
  forall `{time T} e (C : @dy_ctx T) m t l V m' t' 
    (R : {| Cf e C m t ~> Rs V m' t' |}),
    exists FUEL, 
      match eval e C m t l FUEL with
      | Resolved V' m'' t'' _ => V = V' /\ m' = m'' /\ t' = t''
      | _ => False
      end.
Proof.
  intros. revert l. remember (Cf e C m t) as cf. remember (Rs V m' t') as rs.
  generalize dependent e. generalize dependent V. revert C m t m' t'.
  induction R; intros; inversion Heqcf; inversion Heqrs; subst.
  - exists 1; simpl. rewrite ADDR. rewrite ACCESS. eauto.
  - exists 1; simpl; eauto.
  - edestruct IHR1 as [FUEL' EQ']; eauto. clear IHR1. des_hyp.
    edestruct IHR2 as [FUEL'' EQ'']; eauto. clear IHR2. des_hyp.
    edestruct IHR3 as [FUEL''' EQ''']; eauto. clear IHR3. des_hyp.
    exists (S (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))).
    simpl.
    destruct EQ' as [? [? ?]]. subst.
    destruct EQ'' as [? [? ?]]. subst.
    destruct EQ''' as [? [? ?]]. subst.
    rep_eval relax_fuel.
    rep_eval relax_fuel.
    rep_eval relax_fuel. eauto.
  - edestruct IHR1 as [FUEL' EQ']; eauto. clear IHR1. des_hyp.
    edestruct IHR2 as [FUEL'' EQ'']; eauto. clear IHR2. des_hyp.
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    destruct EQ' as [? [? ?]]. subst.
    destruct EQ'' as [? [? ?]]. subst.
    rep_eval relax_fuel.
    rep_eval relax_fuel. eauto.
  - exists 1. simpl; eauto.
  - exists 1; simpl. rewrite ACCESS. eauto.
  - edestruct IHR1 as [FUEL' EQ']; eauto. clear IHR1. des_hyp.
    edestruct IHR2 as [FUEL'' EQ'']; eauto. clear IHR2. des_hyp.
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    destruct EQ' as [? [? ?]]. subst.
    destruct EQ'' as [? [? ?]]. subst.
    rep_eval relax_fuel.
    rep_eval relax_fuel. eauto.
  - edestruct IHR1 as [FUEL' EQ']; eauto. clear IHR1. des_hyp.
    edestruct IHR2 as [FUEL'' EQ'']; eauto. clear IHR2. des_hyp.
    exists (S (Nat.max FUEL' FUEL'')).
    simpl.
    destruct EQ' as [? [? ?]]. subst.
    destruct EQ'' as [? [? ?]]. subst.
    rep_eval relax_fuel.
    rep_eval relax_fuel. eauto.
Qed.

Ltac interp_to_rel SOLVER :=
  match goal with
  | [H : eval ?e ?C ?m ?t ?reached _ = Resolved ?V ?m0 ?t0 _ |- _] =>
    let REL := fresh "REL" in
    assert (REL : {| Cf e C m t ~> Rs V m0 t0 |});
    try (apply SOLVER with (l := reached); rewrite H; eauto);
    move H at top
  | _ => fail
  end.

Lemma Eval_well_defined_r `{time T} :
  forall FUEL (C : @dy_ctx T) m t e l V m' t'
    (R : match eval e C m t l FUEL with
         | Resolved V' m'' t'' _ => V = V' /\ m' = m'' /\ t' = t''
         | _ => False
         end),
    {| (Cf e C m t) ~> (Rs V m' t') |}.
Proof.
  rename H into ET. rename H0 into OT. rename H1 into TT.
  induction FUEL; intros; simpl in *; try (inversion R; fail).
  destruct e; repeat des_hyp;
  destruct R as [? [? ?]]; subst; eauto;
  inversion HDES; subst; eauto;
  interp_to_rel IHFUEL; eauto;
  interp_to_rel IHFUEL; eauto;
  interp_to_rel IHFUEL; eauto.
Qed.

Theorem Eval_well_defined `{time T} :
  forall l e C m t V m' t',
    (exists FUEL, 
      match eval e C m t l FUEL with 
      | Resolved V' m'' t'' _ => V = V' /\ m' = m'' /\ t' = t''
      | _ => False
      end) <->
    ({| (Cf e C m t) ~> (Rs V m' t') |}).
Proof.
  intros; split; try apply Eval_well_defined_l.
  intros RR. destruct RR as [FUEL EVAL].
  eapply Eval_well_defined_r. eauto.
Qed.

Definition extract_reached `{time T} (interp : interpreter_state) :=
  match interp with
  | Pending reached
  | Error reached
  | Resolved _ _ _ reached => reached
  end.

(* replace a shorter expression with a longer expression,
   which is rewritten with RR to be finished off with KILLER *)
Ltac rep_with_rew short KILLER :=
  match goal with
  | [RR : _ = Pending short |- _] =>
    replace short with (extract_reached (Pending short));
    try reflexivity; rewrite <- RR
  | [RR : Pending short = _ |- _] =>
    replace short with (extract_reached (Pending short));
    try reflexivity; rewrite RR
  | [RR : _ = Error short |- _] =>
    replace short with (extract_reached (Error short));
    try reflexivity; rewrite <- RR
  | [RR : Error short = _ |- _] =>
    replace short with (extract_reached (Error short));
    try reflexivity; rewrite RR
  | [RR : _ = Resolved ?V ?m ?t short |- _] =>
    replace short with (extract_reached (Resolved V m t short));
    try reflexivity; rewrite <- RR
  | [RR : Resolved ?V ?m ?t short = _ |- _] =>
    replace short with (extract_reached (Resolved V m t short));
    try reflexivity; rewrite RR
  | [RR : _ = short |- _] =>
    rewrite <- RR
  | [RR : short = _ |- _] =>
    rewrite RR
  | _ => fail
  end;
  match goal with
  | _ => apply KILLER; try right; simpl; eauto
  | _ => fail
  end.

Lemma reach_myself `{time T} :
  forall FUEL e (C : @dy_ctx T) m t l cf,
    In cf (Cf e C m t :: l) -> In cf (extract_reached (eval e C m t l FUEL)).
Proof.
  rename H into ET. rename H0 into OT. rename H1 into TT.
  induction FUEL; intros; try (simpl; eauto; fail).
  simpl. destruct e; repeat des_goal; simpl; eauto;
  try rep_with_rew reached1 IHFUEL;
  try rep_with_rew reached0 IHFUEL;
  try rep_with_rew reached IHFUEL.
Qed.

Ltac clar_eval := 
  match goal with
  | [H : eval ?e ?C ?m ?t ?l _ = Error _ |- 
      context [eval ?e ?C ?m ?t ?l _]] =>
    rep_eval relax_fuel_err; eauto
  | [H : eval ?e ?C ?m ?t ?l _ = Resolved _ _ _ _ |-
      context [eval ?e ?C ?m ?t ?l _]] =>
    rep_eval relax_fuel; eauto
  | _ => fail
  end.

Lemma relax_fuel_reach `{time T} :
  forall FUEL FUEL' (LE : FUEL <= FUEL') e (C : @dy_ctx T) m t l cf,
    In cf (extract_reached (eval e C m t l FUEL)) ->
    In cf (extract_reached (eval e C m t l FUEL')).
Proof.
  rename H into ET. rename H0 into OT. rename H1 into TT.
  induction FUEL; intros.
  simpl in *. apply reach_myself. eauto.
  inversion LE; subst. assumption.
  assert (FUEL <= m0) as HINT. { nia. }
  destruct e; simpl in *; eauto.
  - des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached2 reach_myself;
    try rep_with_rew reached1 reach_myself;
    try rep_with_rew reached0 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp. des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached2 reach_myself;
    try rep_with_rew reached1 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached2 IHFUEL;
    rep_eval idtac; eauto.
  - des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached1 reach_myself;
    try rep_with_rew reached0 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached1 IHFUEL;
    rep_eval idtac; eauto.
  - des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached1 reach_myself;
    try rep_with_rew reached0 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached1 IHFUEL;
    rep_eval idtac; eauto.
  - des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached1 reach_myself;
    try rep_with_rew reached0 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached1 IHFUEL;
    rep_eval idtac; eauto.
Qed.

Lemma reach_same `{time T} :
  forall FUEL e (C : @dy_ctx T) m t l l'
        (CONTAINED : forall cf, In cf l -> In cf l'),
    match (eval e C m t l FUEL), (eval e C m t l' FUEL) with
    | Resolved V m t reached, Resolved V' m' t' reached' => 
      V = V' /\ m = m' /\ t = t' /\ (forall cf, In cf reached -> In cf reached')
    | Error reached, Error reached'
    | Pending reached, Pending reached' =>
      forall cf, In cf reached -> In cf reached'
    | _, _ => False
    end.
Proof.
  rename H into ET. rename H0 into OT. rename H1 into TT.
  induction FUEL; intros.
  simpl. intros. destruct H; eauto.
  assert ((forall cf : config,
            In cf (Cf e C m t :: l) ->
            In cf (Cf e C m t :: l'))) as CONTAINED'.
  { intros. simpl in *. destruct H; eauto. }
  destruct e; simpl; eauto;
  try (
    (* trivial cases *)
    lazymatch goal with 
    | |- context [eval _ _ _ _ _ _] => fail
    | _ => idtac
    end;
    repeat des_goal; repeat des_hyp; clarify;
    repeat split; eauto;
    intros cf OR; simpl in *; destruct OR; eauto);
  match goal with
    | |- context [eval ?e ?C ?m ?t _ _] =>
      specialize (IHFUEL e C m t _ _ CONTAINED') as CONTAINED''
    | _ => fail
  end;
  repeat des_hyp; eauto;
  destruct CONTAINED'' as [? [? [? CONTAINED'']]]; subst;
  des_goal; repeat des_hyp; clarify;
  match goal with
  | |- context [eval ?e ?C ?m ?t _ _] =>
    specialize (IHFUEL e C m t _ _ CONTAINED'') as CONTAINED'''
  | _ => fail
  end;
  repeat des_hyp; clarify;
  destruct CONTAINED''' as [? [? [? CONTAINED''']]]; subst; eauto;
  match goal with
  | |- context [eval ?e ?C ?m ?t _ _] =>
    specialize (IHFUEL e C m t _ _ CONTAINED''') as CONTAINED''''
  | _ => fail
  end;
  repeat des_hyp; clarify;
  destruct CONTAINED'''' as [? [? [? ?]]]; clarify.
Qed.

Ltac separate_reach_tac cf IHFUEL HINT HINT' RR RR' :=
  match goal with
  | [H : context [match eval ?e ?C ?m ?t ?l ?n with _ => _ end] |-
      context [match eval ?e ?C ?m ?t ?l0 ?n with _ => _ end]] =>
    specialize (IHFUEL e C m t l cf) as HINT;
    specialize (IHFUEL e C m t l0 cf) as HINT';
    pose proof (reach_same n e C m t l0 l RR) as RR';
    clear RR
  | [H : context [match eval ?e ?C ?m ?t ?l ?n with _ => _ end] |-
      context [match eval ?e ?C ?m ?t ?l0 ?n with _ => _ end]] =>
    specialize (IHFUEL e C m t l cf) as HINT;
    specialize (IHFUEL e C m t l0 cf) as HINT';
    pose proof (reach_same n e C m t l l0 RR) as RR';
    clear RR
  | _ => fail
  end.

Lemma separate_reach `{time T} :
  forall FUEL e (C : @dy_ctx T) m t l cf,
    In cf (extract_reached (eval e C m t l FUEL)) <->
    In cf l \/ In cf (extract_reached (eval e C m t [] FUEL)).
Proof.
  rename H into ET. rename H0 into OT. rename H1 into TT.
  induction FUEL; intros;
  assert (forall cf, In cf [Cf e C m t] ->
            In cf (Cf e C m t :: l)) as CONTAINED;
  try (intros; simpl in *; destruct H; eauto; contradict);
  simpl; split; intros SPLIT.
  { destruct SPLIT; eauto. }
  { destruct SPLIT as [?|[?|?]]; eauto. contradict. }
  - destruct e;
    try (
      (* trivial cases *)
      lazymatch goal with 
      | |- context [eval _ _ _ _ _ _] => fail
      | _ => idtac
      end;
      repeat des_hyp; simpl in *;
      try destruct SPLIT as [?|[?|?]];
      try destruct SPLIT as [?|?]; eauto);
    separate_reach_tac cf IHFUEL HINT1 HINT1' CONTAINED RR;
    des_goal; des_hyp;
    try (destruct RR as [? [? [? RR]]]; subst; des_hyp);
    try (rewrite HINT1 in SPLIT;
      destruct SPLIT as [[?|?]|?]; eauto;
      right; rewrite HINT1'; simpl; eauto);
    separate_reach_tac cf IHFUEL HINT2 HINT2' RR RR';
    des_hyp; try des_goal; des_hyp;
    try (destruct RR' as [? [? [? RR']]]; subst; try des_hyp);
    try (rewrite HINT2 in SPLIT; destruct SPLIT as [SPLIT|?];
      try (rewrite HINT1 in SPLIT; destruct SPLIT as [[?|?]|?]);
      eauto;
      rewrite HINT2'; rewrite HINT1'; simpl; eauto).
    separate_reach_tac cf IHFUEL HINT3 HINT3' RR' RR''.
    des_goal; des_hyp;
    try (destruct RR'' as [? [? [? RR'']]]; subst; des_hyp);
    try (rewrite HINT3 in SPLIT; destruct SPLIT as [SPLIT|?];
      try (rewrite HINT2 in SPLIT; destruct SPLIT as [SPLIT|?];
        try (rewrite HINT1 in SPLIT; destruct SPLIT as [[?|?]|?]));
      eauto;
      rewrite HINT3'; rewrite HINT2'; rewrite HINT1'; simpl; eauto 7).
  - destruct e;
    try (
      (* trivial cases *)
      lazymatch goal with 
      | |- context [eval _ _ _ _ _ _] => fail
      | _ => idtac
      end;
      repeat des_hyp; simpl in *;
      try destruct SPLIT as [?|[?|[?|?]]];
      try destruct SPLIT as [?|[?|?]];
      try destruct SPLIT as [?|?]; eauto; contradict);
    separate_reach_tac cf IHFUEL HINT1 HINT1' CONTAINED RR;
    des_hyp; des_goal; try contradict;
    try (destruct RR as [? [? [? RR]]]; subst; des_hyp);
    try rewrite HINT1 in SPLIT; 
    try destruct SPLIT as [?|[[?|?]|?]];
    try rewrite HINT1';
    simpl in *; eauto; try contradict;
    try destruct ev;
    separate_reach_tac cf IHFUEL HINT2 HINT2' RR RR';
    des_hyp; des_goal; try contradict;
    try (destruct RR' as [? [? [? RR']]]; subst; des_hyp);
    try rewrite HINT2 in SPLIT;
    try destruct SPLIT as [?|[SPLIT|?]];
    try rewrite HINT1 in SPLIT;
    try destruct SPLIT as [[?|?]|?];
    try rewrite HINT2'; try rewrite HINT1';
    simpl in *; eauto; try contradict.
    separate_reach_tac cf IHFUEL HINT3 HINT3' RR' RR'';
    des_hyp; repeat des_goal; try contradict;
    try (destruct RR'' as [? [? [? RR'']]]; subst);
    try rewrite HINT3 in SPLIT;
    try destruct SPLIT as [?|[SPLIT|?]];
    try rewrite HINT2 in SPLIT;
    try destruct SPLIT as [SPLIT|?];
    try rewrite HINT1 in SPLIT;
    try destruct SPLIT as [[?|?]|?];
    try rewrite HINT3'; try rewrite HINT2'; try rewrite HINT1';
    simpl in *; eauto 7; try contradict.
Qed.

(*
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
    destruct (eval (C0 [|dy_binde x t ([||])|])
                   (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
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
    destruct (eval (C_lam [|dy_binde x t ([||])|])
                   (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
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
    destruct (eval (C_lam [|dy_binde x t ([||])|])
                   (ST (t !-> arg; mem) (tick C (ST mem t) x arg))
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
    destruct (eval (C [|dy_binde x t ([||])|])
                   (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
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
    destruct (eval (C [|dy_binde x t ([||])|])
                   (ST (t !-> v; mem) (tick C (ST mem t) x v))
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
    destruct (eval (C [|dy_bindm M mv ([||])|]) (ST mem t) m2 reached FUEL) eqn:EVAL2;
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
    destruct (eval (C [|dy_bindm M C_M ([||])|]) st_M m2 reached (Nat.max FUEL FUEL')) eqn:EVAL2;
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
      destruct (eval (C0 [|dy_binde x t ([||])|])
                     (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
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
      destruct (eval (C [|dy_binde x t ([||])|])
                     (ST (t !-> Closure x0 e C0; mem) (tick C (ST mem t) x (Closure x0 e C0)))
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
      destruct (eval (C [|dy_bindm M mv ([||])|]) st0 e2 reached FUEL) eqn:EVAL2;
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
      destruct (eval (C0 [|dy_binde x t ([||])|])
                     (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
                     e reached0 FUEL) eqn:BODY; eauto.
      destruct v; eauto.
      pose proof (reach_same FUEL (C0 [|dy_binde x t ([||])|])
                                  (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
                                  e [] reached0 (HINT _ reached0)) as R.
      rewrite BODY in R.
      destruct (eval (C0 [|dy_binde x t ([||])|])
                     (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
                     e [] FUEL) eqn:BODY'; try (inversion R; fail).
      specialize (IHFUEL (C0 [|dy_binde x t ([||])|])
                         (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
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
      destruct (eval (C [|dy_binde x t ([||])|])
                     (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
                     e2 reached FUEL) eqn:BODY; eauto.
      pose proof (reach_same FUEL (C [|dy_binde x t ([||])|])
                                  (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
                                  e2 [] reached (HINT _ reached)) as R.
      rewrite BODY in R.
      destruct (eval (C [|dy_binde x t ([||])|])
                     (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
                     e2 []) eqn:BODY'; try (inversion R; fail).
      specialize (IHFUEL (C [|dy_binde x t ([||])|])
                         (ST (t !-> ev; mem) (tick C (ST mem t) x ev))
                         e2). rewrite BODY' in IHFUEL.
      destruct R as [RR [RR' R]]. rewrite RR in *. rewrite RR' in *. clear RR RR'.
      destruct IHFUEL as [C' [e' [CONTAINED EVAL]]].
      destruct v; eauto.
    + destruct (eval C st e1 [Config C st (m_letm M e1 e2)] FUEL) eqn:EVALM; eauto.
      destruct v; eauto.
      destruct (eval (C [|dy_bindm M mv ([||])|]) st0 e2 reached FUEL) eqn:BODY; eauto.
      pose proof (reach_same FUEL (C [|dy_bindm M mv ([||])|]) st0 e2 [] reached (HINT _ reached)) as R.
      rewrite BODY in R.
      destruct (eval (C [|dy_bindm M mv ([||])|]) st0 e2 []) eqn:BODY'; try (inversion R; fail).
      specialize (IHFUEL (C [|dy_bindm M mv ([||])|]) st0 e2). rewrite BODY' in IHFUEL.
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
*)
