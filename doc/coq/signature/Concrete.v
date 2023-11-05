From Signature Require Export Syntax.

Generalizable Variables T.

Class time `{TotalOrder T} :=
{
  tick : dy_ctx T -> memory T -> T -> ID -> expr_value T -> T;
  (* functional extensionality *)
  tick_ext : forall C m m' t x v (EQ : same m m'), tick C m t x v = tick C m' t x v;
  (* fresh timestamp *)
  tick_lt : forall C mem t x v, t << tick C mem t x v
}.

Inductive step `{time T} : (config T) -> (config T) -> Prop :=
  | ExprID x C m t v addr
    (ADDR : addr_x C x = Some addr)
    (ACCESS : read m addr = Some v)
    : step (Cf (e_var x) C m t) (Rs (EVal v) m t)

  | Fn x e C m t
    : step (Cf (e_lam x e) C m t) (Rs (EVal (Fun x e C)) m t)
  
  | EAppL e1 e2 C m t
    : step (Cf (e_app e1 e2) C m t) (Cf e1 C m t)

  | FnEAppR e1 e2 C m t x e C_f m_f t_f
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    : step (Cf (e_app e1 e2) C m t) (Cf e2 C m_f t_f)

  | FtEAppR e1 e2 C m t M s_M e C_f m_f t_f
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    : step (Cf (e_app e1 e2) C m t) (Cf e2 C m_f t_f)
  
  | FnEAppBody e1 e2 C m t x e C_f m_f t_f v m_a t_a
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    : step (Cf (e_app e1 e2) C m t) (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v))

  | FtEAppBody e1 e2 C m t M s_M e C_f m_f t_f C_v m_a t_a C_M
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    : step (Cf (e_app e1 e2) C m t) (Cf e (dy_bindm M C_M C_f) m_a t_a)
  
  | FnEApp e1 e2 C m t x e C_f m_f t_f v m_a t_a v' m' t'
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    (BODY : step (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v)) (Rs (EVal v') m' t'))
    : step (Cf (e_app e1 e2) C m t) (Rs (EVal v') m' t')
  
  | FtEApp e1 e2 C m t M s_M e C_f m_f t_f C_v m_a t_a C_M v' m' t'
    (FN : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    (BODY : step (Cf e (dy_bindm M C_M C_f) m_a t_a) (Rs (EVal v') m' t'))
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
    : step (Cf (m_var M) C m t) (Rs (MVal (C_M[|C|])) m t)
  
  | Ft M e s_M C m t
    : step (Cf (m_lam M s_M e) C m t) (Rs (EVal (Func M s_M e C)) m t)

  | MAppL e1 e2 s C m t
    : step (Cf (m_app e1 e2 s) C m t) (Cf e1 C m t)

  | FnMAppR e1 e2 s C m t x e C_f m_f t_f
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e2 C m_f t_f)

  | FtMAppR e1 e2 s C m t M s_M e C_f m_f t_f
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e2 C m_f t_f)
  
  | FnMAppBody e1 e2 s C m t x e C_f m_f t_f v m_a t_a
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v))

  | FtMAppBody e1 e2 s C m t M s_M e C_f m_f t_f C_v m_a t_a C_M
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    : step (Cf (m_app e1 e2 s) C m t) (Cf e (dy_bindm M C_M C_f) m_a t_a)
  
  | FnMApp e1 e2 s C m t x e C_f m_f t_f v m_a t_a C' m' t' C_s
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    (BODY : step (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v)) (Rs (MVal C') m' t'))
    (PROJs : project C' s = Some C_s)
    : step (Cf (m_app e1 e2 s) C m t) (Rs (MVal (C_s[|C|])) m' t')
  
  | FtMApp e1 e2 s C m t M s_M e C_f m_f t_f C_v m_a t_a C_M C' m' t' C_s
    (FN : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    (BODY : step (Cf e (dy_bindm M C_M C_f) m_a t_a) (Rs (MVal C') m' t'))
    (PROJs : project C' s = Some C_s)
    : step (Cf (m_app e1 e2 s) C m t) (Rs (MVal (C_s[|C|])) m' t')
.

#[export] Hint Constructors step : core.

Inductive multi_step `{time T} : (@config T) -> (@config T) -> Prop :=
  | Refl cf : multi_step cf cf
  | Trans cf cf' cf''
    (REACHl : step cf cf')
    (REACHr : multi_step cf' cf'')
    : multi_step cf cf''
.

#[export] Hint Constructors multi_step : core.

Notation "'{|' ll '~>' rr '|}'" := 
  (step ll rr) 
  (at level 10, ll at next level, rr at next level).

Notation "'{|' ll '~>*' rr '|}'" := 
  (multi_step ll rr) 
  (at level 10, ll at next level, rr at next level).

Inductive interpreter_state `{time T} :=
  | Pending (reached : list (config T))
  | Error (reached : list (config T)) (* Type error *)
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
        match read m addr with
        | None => Error reached
        | Some v => Resolved (EVal v) m t ((Rs (EVal v) m t) :: reached)
        end
      end
    | e_lam x e =>
      let v := Fun x e C in
      Resolved (EVal v) m t ((Rs (EVal v) m t) :: reached)
    | e_app e1 e2 =>
      match eval e1 C m t reached FUEL' with
      | Resolved (EVal (Fun x e C_f)) m_f t_f reached' =>
        match eval e2 C m_f t_f reached' FUEL' with
        | Resolved (EVal v) m_a t_a reached'' =>
          match eval e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v) reached'' FUEL' with
          | Resolved (EVal v') m' t' reached''' => Resolved (EVal v') m' t' reached'''
          | Resolved _ _ _ reached''' => Error reached'''
          | other => other
          end
        | Resolved _ _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved (EVal (Func M s_M e C_f)) m_f t_f reached' =>
        match eval e2 C m_f t_f reached' FUEL' with
        | Resolved (MVal C_v) m_a t_a reached'' =>
          match project C_v s_M with
          | None => Error reached''
          | Some C_M =>
          match eval e (dy_bindm M C_M C_f) m_a t_a reached'' FUEL' with
          | Resolved (EVal v') m' t' reached''' => Resolved (EVal v') m' t' reached'''
          | Resolved _ _ _ reached''' => Error reached'''
          | other => other
          end end
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
      | Some C_M => Resolved (MVal (C_M[|C|])) m t ((Rs (MVal (C_M[|C|])) m t) :: reached)
      end
    | m_lam M s e =>
      let v := Func M s e C in
      Resolved (EVal v) m t ((Rs (EVal v) m t) :: reached)
    | m_app e1 e2 s =>
      match eval e1 C m t reached FUEL' with
      | Resolved (EVal (Fun x e C_f)) m_f t_f reached' =>
        match eval e2 C m_f t_f reached' FUEL' with
        | Resolved (EVal v) m_a t_a reached'' =>
          match eval e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v) reached'' FUEL' with
          | Resolved (MVal C') m' t' reached''' =>
            match project C' s with
            | Some C'' => Resolved (MVal (C''[|C|])) m' t' 
              ((Rs (MVal (C''[|C|])) m' t') :: reached''')
            | None => Error reached'''
            end
          | Resolved _ _ _ reached''' => Error reached'''
          | other => other
          end
        | Resolved _ _ _ reached'' => Error reached''
        | other => other
        end
      | Resolved (EVal (Func M s_M e C_f)) m_f t_f reached' =>
        match eval e2 C m_f t_f reached' FUEL' with
        | Resolved (MVal C_v) m_a t_a reached'' =>
          match project C_v s_M with
          | None => Error reached''
          | Some C_M =>
          match eval e (dy_bindm M C_M C_f) m_a t_a reached'' FUEL' with
          | Resolved (MVal C') m' t' reached''' => 
            match project C' s with
            | Some C'' => Resolved (MVal (C''[|C|])) m' t'
              ((Rs (MVal (C''[|C|])) m' t') :: reached''')
            | None => Error reached'''
            end
          | Resolved _ _ _ reached''' => Error reached'''
          | other => other
          end end
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
  | |- context [match project ?C ?s with _ => _ end] =>
    let PROJ := fresh "PROJ" in
    destruct (project C s) eqn:PROJ; clarify;
    rep_eval SOLVER
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
    rep_eval IHFUEL; eauto;
    rep_eval IHFUEL; eauto.
    all:rep_eval IHFUEL.
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
  try solve 
    [do 3 (rep_eval IHFUEL; eauto) |
     do 3 (rep_eval relax_fuel; eauto)].
  all: rep_eval relax_fuel; rep_eval IHFUEL; eauto.
Qed.

Lemma Eval_well_defined_l :
  forall `{time T} e (C : @dy_ctx T) m t V m' t' 
    (R : {| Cf e C m t ~> Rs V m' t' |}) l,
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
  - exists 1; simpl; eauto.
  - edestruct IHR1 as [FUEL' EQ']; eauto. clear IHR1. des_hyp.
    edestruct IHR2 as [FUEL'' EQ'']; eauto. clear IHR2. des_hyp.
    edestruct IHR3 as [FUEL''' EQ''']; eauto. clear IHR3. des_hyp.
    exists (S (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))).
    simpl.
    destruct EQ' as [? [? ?]]. subst.
    destruct EQ'' as [? [? ?]]. subst.
    destruct EQ''' as [? [? ?]]. subst.
    do 4 rep_eval relax_fuel.
  - edestruct IHR1 as [FUEL' EQ']; eauto. clear IHR1. des_hyp.
    edestruct IHR2 as [FUEL'' EQ'']; eauto. clear IHR2. des_hyp.
    edestruct IHR3 as [FUEL''' EQ''']; eauto. clear IHR3. des_hyp.
    exists (S (Nat.max FUEL' (Nat.max FUEL'' FUEL'''))).
    simpl.
    destruct EQ' as [? [? ?]]. subst.
    destruct EQ'' as [? [? ?]]. subst.
    destruct EQ''' as [? [? ?]]. subst.
    do 4 rep_eval relax_fuel.
Qed.

Ltac interp_to_rel SOLVER :=
  match goal with
  | [H : eval ?e ?C ?m ?t ?reached _ = Resolved ?V ?m0 ?t0 _ |- _] =>
    let REL := fresh "REL" in
    assert (REL : {| Cf e C m t ~> Rs V m0 t0 |});
    try (apply SOLVER with (l := reached); rewrite H; eauto);
    move H at top
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
  intros; split; intros RR;
  try apply Eval_well_defined_l; eauto.
  destruct RR as [FUEL EVAL].
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
  end;
  match goal with
  | _ => apply KILLER; try right; simpl; eauto
  end.

Lemma reach_myself `{time T} :
  forall FUEL e (C : @dy_ctx T) m t l cf,
    In cf (Cf e C m t :: l) -> In cf (extract_reached (eval e C m t l FUEL)).
Proof.
  induction FUEL; intros; try (simpl; eauto; fail).
  simpl. destruct e; repeat des_goal; simpl; eauto;
  try right;
  try rep_with_rew reached1 IHFUEL;
  try rep_with_rew reached0 IHFUEL;
  try rep_with_rew reached IHFUEL.
Qed.

Lemma reach_myself_eval `{time T} :
  forall FUEL e (C : @dy_ctx T) m t l,
  match eval e C m t l FUEL with
  | Resolved V m' t' l' => In (Rs V m' t') l'
  | _ => True
  end.
Proof.
  induction FUEL; intros; try (simpl; eauto; fail);
  destruct e; simpl; repeat des_goal; eauto;
  repeat des_hyp; clarify; simpl; eauto;
  try match goal with
  | |- In (Rs ?V ?m' ?t') ?l' =>
    match goal with
    | [RR : eval ?e ?C ?m ?t ?l ?FUEL = Resolved V m' t' l' |- _] =>
      specialize (IHFUEL e C m t l);
      rewrite RR in IHFUEL
    end
  end; eauto.
Qed.

Ltac clar_eval := 
  match goal with
  | [H : eval ?e ?C ?m ?t ?l _ = Error _ |- 
      context [eval ?e ?C ?m ?t ?l _]] =>
    rep_eval relax_fuel_err; eauto
  | [H : eval ?e ?C ?m ?t ?l _ = Resolved _ _ _ _ |-
      context [eval ?e ?C ?m ?t ?l _]] =>
    rep_eval relax_fuel; eauto
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
    des_hyp.
    des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached2 reach_myself;
    try rep_with_rew reached1 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached2 IHFUEL;
    rep_eval idtac; eauto.
    des_hyp; try clar_eval.
    repeat des_goal;
    try rep_with_rew reached2 reach_myself;
    try rep_with_rew reached1 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval; eauto.
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
    repeat des_goal; try right;
    try rep_with_rew reached2 reach_myself;
    try rep_with_rew reached1 reach_myself;
    try rep_with_rew reached0 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp.
    des_hyp; try clar_eval.
    repeat des_goal; try right;
    try rep_with_rew reached2 reach_myself;
    try rep_with_rew reached1 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval.
    repeat des_goal; try right;
    try rep_with_rew reached2 IHFUEL;
    rep_eval idtac; eauto.
    des_hyp; try clar_eval.
    repeat des_goal; try right;
    try rep_with_rew reached2 reach_myself;
    try rep_with_rew reached1 IHFUEL;
    try rep_eval idtac; eauto.
    des_hyp; simpl; eauto.
    des_hyp; try clar_eval; eauto.
    des_hyp; try clar_eval.
    repeat des_goal; try right;
    try rep_with_rew reached2 IHFUEL;
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
  assert ((forall cf : config T,
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
  end;
  repeat des_hyp; eauto;
  destruct CONTAINED'' as [? [? [? CONTAINED'']]]; subst;
  des_goal; repeat des_hyp; clarify;
  match goal with
  | |- context [eval ?e ?C ?m ?t _ _] =>
    specialize (IHFUEL e C m t _ _ CONTAINED'') as CONTAINED'''
  end;
  repeat des_hyp; clarify;
  destruct CONTAINED''' as [? [? [? CONTAINED''']]]; subst; eauto;
  try match goal with
  | |- context [project ?C ?s] =>
    let PROJ := fresh "PROJ" in
    destruct (project C s) eqn:PROJ; clarify
  end;
  match goal with
  | |- context [eval ?e ?C ?m ?t _ _] =>
    specialize (IHFUEL e C m t _ _ CONTAINED''') as CONTAINED''''
  end;
  repeat des_hyp; clarify;
  destruct CONTAINED'''' as [? [? [? ?]]]; clarify;
  rw; repeat split; ii; ss; des; eauto.
Qed.

Ltac separate_reach_tac cf IHFUEL HINT HINT' RR RR' :=
  match goal with
  | |- context [project ?C ?s] =>
    let PROJ := fresh "PROJ" in
    destruct (project C s) eqn:PROJ; clarify;
    separate_reach_tac cf IHFUEL HINT HINT' RR RR'
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
    try match goal with
    | |- context [project ?C ?s] =>
      let PROJ := fresh "PROJ" in
      destruct (project C s) eqn:PROJ; clarify
    end;
    try (rewrite HINT2 in SPLIT; destruct SPLIT as [SPLIT|?];
      try (rewrite HINT1 in SPLIT; destruct SPLIT as [[?|?]|?]);
      eauto;
      rewrite HINT2'; rewrite HINT1'; simpl; eauto);
    separate_reach_tac cf IHFUEL HINT3 HINT3' RR' RR'';
    des_goal; des_hyp;
    try (destruct RR'' as [? [? [? RR'']]]; subst; des_hyp);
    try match goal with
    | |- context [project ?C ?s] =>
      let PROJ := fresh "PROJ" in
      destruct (project C s) eqn:PROJ; clarify;
      ss;
      match type of SPLIT with
      | _ \/ In ?cf ?l =>
        destruct SPLIT as [SPLIT | SPLIT]
      | _ => idtac
      end
    end; ss;
    try (rewrite HINT3 in SPLIT; destruct SPLIT as [SPLIT|?];
      try (rewrite HINT2 in SPLIT; destruct SPLIT as [SPLIT|?];
        try (rewrite HINT1 in SPLIT; destruct SPLIT as [[?|?]|?]));
      eauto;
      rewrite HINT3'; rewrite HINT2'; rewrite HINT1'; simpl; eauto 7).
    all:eauto.
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
    try match goal with
    | |- context [project ?C ?s] =>
      let PROJ := fresh "PROJ" in
      destruct (project C s) eqn:PROJ; clarify
    end;
    try rewrite HINT2 in SPLIT;
    try destruct SPLIT as [?|[SPLIT|?]];
    try rewrite HINT1 in SPLIT;
    try destruct SPLIT as [[?|?]|?];
    try rewrite HINT2'; try rewrite HINT1';
    simpl in *; eauto; try contradict;
    separate_reach_tac cf IHFUEL HINT3 HINT3' RR' RR'';
    des_hyp; repeat des_goal; try contradict;
    try (destruct RR'' as [? [? [? RR'']]]; subst);
    try match goal with
    | SPLIT : context [project ?C ?s], RR : project ?C ?s = _ |- _ =>
      rewrite RR in SPLIT; ss;
      try destruct SPLIT as [SPLIT | SPLIT]
    end; ss;
    try rewrite HINT3 in SPLIT;
    try destruct SPLIT as [?|[SPLIT|?]];
    try rewrite HINT2 in SPLIT;
    try destruct SPLIT as [SPLIT|?];
    try rewrite HINT1 in SPLIT;
    try destruct SPLIT as [[?|?]|?];
    try rewrite HINT3'; try rewrite HINT2'; try rewrite HINT1';
    simpl in *; eauto 7; try contradict.
    all:des; clarify; eauto.
Qed.

Lemma Reach_well_defined_l `{time T} :
  forall e (C : dy_ctx T) m t cf' (R : {| (Cf e C m t) ~> cf' |}),
    exists FUEL,
      In cf' (extract_reached (eval e C m t [] FUEL)).
Proof.
  intros. remember (Cf e C m t) as cf.
  ginduction R; intros; clarify;
  try (exists 1; simpl; repeat des_goal; clarify; eauto; fail);
  repeat match goal with
  | [IH : context [Cf ?e ?C ?m ?t = _ -> _] |- _] =>
    let FUEL := fresh "FUEL" in
    let CONTAINED := fresh "CONTAINED" in
    specialize (IH e C m t eq_refl);
    destruct IH as [FUEL CONTAINED]
  | [R : {| (Cf ?e ?C ?m ?t) ~> (Rs ?V' ?m' ?t') |} |- _] =>
    let EVAL := fresh "EVAL" in
    pose proof (Eval_well_defined_l e C m t V' m' t' R) as EVAL;
    clear R
  end;
  match goal with
  | |- exists n, In ?cf (extract_reached (eval ?e ?C ?m ?t _ n)) =>
    repeat match goal with
    | [H : forall l, exists n, 
      match eval ?e' _ _ _ l n with _ => _ end |- _] =>
      let FUEL := fresh "FUEL" in
      let RR := fresh "RR" in
      match e with
      | e_app ?e1 ?e2 =>
        match e' with
        | e1 => specialize (H [Cf e C m t]); destruct H as [FUEL RR]
        | e2 => 
          match goal with 
          | [_ : eval e1 _ _ _ _ _ = Resolved _ _ _ ?ll |- _] =>
            specialize (H ll); destruct H as [FUEL RR]
          end
        | _ =>
          match goal with
          | [_ : eval e2 _ _ _ _ _ = Resolved _ _ _ ?ll |- _] =>
            specialize (H ll); destruct H as [FUEL RR]
          end
        end
      | e_link ?e1 ?e2 =>
        match e' with
        | e1 => specialize (H [Cf e C m t]); destruct H as [FUEL RR]
        | e2 =>
          match goal with
          | [_ : eval e1 _ _ _ _ _ = Resolved _ _ _ ?ll |- _] =>
            specialize (H ll); destruct H as [FUEL RR]
          end
        end
      | m_app ?e1 ?e2 ?s =>
        match e' with
        | e1 => specialize (H [Cf e C m t]); destruct H as [FUEL RR]
        | e2 => 
          match goal with 
          | [_ : eval e1 _ _ _ _ _ = Resolved _ _ _ ?ll |- _] =>
            specialize (H ll); destruct H as [FUEL RR]
          end
        | _ =>
          match goal with
          | [_ : eval e2 _ _ _ _ _ = Resolved _ _ _ ?ll |- _] =>
            specialize (H ll); destruct H as [FUEL RR]
          end
        end
      end; des_hyp; try (destruct RR as [? [? ?]]; subst)
    end
  end;
  match goal with
  | [_ : eval _ _ _ _ _ ?n = Resolved _ _ _ _ |- _] =>
    match goal with
    | [_ : eval _ _ _ _ _ ?n0 = Resolved _ _ _ _ |- _] =>
      lazymatch n0 with
      | n => fail
      | _ =>
        match goal with
        | [_ : eval _ _ _ _ _ ?n1 = Resolved _ _ _ _ |- _] =>
          lazymatch n1 with
          | n => fail
          | n0 => fail
          | _ => exists (S (Nat.max n (Nat.max n0 n1)))
          end
        | _ => exists (S (Nat.max n n0))
        end
      end
    | _ => exists (S n)
    end
  end; simpl;
  repeat rep_eval relax_fuel;
  repeat rw;
  try match goal with
  | [RR : eval ?e ?C ?m ?t ?l ?n = Resolved ?V ?m' ?t' ?l' |- 
    In _ (extract_reached (Resolved ?V ?m' ?t' ?l'))] =>
    let H := fresh "H" in
    pose proof (reach_myself_eval n e C m t l) as H;
    rewrite RR in H; eauto
  | |- context [match eval ?e ?C ?m ?t ?l ?n with | _ => _ end] =>
    let H := fresh "H" in
    assert (In (Cf e C m t) (extract_reached (eval e C m t l n))) as H;
    try (apply reach_myself; simpl; eauto);
    repeat des_goal; eauto; try right;
    rep_with_rew reached1 reach_myself
  end.
  all:s; eauto.
Qed.

Lemma Reach_well_defined_r `{time T} :
  forall FUEL e (C : @dy_ctx T) m t cf'
         (R : In cf' (extract_reached (eval e C m t [] FUEL))),
  {|(Cf e C m t) ~>* cf'|}.
Proof.
  induction FUEL; intros; simpl in *.
  destruct R as [R | R]; inversion R; eauto.
  repeat des_hyp;
  repeat match goal with
  | [RR : eval ?e ?C ?m ?t ?l ?n = _ |- _] =>
    let H := fresh "H" in
    assert (In cf' (extract_reached (eval e C m t l n))) as H;
    try (rewrite RR; simpl; eauto);
    rewrite separate_reach in H;
    clear RR; simpl in *
  | H : _ \/ _ |- _ => destruct H as [?|?]
  | _ => clarify; try contradict; eauto
  end;
  repeat match goal with
  | [H : In cf' (extract_reached (eval ?e ?C ?m ?t [] ?n)) |- _] =>
    apply IHFUEL in H
  | [H : eval ?e ?C ?m ?t _ _ = Resolved ?V ?m' ?t' _ |- _] =>
    assert ({|(Cf e C m t) ~> (Rs V m' t')|});
    try (eapply Eval_well_defined_r; rewrite H; eauto);
    clear H
  end; eauto.
Qed.

Theorem Reach_well_defined `{time T}:
  forall e (C : @dy_ctx T) m t cf',
    (exists FUEL, In cf' (extract_reached (eval e C m t [] FUEL))) <->
    {| (Cf e C m t) ~>* cf' |}.
Proof.
  split; intros REACH; 
  try (destruct REACH as [FUEL REACH]; eapply Reach_well_defined_r; eauto).
  remember (Cf e C m t) as cf.
  ginduction REACH; intros; subst.
  exists 0. simpl. eauto.
  apply Reach_well_defined_l in REACHl.
  destruct REACHl as [FUEL IN].
  destruct cf'; inversion REACH; subst; eauto;
  match goal with
  | [contra : {|(Rs _ _ _) ~> _|}|-_] => inversion contra
  | [H : forall e C m t, Cf ?e' ?C' ?m' ?t' = Cf e C m t -> _ |- _] =>
    let FUEL := fresh "FUEL'" in
    let IN := fresh "IN'" in
    specialize (H e' C' m' t' eq_refl);
    destruct H as [FUEL IN]; move FUEL at top
  end.
  clear REACH REACHl REACHr cf'.
  exists (FUEL + FUEL').
  ginduction FUEL; intros.
  destruct IN as [IN|IN]; clarify; eauto.
  simpl in IN.
  repeat des_hyp;
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [?|?]
  | _ => clarify; eauto 2
  end;
  try (apply relax_fuel_reach with (FUEL := FUEL'); try nia; assumption);
  repeat match goal with
  | H : In (Cf ?e0 ?C0 ?m0 ?t0) ?l0 |- _ =>
    let IN := fresh "IN" in
    match goal with
    | RR : eval ?e ?C ?m ?t ?l ?n = _ |- _ =>
      match type of RR with
      | context [l0] =>
        replace l0 with (extract_reached (eval e C m t l n)) in H;
        try (rewrite RR; reflexivity);
        rewrite separate_reach in H;
        destruct H as [H | H]; 
        simpl in H; try (destruct H; clarify)
      end
    end
  end;
  try (apply relax_fuel_reach with (FUEL := FUEL'); try nia; assumption);
  eapply IHFUEL in IN'; eauto; simpl;
  repeat match goal with
  | H : eval ?e ?C ?m ?t ?l ?n = ?r |- 
    context [eval ?e ?C ?m ?t ?l (?n + ?n0)] =>
    let RR := fresh "RR" in
    match type of H with
    | context [Error] =>
      assert (eval e C m t l (n + n0) = r) as RR;
      first [apply relax_fuel_err with (FUEL := n); eauto; nia|
      rewrite RR]
    | context [Resolved] =>
      assert (eval e C m t l (n + n0) = r) as RR;
      first [apply relax_fuel with (FUEL := n); eauto; nia|
      rewrite RR]
    end
  end; simpl; repeat des_goal; clarify; try right;
  repeat match goal with
  | RR : eval ?e ?C ?m ?t ?l ?n = ?r |- In cf'' ?ll =>
    match type of RR with
    | context [ll] =>
      replace ll with (extract_reached (eval e C m t l n));
      try (rewrite RR; reflexivity);
      rewrite separate_reach;
      first [right; assumption | left]
    end
  end.
Qed.
