From Simple Require Export Bound.

Generalizable Variables T.

Lemma read_top `{Eq T} :
  forall a b t,
  read (a ++ b) t = 
  match read a t with
  | None => read b t
  | Some _ => read a t
  end.
Proof.
  induction a; ii; ss;
  repeat des_goal; repeat des_hyp; clarify;
  repeat rw; reflexivity.
Qed.

Lemma app_same `{Eq T} :
  forall l l' m m'
    (SAMEl : same l l')
    (SAMEm : same m m'),
    same (l ++ m) (l' ++ m').
Proof.
  pose proof read_top.
  ii. repeat rw. unfold same in SAMEl.
  repeat des_goal; clarify;
  repeat match goal with
  | H : read _ _ = _ |- _ => symmetry in H
  end;
  first [rewrite SAMEl in * | rewrite <- SAMEl in *];
  match goal with
  | _ : ?a = read ?l ?t, _ : ?b = read ?l ?t |- _ =>
    assert (a = b); clarify; repeat rw; eauto
  end.
Qed.

Lemma disj_reflect `{Eq T} :
  forall m m',
  (forall t (READ : None <> read m t), None = read m' t) <->
  (forall t (READ : None <> read m' t), None = read m t).
Proof.
  induction m; ii; ss;
  repeat des_goal; clarify.
  split; intros IN ? ?; try des_goal; try des_hyp; clarify.
  - rewrite eqb_eq in *; clarify.
    exfalso. apply READ. apply IN. rewrite t_refl.
    red; ii; clarify.
  - assert (forall t, None <> read m' t -> None = read m t); eauto.
    rewrite <- IHm.
    ii. apply IN. red; ii; des_hyp; clarify.
  - rewrite eqb_eq in *; clarify.
    specialize (IN t0). rewrite t_refl in *.
    destruct (read m' t0); eauto.
    assert (None = Some e); clarify.
    apply IN; red; ii; clarify.
  - assert (forall t, None <> read m t -> None = read m' t); eauto.
    rewrite IHm.
    ii. specialize (IN t1). apply IN in READ0.
    des_hyp; clarify.
Qed.

Lemma app_disj_same `{Eq T} :
  forall m m' (DISJ : forall t (READ : None <> read m t), None = read m' t),
  same (m ++ m') (m' ++ m).
Proof.
  induction m; ii; ss.
  - rewrite app_nil_r. eauto.
  - des_goal.
    assert (None = read m' t0).
    apply DISJ. rewrite t_refl. red; ii; clarify.
    des_goal; clarify.
    + rewrite eqb_eq in *; clarify.
      clear IHm DISJ.
      ginduction m'; ii; ss. rewrite t_refl. eauto.
      repeat des_hyp; clarify; eauto.
    + assert (read (m' ++ (t0, e) :: m) t = read (m' ++ m) t) as RR.
      {
        clear H0 v DISJ IHm.
        ginduction m'; ii; ss. rw. eauto.
        repeat des_goal; clarify; eauto.
      }
      rewrite RR.
      apply IHm. ii. apply DISJ.
      red; ii. repeat des_hyp; clarify.
Qed.

Lemma eq_node_neq `{Eq T} :
  forall n n', eq_node n n' = false <-> n <> n'.
Proof.
  assert (eq_node = eqb) as RR. reflexivity.
  rewrite RR in *. exact eqb_neq.
Qed.

Lemma same_comm `{Eq T} :
  forall m m',
  same m m' <-> same m' m.
Proof.
  intros; unfold same; split; ii; rw; eauto.
Qed.

Lemma same_trans `{Eq T} :
  forall m m' m'' (SAME : same m m') (SAME' : same m' m''),
  same m m''.
Proof.
  ii. unfold same in *. rewrite SAME. rewrite SAME'. eauto.
Qed.

Inductive edge T :=
  | Ex (nC : node T) (x : ID) (ntx : node T)
  | EM (nC : node T) (M : ID) (nCM : node T)
  | Ev (nt : node T) (v : value) (nCv : node T)
.

Arguments Ex {T}.
Arguments EM {T}.
Arguments Ev {T}.

Definition eq_val (v v' : value) :=
  match v, v' with
  | v_fn x e, v_fn x' e' => eqb x x' && eqb e e'
  end.

Lemma eq_val_eq :
  forall v v', eq_val v v' = true <-> v = v'.
Proof.
  ii. unfold eq_val.
  repeat des_goal; try rewrite eqb_ID_eq in *; clarify.
  rewrite eq_tm_eq. split; ii; clarify.
  rewrite eqb_ID_neq in *.
  split; ii; clarify.
Qed.

#[export] Instance EqVal : Eq value :=
  { eqb := eq_val; eqb_eq := eq_val_eq; }.

Lemma eq_val_neq :
  forall v v', eq_val v v' = false <-> v <> v'.
Proof.
  assert (eq_val = eqb) as RR. eauto.
  rewrite RR. exact eqb_neq.
Qed.

Definition eq_edge `{Eq T} (e e' : edge T) :=
  match e, e' with
  | Ex nC x ntx, Ex nC' x' ntx' =>
    eqb nC nC' && eqb x x' && eqb ntx ntx'
  | EM nC M nCM, EM nC' M' nCM' =>
    eqb nC nC' && eqb M M' && eqb nCM nCM'
  | Ev nt v nCv, Ev nt' v' nCv' =>
    eqb nt nt' && eqb v v' && eqb nCv nCv'
  | _, _ => false
  end.

Lemma eq_edge_eq `{Eq T} :
  forall e e', eq_edge e e' = true <-> e = e'.
Proof.
  ii. unfold eq_edge.
  repeat des_goal; repeat des_hyp;
  try rewrite eqb_ID_eq in *; 
  try rewrite eqb_ID_neq in *;
  try rewrite eq_node_eq in *;
  try rewrite eq_node_neq in *;
  try rewrite eq_val_eq in *;
  try rewrite eq_val_neq in *;
  split; ii; clarify.
Qed.

#[export] Instance EqEdge `{Eq T} : Eq (edge T) :=
  { eqb := eq_edge; eqb_eq := eq_edge_eq; }.

Lemma eq_edge_neq `{Eq T} :
  forall e e', eq_edge e e' = false <-> e <> e'.
Proof.
  assert (eq_edge = eqb) as RR. eauto.
  rewrite RR. exact eqb_neq.
Qed.

Definition valid_edge `{Eq T} (m : memory T) (e : edge T) :=
  match e with
  | Ex (Ctx C) x (Ptr tx) =>
    match addr_x C x with
    | Some t => t = tx
    | None => False
    end
  | EM (Ctx C) M (Ctx CM) =>
    match ctx_M C M with
    | Some C => C = CM
    | None => False
    end
  | Ev (Ptr t) v (Ctx Cv) =>
    exists ev, Some ev = read m t /\
    match ev with
    | Closure x e C =>
      v = v_fn x e /\ C = Cv
    end
  | _ => False
  end.

Definition avalid_edge `{Eq T} (m : memory T) (e : edge T) :=
  match e with
  | Ex (Ctx C) x (Ptr tx) =>
    match addr_x C x with
    | Some t => t = tx
    | None => False
    end
  | EM (Ctx C) M (Ctx CM) =>
    match ctx_M C M with
    | Some C => C = CM
    | None => False
    end
  | Ev (Ptr t) v (Ctx Cv) =>
    exists ev, In ev (aread m t) /\
    match ev with
    | Closure x e C =>
      v = v_fn x e /\ C = Cv
    end
  | _ => False
  end.

Lemma same_valid_edge `{Eq T} :
  forall e m m' (SAME : same m m')
    (VALe : valid_edge m e),
  valid_edge m' e.
Proof.
  ii. unfold valid_edge.
  repeat des_goal; repeat des_hyp; clarify;
  ss; repeat des_hyp; clarify.
  des. repeat des_hyp; clarify.
  des; clarify.
  exists (Closure x e C). eauto.
  unfold same in SAME.
  rewrite <- SAME. eauto.
Qed.

Lemma asame_avalid_edge `{Eq T} :
  forall e m m' (SAME : asame m m')
    (VALe : avalid_edge m e),
  avalid_edge m' e.
Proof.
  ii. unfold avalid_edge.
  repeat des_goal; repeat des_hyp; clarify;
  ss; repeat des_hyp; clarify.
  des. repeat des_hyp; clarify.
  des; clarify.
  exists (Closure x e C). eauto.
  unfold asame in SAME.
  rewrite <- SAME. eauto.
Qed.

Fixpoint Edges `{Eq T} (n : node T) (p : path T) :=
  match p with
  | Pnil => []
  | Px x n' tl => Ex n x n' :: Edges n' tl
  | PM M n' tl => EM n M n' :: Edges n' tl
  | Pv v n' tl => Ev n v n' :: Edges n' tl
  end.

Lemma vpath_iff_vedge `{Eq T} :
  forall p m n,
    valid_path n m p <->
    forall e (IN : In e (Edges n p)), valid_edge m e.
Proof.
  induction p; ii; ss; repeat des_goal; repeat des_hyp; clarify; des;
  split; ii; des; clarify; ltac:(
  let HH := fresh "HH" in
  match goal with
  | H : forall e, Ex ?n ?x ?n' = e \/ _ -> _ |- _ =>
    specialize (H (Ex n x n')) as HH; 
    exploit HH; eauto;
    ii; ss; repeat des_hyp; clarify
  | H : forall e, EM ?n ?M ?n' = e \/ _ -> _ |- _ =>
    specialize (H (EM n M n')) as HH; 
    exploit HH; eauto;
    ii; ss; repeat des_hyp; clarify
  | H : forall e, Ev ?n ?v ?n' = e \/ _ -> _ |- _ =>
    specialize (H (Ev n v n')) as HH; 
    exploit HH; eauto;
    ii; ss; repeat des_hyp; clarify
  | _ => idtac
  end).
  - ss; des_goal; clarify.
  - rewrite IHp in *. eauto.
  - split; try rewrite IHp; ii; eauto.
  - ss; des_goal; clarify.
  - rewrite IHp in *. eauto.
  - split; try rewrite IHp; ii; eauto.
  - ss. exists ev. 
    des_goal; des; repeat split; clarify.
  - des_hyp; des; clarify.
    rewrite IHp in *; eauto.
  - des. exists ev.
    des_goal; des; repeat split; clarify.
    rewrite IHp; ii; eauto.
Qed.

Lemma avpath_iff_avedge `{Eq T} :
  forall p m n,
    avalid_path n m p <->
    forall e (IN : In e (Edges n p)), avalid_edge m e.
Proof.
  induction p; ii; ss; repeat des_goal; repeat des_hyp; clarify; des;
  split; ii; des; clarify; ltac:(
  let HH := fresh "HH" in
  match goal with
  | H : forall e, Ex ?n ?x ?n' = e \/ _ -> _ |- _ =>
    specialize (H (Ex n x n')) as HH; 
    exploit HH; eauto;
    ii; ss; repeat des_hyp; clarify
  | H : forall e, EM ?n ?M ?n' = e \/ _ -> _ |- _ =>
    specialize (H (EM n M n')) as HH; 
    exploit HH; eauto;
    ii; ss; repeat des_hyp; clarify
  | H : forall e, Ev ?n ?v ?n' = e \/ _ -> _ |- _ =>
    specialize (H (Ev n v n')) as HH; 
    exploit HH; eauto;
    ii; ss; repeat des_hyp; clarify
  | _ => idtac
  end).
  - ss; des_goal; clarify.
  - rewrite IHp in *. eauto.
  - split; try rewrite IHp; ii; eauto.
  - ss; des_goal; clarify.
  - rewrite IHp in *. eauto.
  - split; try rewrite IHp; ii; eauto.
  - ss. exists ev. 
    des_goal; des; repeat split; clarify.
  - des_hyp; des; clarify.
    rewrite IHp in *; eauto.
  - des. exists ev.
    des_goal; des; repeat split; clarify.
    rewrite IHp; ii; eauto.
Qed.

Definition reachable `{Eq T} root m e :=
  exists p,
    valid_path root m p /\
    In e (Edges root p).

Definition lvertex `{Eq T} (e : edge T) :=
  match e with
  | Ex n _ _
  | EM n _ _
  | Ev n _ _ => n
  end.

Definition rvertex `{Eq T} (e : edge T) :=
  match e with
  | Ex _ _ n
  | EM _ _ n
  | Ev _ _ n => n
  end.

Lemma reachable_paste `{Eq T} :
  forall n m e (REACH : reachable n m e)
    e' (EXT : rvertex e = lvertex e')
    (VAL : valid_edge m e'),
    reachable n m e'.
Proof.
  ii. unfold reachable in REACH. des.
  ginduction p; ii; ss;
  repeat des_hyp; clarify; des; clarify; ss;
  destruct e'; ss;
  repeat des_hyp; des; clarify;
  repeat des_hyp; des; clarify;
  try match goal with
  | _ : rvertex _ = _ |- reachable _ _ ?e =>
    exploit IHp; eauto;
    try instantiate (1 := e); ss;
    try match goal with
    | _ : Some (Closure ?x ?e ?C) = _ |- _ =>
      exists (Closure x e C)
    | _ => rw
    end; eauto;
    unfold reachable; ii; des
  end;
  try match goal with
  | _ : valid_path ?n _ ?p |- _ =>
    solve [
      exists (Px x n p); ss; rw; eauto|
      exists (PM M n p); ss; rw; eauto]
  | _ : Some (Closure ?x ?e _) = _,
    _ : valid_path (Ctx ?C) _ ?p |- _ =>
    solve [
      exists (Pv (v_fn x e) (Ctx C) p);
      ss; repeat split; eauto;
      exists (Closure x e C); ss]
  end.
  - exists (Px x (Ptr t) (Pv (v_fn x0 e) (Ctx C0) Pnil)).
    ss; rw. repeat split; eauto.
    exists (Closure x0 e C0). eauto.
  - exists (PM M (Ctx C) (Px x (Ptr t) Pnil)).
    ss. repeat rw. repeat split; eauto.
  - exists (PM M (Ctx C) (PM M0 (Ctx C1) Pnil)).
    ss. repeat rw. repeat split; eauto.
  - exists (Pv (v_fn x0 e) (Ctx C0) (Px x (Ptr t0) Pnil)).
    ss. repeat split; eauto.
    exists (Closure x0 e C0). rw. eauto.
  - exists (Pv (v_fn x e) (Ctx C0) (PM M (Ctx C1) Pnil)).
    ss. repeat split; eauto.
    exists (Closure x e C0). rw. eauto.
Qed.

Lemma reachable_left `{Eq T} :
  forall n m e (REACH : reachable n m e),
    n = lvertex e \/
    exists e', reachable n m e' /\ rvertex e' = lvertex e.
Proof.
  ii. unfold reachable in REACH. des.
  ginduction p; ii; ss; repeat des_hyp; clarify;
  des; clarify; ss; repeat des_hyp;
  clarify; des; clarify; eauto;
  exploit IHp; eauto; ii; des; clarify; right.
  - exists (Ex (Ctx C) x (Ptr t0)).
    split; ss.
    exists (Px x (Ptr t0) Pnil). ss. repeat rw. eauto.
  - exists e'.
    split; ss.
    unfold reachable in *. des.
    exists (Px x (Ptr t0) p0).
    ss. rw. eauto.
  - exists (EM (Ctx C0) M (Ctx d)).
    split; ss.
    exists (PM M (Ctx d) Pnil). ss. repeat rw. eauto.
  - exists e'.
    split; ss.
    unfold reachable in *. des.
    exists (PM M (Ctx d) p0).
    ss. rw. eauto.
  - exists (Ev (Ptr t) (v_fn x e0) (Ctx C0)).
    split; ss.
    exists (Pv (v_fn x e0) (Ctx C0) Pnil). ss.
    repeat split; eauto.
    exists (Closure x e0 C0). ss.
  - exists e'.
    split; ss.
    unfold reachable in *. des.
    exists (Pv (v_fn x e0) (Ctx C0) p0).
    ss. split; eauto.
    exists (Closure x e0 C0). ss.
Qed.

Lemma reachable_eq_def `{Eq T} :
  forall n m e,
    reachable n m e <->
    (valid_edge m e /\
      (n = lvertex e \/
      exists e', 
        reachable n m e' /\
        rvertex e' = lvertex e)).
Proof.
  ii. split; intros REACH; des; clarify.
  - split. unfold reachable in *. des.
    rewrite vpath_iff_vedge in REACH. eauto.
    apply reachable_left. eauto.
  - destruct e; ss; repeat des_hyp; clarify; des;
    repeat des_hyp; des; clarify;
    match goal with
    | |- context [Ex _ ?x (Ptr ?t)] =>
      exists (Px x (Ptr t) Pnil)
    | |- context [EM _ ?M (Ctx ?C)] =>
      exists (PM M (Ctx C) Pnil)
    | |- context [Ev _ ?v (Ctx ?C)] =>
      exists (Pv v (Ctx C) Pnil)
    end; ss; try rw; eauto.
    split; eauto.
    exists (Closure x e C). eauto.
  - eapply reachable_paste; eauto.
Qed.

Fixpoint remove_t `{Eq T} (m : memory T) t :=
  match m with
  | [] => []
  | (t', v) :: tl =>
    let tl := remove_t tl t in
    if eqb t t' then tl else (t', v) :: tl
  end.

Fixpoint reach_C `{Eq T} seenx seenM (Cout Cin : dy_ctx T) :=
  match Cin with
  | [||] => []
  | dy_binde x t Cin =>
    if Inb x seenx then reach_C seenx seenM Cout Cin
    else Ex (Ctx Cout) x (Ptr t) ::
    reach_C (x :: seenx) seenM Cout Cin
  | dy_bindm M Cout' Cin =>
    if Inb M seenM then reach_C seenx seenM Cout Cin
    else reach_C [] [] Cout' Cout' ++ 
    EM (Ctx Cout) M (Ctx Cout') ::
    reach_C seenx (M :: seenM) Cout Cin
  end.

Fixpoint InL `{Eq T} (n : node T) (l : list (edge T)) :=
  match l with
  | [] => false
  | e :: tl => eqb n (lvertex e) || InL n tl
  end.

Fixpoint InR `{Eq T} (n : node T) (l : list (edge T)) :=
  match l with
  | [] => false
  | e :: tl => eqb n (rvertex e) || InR n tl
  end.

Lemma InL_In `{Eq T} :
  forall l n, InL n l = true <-> exists e, In e l /\ n = lvertex e.
Proof.
  induction l; ii; ss; split; ii; 
  repeat des_goal; repeat des_hyp; ss; des; clarify;
  first [rewrite eq_node_eq in * | rewrite eq_node_neq in *];
  clarify.
  - exists a. eauto.
  - rewrite IHl in *. des. clarify.
    exists e. eauto.
  - rewrite IHl. exists e. eauto.
Qed.

Lemma InL_nIn `{Eq T} :
  forall l n, InL n l = false <-> forall e, ~ In e l \/ n <> lvertex e.
Proof.
  split; intros NIN.
  - assert (InL n l <> true) as HINT.
    { refl_bool. eauto. }
    red in HINT. rewrite InL_In in HINT.
    ii.
    destruct (Inb e l) eqn:CASEIn;
    destruct (eqb n (lvertex e)) eqn:CASEv;
    try rewrite Inb_eq in *;
    try rewrite eqb_eq in *;
    try rewrite Inb_neq in *;
    try rewrite eqb_neq in *;
    clarify; eauto.
    exfalso. apply HINT. exists e. eauto.
  - refl_bool. ii.
    rewrite InL_In in *. des.
    specialize (NIN e). des; eauto.
Qed.

Lemma InR_In `{Eq T} :
  forall l n, InR n l = true <-> exists e, In e l /\ n = rvertex e.
Proof.
  induction l; ii; ss; split; ii; 
  repeat des_goal; repeat des_hyp; ss; des; clarify;
  first [rewrite eq_node_eq in * | rewrite eq_node_neq in *];
  clarify.
  - exists a. eauto.
  - rewrite IHl in *. des. clarify.
    exists e. eauto.
  - rewrite IHl. exists e. eauto.
Qed.

Lemma InR_nIn `{Eq T} :
  forall l n, InR n l = false <-> forall e, ~ In e l \/ n <> rvertex e.
Proof.
  split; intros NIN.
  - assert (InR n l <> true) as HINT.
    { refl_bool. eauto. }
    red in HINT. rewrite InR_In in HINT.
    ii.
    destruct (Inb e l) eqn:CASEIn;
    destruct (eqb n (rvertex e)) eqn:CASEv;
    try rewrite Inb_eq in *;
    try rewrite eqb_eq in *;
    try rewrite Inb_neq in *;
    try rewrite eqb_neq in *;
    clarify; eauto.
    exfalso. apply HINT. exists e. eauto.
  - refl_bool. ii.
    rewrite InR_In in *. des.
    specialize (NIN e). des; eauto.
Qed.

Lemma InL_app_iff `{Eq T} :
  forall n l1 l2,
  InL n (l1 ++ l2) = true <-> InL n l1 = true \/ InL n l2 = true.
Proof.
  ii. split; ii; rewrite InL_In in *; des; clarify.
  - rewrite in_app_iff in *. des.
    left. exists e. eauto.
    right. rewrite InL_In. exists e. eauto.
  - exists e. rewrite in_app_iff. eauto.
  - rewrite InL_In in *. des.
    exists e. rewrite in_app_iff. eauto.
Qed.

Lemma InR_app_iff `{Eq T} :
  forall n l1 l2,
  InR n (l1 ++ l2) = true <-> InR n l1 = true \/ InR n l2 = true.
Proof.
  ii. split; ii; rewrite InR_In in *; des; clarify.
  - rewrite in_app_iff in *. des.
    left. exists e. eauto.
    right. rewrite InR_In. exists e. eauto.
  - exists e. rewrite in_app_iff. eauto.
  - rewrite InR_In in *. des.
    exists e. rewrite in_app_iff. eauto.
Qed.

Fixpoint reach_m_step `{Eq T} acc (m : memory T) :=
  match m with
  | [] => (acc, [])
  | (t, v) :: m =>
    if InR (Ptr t) acc then match v with
    | Closure x e C =>
      (reach_C [] [] C C ++ 
      Ev (Ptr t) (v_fn x e) (Ctx C) ::
      acc, remove_t m t)
    end else match reach_m_step acc m with
    | (acc, m) => (acc, (t, v) :: m)
    end
  end.

Fixpoint areach_m_step `{Eq T} acc (m : memory T) :=
  match m with
  | [] => (acc, [])
  | (t, v) :: m =>
    if InR (Ptr t) acc then match v with
    | Closure x e C =>
      match areach_m_step acc m with
      | (acc, m) =>
        (reach_C [] [] C C ++
        Ev (Ptr t) (v_fn x e) (Ctx C) ::
        acc, m)
      end
    end else match areach_m_step acc m with
    | (acc, m) => (acc, (t, v) :: m)
    end
  end.

Fixpoint reach_m_aux `{Eq T} acc (m : memory T) fuel :=
  match reach_m_step acc m with
  | (acc, m') =>
    if Nat.eqb (List.length m) (List.length m') then
      Some acc
    else match fuel with
    | 0 => None
    | S fuel => reach_m_aux acc m' fuel
    end
  end.

Lemma remove_t_dec `{Eq T} :
  forall (m : memory T) t,
  (List.length (remove_t m t)) <= (List.length m).
Proof.
  induction m; intros; simpl; eauto.
  repeat des_goal; repeat des_hyp; clarify;
  try rewrite eqb_eq in *; subst;
  match goal with
  | |- context [remove_t _ ?t] =>
    specialize (IHm t); nia
  end.
Qed.

Lemma remove_t_read `{Eq T} :
  forall (m : memory T) t,
  None = read (remove_t m t) t.
Proof.
  induction m; ii; ss; repeat des_goal; repeat des_hyp; clarify.
  rewrite eqb_eq in *; clarify. rewrite t_refl in *. clarify.
Qed.

Lemma remove_t_read_some `{Eq T} :
  forall (m : memory T) t t' (NEQ : t <> t'),
  read (remove_t m t) t' = read m t'.
Proof.
  induction m; ii; ss; repeat des_goal; repeat des_hyp;
  try rewrite eqb_eq in *; clarify; eauto.
Qed.

Lemma reach_m_step_dec `{Eq T} :
  forall m acc,
  match reach_m_step acc m with
  | (_, m') => length m' <= length m
  end.
Proof.
  induction m; ii; ss;
  repeat des_goal; repeat des_hyp; clarify; ss.
  - pose proof (remove_t_dec m t). nia.
  - specialize (IHm acc). repeat des_hyp; clarify. nia.
Qed.

Lemma areach_m_step_dec `{Eq T} :
  forall (m : memory T) acc,
  match areach_m_step acc m with
  | (_, m') => length m' <= length m
  end.
Proof.
  induction m; intros; simpl; eauto;
  repeat des_goal; repeat des_hyp; clarify; simpl.
  - specialize (IHm acc). 
    repeat des_hyp; clarify. auto.
  - specialize (IHm acc).
    repeat des_hyp; clarify. nia.
Qed.

Lemma reach_m_step_same `{Eq T} :
  forall m acc,
  match reach_m_step acc m with
  | (acc', m') =>
    if length m =? length m' then
      acc = acc' /\ m = m'
    else True
  end.
Proof.
  induction m; ii; ss; repeat des_goal; repeat des_hyp; des; clarify;
  rewrite Nat.eqb_eq in *; clarify.
  - pose proof (reach_m_step_dec m acc).
    pose proof (remove_t_dec m t).
    repeat des_hyp; clarify. nia.
  - ss.
    assert (length m = length l2) as RR. nia.
    rewrite <- Nat.eqb_eq in RR.
    specialize (IHm acc).
    repeat des_hyp; clarify; des; clarify.
Qed.

Fixpoint areach_m_aux `{Eq T} acc (m : memory T) fuel :=
  match areach_m_step acc m with
  | (acc, m') =>
    if Nat.eqb (List.length m) (List.length m') then
      Some acc
    else match fuel with
    | 0 => None
    | S fuel => areach_m_aux acc m' fuel
    end
  end.

Definition reach_m `{Eq T} init (m : memory T) :=
  reach_m_aux init m (List.length m).

Definition areach_m `{Eq T} init (m : memory T) :=
  areach_m_aux init m (List.length m).

Lemma reach_m_aux_some `{Eq T} :
  forall fuel m init (GE : (List.length m) <= fuel),
    exists reached, reach_m_aux init m fuel = Some reached.
Proof.
  induction fuel; intros; destruct m; simpl in *; eauto;
  try (inversion GE; fail).
  assert (List.length m <= fuel). { nia. }
  repeat des_goal; repeat des_hyp; clarify; eauto; apply IHfuel;
  match goal with
  | _ : context [remove_t ?m ?t] |- _ =>
    pose proof (remove_t_dec m t);
    repeat des_hyp; ss; clarify; try nia
  | _ : context [reach_m_step ?init ?m] |- _ =>
    pose proof (reach_m_step_dec m init);
    repeat des_hyp; ss; clarify
  end.
  - rewrite Nat.eqb_neq in *. nia.
Qed.

Lemma areach_m_aux_some `{Eq T} :
  forall fuel m init (GE : (List.length m) <= fuel),
    exists reached, areach_m_aux init m fuel = Some reached.
Proof.
  induction fuel; intros; destruct m; simpl in *; eauto;
  try (inversion GE; fail).
  assert (List.length m <= fuel). { nia. }
  repeat des_goal; repeat des_hyp; clarify; eauto; apply IHfuel;
  match goal with
  | _ => rw; nia
  | _ =>
    pose proof (areach_m_step_dec m init);
    repeat des_hyp; ss; clarify;
    rewrite Nat.eqb_neq in *; nia
  end.
Qed.

Lemma relax_fuel `{Eq T} :
  forall fuel fuel' (LE : fuel' <= fuel) init m reached
    (EV : reach_m_aux init m fuel' = Some reached),
  reach_m_aux init m fuel = Some reached.
Proof.
  induction fuel;
  ii; inv LE; ss; repeat des_goal; repeat des_hyp; clarify;
  apply IHfuel in EV; eauto.
  - rewrite <- EV. symmetry.
    eapply IHfuel; eauto.
    destruct fuel'; ss; repeat rw; eauto.
  - destruct fuel; ss; repeat des_hyp; clarify.
    apply IHfuel with (fuel' := fuel); eauto.
Qed.

Lemma arelax_fuel `{Eq T} :
  forall fuel fuel' (LE : fuel' <= fuel) init m reached
    (EV : areach_m_aux init m fuel' = Some reached),
  areach_m_aux init m fuel = Some reached.
Proof.
  induction fuel;
  ii; inv LE; ss; repeat des_goal; repeat des_hyp; clarify;
  apply IHfuel in EV; eauto.
  - rewrite <- EV. symmetry.
    eapply IHfuel; eauto.
    destruct fuel'; ss; repeat rw; eauto.
  - destruct fuel; ss; repeat des_hyp; clarify.
    apply IHfuel with (fuel' := fuel); eauto.
Qed.

Lemma reach_m_some `{Eq T} :
  forall m init, exists reached, reach_m init m = Some reached.
Proof.
  intros. unfold reach_m. apply reach_m_aux_some. eauto.
Qed.

Lemma areach_m_some `{Eq T} :
  forall m init, exists reached, areach_m init m = Some reached.
Proof.
  intros. unfold areach_m. apply areach_m_aux_some. eauto.
Qed.

Definition reach `{Eq T} (n : node T) (m : memory T) :=
  match n with
  | Ctx C => reach_m (reach_C [] [] C C) m
  | Ptr t =>
    let init := match read m t with
    | Some (Closure x e C) => 
      (Ev (Ptr t) (v_fn x e) (Ctx C)) ::
      reach_C [] [] C C
    | None => []
    end in
    reach_m init (remove_t m t)
  end.

Fixpoint flatten {T} (ll : list (list T)) :=
  match ll with
  | [] => []
  | l :: tll => l ++ flatten tll
  end.

Definition areach `{Eq T} (n : node T) (m : memory T) :=
  match n with
  | Ctx C => areach_m (reach_C [] [] C C) m
  | Ptr t => 
    let init := flatten (map (fun v => match v with
    | Closure x e C => 
      (Ev (Ptr t) (v_fn x e) (Ctx C)) ::
      reach_C [] [] C C
    end) (aread m t)) in
    areach_m init (remove_t m t)
  end.

Fixpoint memify `{Eq T} (edges : list (edge T)) : memory T :=
  match edges with
  | [] => []
  | Ev (Ptr t) (v_fn x e) (Ctx C) :: tl =>
    (t, Closure x e C) :: memify tl
  | _ :: tl => memify tl
  end.

Lemma app_memify `{Eq T} :
  forall l1 l2,
    memify (l1 ++ l2) = memify l1 ++ memify l2.
Proof.
  induction l1; ii; ss;
  repeat des_goal; repeat des_hyp; clarify.
  rw. reflexivity.
Qed.

Lemma valid_edge_C `{Eq T} :
  forall e m C (LEFT : Ctx C = lvertex e),
  valid_edge m e <-> valid_edge [] e.
Proof.
  ii. destruct e; ss; repeat des_goal; repeat des_hyp; clarify.
Qed.

Definition reach_C_pre `{Eq T} seenx seenM (Cout Cin : dy_ctx T) :=
  (forall x (NIN : ~ In x seenx),
    match addr_x Cout x, addr_x Cin x with
    | Some tx, Some tx' => tx = tx'
    | None, None => True
    | _, _ => False
    end) /\
  (forall M (NIN : ~ In M seenM),
    match ctx_M Cout M, ctx_M Cin M with
    | Some CM, Some CM' => CM = CM'
    | None, None => True
    | _, _ => False
    end).

Definition reach_C_post `{Eq T} seenx seenM Cout res :=
  (forall x (NIN : ~ In x seenx),
  match addr_x Cout x with
  | Some t => In (Ex (Ctx Cout) x (Ptr t)) res
  | None => True
  end) /\
  (forall M (NIN : ~ In M seenM),
  match ctx_M Cout M with
  | Some CM => In (EM (Ctx Cout) M (Ctx CM)) res
  | None => True
  end) /\
  (forall C e e'
    (IN : In e res)
    (RIGHT : Ctx C = rvertex e)
    (LEFT : Ctx C = lvertex e')
    (VAL : valid_edge [] e'),
    In e' res) /\
  (forall e (IN : In e res),
    valid_edge [] e) /\
  (forall e C
    (IN : In e res) 
    (LEFT : Ctx C = lvertex e),
    C = Cout \/
    exists e', Ctx C = rvertex e' /\ In e' res).

Lemma reach_C_pre_post `{Eq T} :
  forall Cin Cout seenx seenM
    (INV : reach_C_pre seenx seenM Cout Cin),
  reach_C_post seenx seenM Cout (reach_C seenx seenM Cout Cin).
Proof.
  induction Cin; ii; ss;
  unfold reach_C_pre in *;
  unfold reach_C_post in *;
  des;
  repeat match goal with
  | |- _ /\ _ => split
  end; ii; ss;
  repeat des_goal; repeat des_hyp; clarify.
  - exploit INV; eauto. rw. eauto.
  - exploit INV0; eauto. rw. eauto.
  - rewrite Inb_eq in *.
    exploit INV; eauto. rw.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    exploit (IHCin Cout seenx seenM).
    split; eauto.
    ii. exploit (INV x1); eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *. clarify.
    rw. eauto. rw. eauto.
    ii. des.
    specialize (x2 x0 NIN).
    repeat des_hyp; clarify.
  - rewrite Inb_neq in *.
    specialize (INV x0 NIN) as HINT.
    rewrite GDES in *.
    repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify; eauto.
    right.
    exploit (IHCin Cout (x :: seenx) seenM).
    split; eauto.
    ii. exploit (INV x1).
    red; ii; ss; eauto.
    ii. repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *. ss. clarify. contradict.
    rw. eauto. rw. eauto.
    ii. des. exploit (x2 x0).
    red; ii; ss; des; clarify.
    rewrite eqb_ID_neq in *. eauto.
    ii. repeat des_hyp; clarify.
  - rewrite Inb_eq in *.
    exploit (IHCin Cout seenx seenM).
    split; eauto.
    ii. exploit INV; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *. clarify.
    rw. eauto. rw. eauto.
    ii; des.
    specialize (x0 M NIN).
    rewrite GDES in *. eauto.
  - right. rewrite Inb_neq in *.
    exploit (IHCin Cout (x :: seenx) seenM).
    split; eauto.
    ii. exploit (INV x0).
    red; ii; ss; eauto.
    ii. repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *. clarify. ss. contradict.
    rw. eauto. rw. eauto.
    ii. des. exploit (x0 M); eauto.
    rw. eauto.
  - rewrite Inb_eq in *.
    specialize (IHCin Cout seenx seenM).
    exploit IHCin; eauto.
    split; eauto.
    ii. exploit INV; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
    ii; des. eauto.
  - ss. des; clarify.
    rewrite Inb_neq in *.
    exploit (IHCin Cout (x :: seenx) seenM).
    split; eauto.
    ii. exploit (INV x0); eauto.
    red; ii. apply NIN; ss; eauto.
    ii. repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    ss; contradict.
    rw. eauto. rw. eauto.
    ii. des. eauto.
  - rewrite Inb_eq in *.
    exploit (IHCin Cout seenx seenM).
    split; eauto.
    ii. exploit INV; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
    ii. des. eauto.
  - rewrite Inb_neq in *.
    des; clarify; ss.
    + exploit INV; eauto.
      ii. repeat des_hyp; try rewrite eqb_ID_neq in *; clarify.
    + exploit (IHCin Cout (x :: seenx) seenM).
      split; eauto.
      ii. exploit (INV x0); eauto.
      ii; ss; eauto.
      ii. repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *. clarify. ss; contradict.
      rw. eauto. rw. eauto.
      ii. des. eauto.
  - rewrite Inb_eq in *.
    exploit (IHCin Cout seenx seenM); eauto.
    split; eauto.
    ii. exploit (INV x0); eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
    ii. des. eauto.
  - rewrite Inb_neq in *.
    ss; des; clarify; ss; clarify; eauto.
    exploit (IHCin Cout (x :: seenx) seenM); eauto.
    split; eauto.
    ii. exploit (INV x0).
    red; ii; ss; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify. ss; contradict.
    rw. eauto. rw. eauto.
    ii. des. exploit x4; eauto.
    ii. des; clarify; eauto.
  - rewrite Inb_eq in *.
    exploit (IHCin2 Cout seenx seenM).
    split; eauto.
    ii. exploit INV0; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
    ii. des. exploit x1; eauto. rw. eauto.
  - rewrite Inb_neq in *.
    rewrite in_app_iff. right. right.
    exploit (IHCin2 Cout seenx (M :: seenM)).
    split; eauto.
    ii. exploit (INV0 M0); eauto.
    red; ii. ss; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; ss. contradict.
    rw. eauto. rw. eauto.
    ii. des.
    exploit x1; eauto. rw. eauto.
  - rewrite Inb_eq in *.
    exploit (IHCin2 Cout seenx seenM).
    split; eauto.
    ii. exploit (INV0 M1); eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; ss; clarify.
    rw. eauto. rw. eauto.
    ii. des. exploit (x1 M0); eauto.
    rw. eauto.
  - rewrite Inb_neq in *.
    specialize (INV0 M0 NIN) as HINT.
    rewrite GDES in HINT.
    repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rewrite in_app_iff. right. left. eauto.
    rewrite eqb_ID_neq in *.
    exploit (IHCin2 Cout seenx (M :: seenM)).
    split; eauto.
    ii. exploit (INV0 M1); eauto.
    red; ii; ss; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; ss; clarify. contradict.
    rw. eauto. rw. eauto.
    ii. des. exploit (x1 M0); eauto.
    red; ii; ss; des; clarify.
    ii; repeat des_hyp; clarify.
    rewrite in_app_iff. right. right. assumption.
  - rewrite Inb_eq in *.
    exploit (IHCin2 Cout seenx seenM).
    split; eauto.
    ii. exploit INV0; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
    ii. des. eauto.
  - rewrite Inb_neq in *.
    rewrite in_app_iff in *. ss. des; clarify; ss; clarify.
    + left. specialize (IHCin1 Cin1 [] []).
      exploit IHCin1.
      split; ii; ss; repeat des_goal; repeat des_hyp; clarify.
      ii; des. eauto.
    + left. specialize (IHCin1 Cin1 [] []).
      destruct e'; ss; repeat des_hyp; clarify;
      exploit IHCin1;
      match goal with
      | |- _ /\ _ =>
        split; ii; ss; repeat des_goal; repeat des_hyp; clarify
      | _ => ii; des
      end.
      exploit x1; eauto. rw. eauto.
      exploit x1; eauto. rw. eauto.
    + right. right.
      specialize (IHCin2 Cout seenx (M :: seenM)).
      exploit IHCin2.
      split; eauto.
      ii. exploit (INV0 M0); eauto.
      red; ii; ss; eauto.
      ii; repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *; ss; clarify. contradict.
      rw. eauto. rw. eauto.
      ii. des. eauto.
  - rewrite Inb_eq in *.
    exploit (IHCin2 Cout seenx seenM).
    split; eauto.
    ii. exploit INV0; eauto.
    ii; repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
    ii. des. eauto.
  - rewrite Inb_neq in *.
    rewrite in_app_iff in *. ss.
    des; clarify.
    + exploit (IHCin1 Cin1 [] []).
      split; ii; ss;
      repeat des_goal; repeat des_hyp; clarify.
      ii; des. eauto.
    + exploit INV0; eauto.
      ii. repeat des_hyp; clarify.
      ss. rw. eauto.
      rewrite eqb_ID_neq in *. contradict.
      rewrite eqb_ID_neq in *. contradict.
    + exploit (IHCin2 Cout seenx (M :: seenM)).
      split; eauto.
      ii. exploit (INV0 M0); eauto.
      red; ii; ss; eauto.
      ii; repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *; ss; clarify. contradict.
      rw. eauto. rw. eauto.
      ii. des. eauto.
  - rewrite Inb_eq in *.
    exploit (IHCin2 Cout seenx seenM).
    split; eauto.
    ii. exploit (INV0 M0); eauto.
    ii. repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
    ii. des. eauto.
  - rewrite Inb_neq in *.
    rewrite in_app_iff in *. ss.
    des; clarify.
    + exploit (IHCin1 Cin1 [] []).
      split; ii; repeat des_goal; repeat des_hyp; clarify.
      ii. des.
      exploit (INV0 M); eauto.
      ii. repeat des_hyp; clarify;
      try rewrite eqb_ID_neq in *; try contradict.
      exploit x4; eauto.
      ii. des; clarify.
      * right. exists (EM (Ctx Cout) M (Ctx d0)).
        split; ss. rewrite in_app_iff; ss. eauto.
      * right. exists e'.
        rewrite in_app_iff; ss; eauto.
    + ss; clarify; eauto.
    + exploit (IHCin2 Cout seenx (M :: seenM)).
      split; eauto.
      ii. exploit (INV0 M0); eauto.
      red; ii; ss; eauto.
      ii; repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *; ss; clarify. contradict.
      rw. eauto. rw. eauto.
      ii. des.
      exploit x4; eauto. ii; des; clarify; eauto.
      right. exists e'. rewrite in_app_iff; ss; eauto.
Qed.

Lemma reach_C_no_t `{Eq T} :
  forall Cin Cout seenx seenM t,
  InL (Ptr t) (reach_C seenx seenM Cout Cin) = false.
Proof.
  induction Cin; ii; ss; repeat des_goal; repeat des_hyp; clarify.
  match goal with
  | |- InL ?a ?b = _ =>
    destruct (InL a b) eqn:CASE; try reflexivity
  end.
  rewrite InL_app_iff in CASE; ss; des.
  rewrite IHCin1 in *. clarify.
  rewrite IHCin2 in *. clarify.
Qed.

Definition reach_C_spec `{Eq T} C res :=
  (forall e (INe : In e res),
    valid_edge [] e) /\
  (forall e (LEFT : Ctx C = lvertex e)
    (VAL : valid_edge [] e),
    In e res) /\
  (forall e e' C (INe : In e res)
    (INC : Ctx C = lvertex e \/ Ctx C = rvertex e)
    (LEFT : Ctx C = lvertex e')
    (VAL : valid_edge [] e'),
    In e' res) /\
  (forall e t (LEFT : Ptr t = lvertex e),
    ~ In e res).

Lemma reach_C_spec_true `{Eq T} :
  forall C, reach_C_spec C (reach_C [] [] C C).
Proof.
  intros.
  pose proof (reach_C_pre_post C C [] []) as HINT.
  exploit HINT.
  unfold reach_C_pre. split; ii; repeat des_goal; clarify.
  clear HINT. intros HINT.
  unfold reach_C_post in HINT. des.
  repeat split; eauto.
  - ii. destruct e; ss; repeat des_hyp; clarify.
    exploit HINT; eauto. rw. eauto.
    exploit HINT0; eauto. rw. eauto.
  - ii; des.
    exploit HINT3; eauto. ii. des; clarify.
    destruct e'; ss; repeat des_hyp; clarify.
    { exploit HINT; eauto. rw. eauto. }
    { exploit HINT0; eauto. rw. eauto. }
    exploit HINT1; eauto.
    exploit HINT1; eauto.
  - red; ii.
    pose proof (reach_C_no_t C C [] [] t).
    match goal with
    | _ : InL ?a ?b = false |- _ =>
      let HINT := fresh "HINT" in
      assert (InL a b <> true) as HINT;
      first [apply HINT | refl_bool; ii; clarify]
    end.
    rewrite InL_In. exists e. eauto.
Qed.

Lemma reach_C_path_left `{Eq T} :
  forall Cin Cout seenx seenM e
    (PRE : reach_C_pre seenx seenM Cout Cin)
    (IN : In e (reach_C seenx seenM Cout Cin)),
    reachable (Ctx Cout) [] e.
Proof.
  induction Cin; ii; ss;
  repeat des_hyp; clarify.
  - rewrite Inb_eq in *.
    unfold reach_C_pre in PRE.
    des; ss.
    eapply IHCin; eauto.
    split; eauto.
    ii. exploit (PRE x0); eauto.
    ii. repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
  - rewrite Inb_neq in *.
    unfold reach_C_pre in PRE.
    des; clarify.
    specialize (PRE x HDES).
    repeat des_hyp; clarify.
    exists (Px x (Ptr t0) Pnil).
    ss. rw. eauto.
    rewrite eqb_ID_neq in *. contradict.
    rewrite eqb_ID_neq in *. contradict.
    eapply IHCin; eauto.
    split; eauto.
    ii. exploit (PRE x0); eauto.
    ss. red; ii; eauto.
    ii. repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify; ss; contradict.
    rw. eauto. rw. eauto.
  - rewrite Inb_eq in *.
    unfold reach_C_pre in PRE.
    des; ss.
    eapply IHCin2; eauto.
    split; eauto.
    ii. exploit (PRE0 M0); eauto.
    ii. repeat des_hyp; clarify.
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto. rw. eauto.
  - rewrite in_app_iff in *.
    rewrite Inb_neq in *.
    ss. des; clarify.
    + exploit (IHCin1 Cin1 [] [] e); eauto.
      red; ii. split; ii; repeat des_goal; clarify.
      ii. unfold reachable in *; des.
      exists (PM M (Ctx Cin1) p).
      split; ss; eauto.
      unfold reach_C_pre in PRE. des.
      exploit (PRE0 M); eauto.
      ii. repeat des_hyp; clarify;
      rewrite eqb_ID_neq in *; contradict.
    + exists (PM M (Ctx Cin1) Pnil).
      split; ss; eauto.
      unfold reach_C_pre in PRE. des.
      exploit (PRE0 M); eauto.
      ii. repeat des_hyp; clarify;
      rewrite eqb_ID_neq in *; clarify.
    + eapply IHCin2; eauto.
      unfold reach_C_pre in *; ss; des.
      split; eauto.
      ii. exploit (PRE0 M0).
      red; ii; eauto.
      ii. repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *; clarify. contradict.
      rw. eauto. rw. eauto.
Qed.

Lemma reach_C_eq_def `{Eq T} :
  forall C e,
  reachable (Ctx C) [] e <->
  In e (reach_C [] [] C C).
Proof.
  ii. split; intros REACH.
  pose proof (reach_C_spec_true C) as SPEC.
  unfold reach_C_spec in SPEC. des.
  unfold reachable in *. des.
  remember (reach_C [] [] C C) as l.
  clear Heql.
  ginduction p; ii; ss;
  repeat des_hyp; clarify; des; clarify.
  - eapply SPEC0; ss; try rw; eauto.
  - destruct p; ss; des; clarify;
    repeat des_hyp; des; clarify.
  - eapply SPEC0; ss; try rw; eauto.
  - eapply IHp; eauto. ii.
    exploit (SPEC1 (EM (Ctx C) M (Ctx d))); ss; eauto.
    eapply SPEC0; ss; try rw; eauto.
  - eapply reach_C_path_left; eauto.
    split; ii; repeat des_goal; eauto.
Qed.

Lemma no_t_memify_empty `{Eq T} :
  forall l (NO : forall t, InL (Ptr t) l = false),
    memify l = [].
Proof.
  induction l; ii; ss; repeat des_goal; repeat des_hyp;
  ss; clarify; eauto;
  match goal with
  | NO : forall t, eqb t ?t' || _ = false |- _ =>
    solve [specialize (NO t'); rewrite t_refl in NO; ss]
  end.
Qed.

Lemma reach_C_memify_empty `{Eq T} :
  forall seenx seenM Cout Cin,
    memify (reach_C seenx seenM Cout Cin) = [].
Proof.
  intros. apply no_t_memify_empty.
  apply reach_C_no_t.
Qed.

Definition step_pre `{Eq T}
  (n : node T) (m : memory T) (E : list (edge T)) :=
  (forall e,
    In e E <-> 
    (valid_edge (memify E) e /\
      (n = lvertex e \/
      exists e',
        In e' E /\
        rvertex e' = lvertex e))) /\
  (forall t (IN : InL (Ptr t) E = true),
    None = read m t).

Lemma reach_C_step_pre `{Eq T} :
  forall C m, step_pre (Ctx C) m (reach_C [] [] C C).
Proof.
  intros. unfold step_pre. split.
  - intros.
    rewrite reach_C_memify_empty.
    rewrite <- reach_C_eq_def.
    split; ii.
    rewrite reachable_eq_def in *; des; eauto.
    rewrite reach_C_eq_def in *. eauto.
    rewrite reachable_eq_def in *; des; eauto.
    rewrite <- reach_C_eq_def in *. eauto.
  - ii. rewrite reach_C_no_t in *. clarify.
Qed.

Lemma read_memify_In `{Eq T} :
  forall E (PRE : forall e, In e E -> valid_edge (memify E) e)
    t x e C,
    Some (Closure x e C) = read (memify E) t <->
    In (Ev (Ptr t) (v_fn x e) (Ctx C)) E.
Proof.
  ii. split; intros IN.
  - clear PRE.
    induction E; ii; ss;
    repeat des_goal; repeat des_hyp; clarify; 
    ss; clarify; eauto.
    rewrite eqb_eq in *; clarify. eauto.
  - assert (forall x' e' C', 
      In (Ev (Ptr t) (v_fn x' e') (Ctx C')) E ->
      x' = x /\ e' = e /\ C' = C).
    intros x' e' C' IN'.
    apply PRE in IN, IN'. ss.
    des. repeat des_hyp; des; clarify.
    rewrite <- IN in *. clarify.
    clear PRE.
    ginduction E; ii; ss;
    repeat des_goal; repeat des_hyp; clarify;
    des; clarify; try solve [apply IHE; eauto].
    rewrite eqb_eq in *. clarify.
    exploit (H0 x0 e0 C0); eauto. ii; des; clarify.
    rewrite t_refl in *. clarify.
Qed.

Lemma step_pre_post_true `{Eq T} :
  forall n m acc (INV : step_pre n m acc),
  let (acc', m') := reach_m_step acc m in
  step_pre n m' acc' /\
  same (memify acc ++ m) (memify acc' ++ m') /\
  (exists acc'',
    acc' = acc'' ++ acc /\
    (forall t
      (RIGHT : InR (Ptr t) acc = true)
      (READ : None <> read m t),
      exists t',
        InL (Ptr t') acc'' = true /\
        None <> read m t') /\
    (forall t
      (RIGHT : InR (Ptr t) acc = false),
      InL (Ptr t) acc'' = false)).
Proof.
  induction m; ii;
  repeat des_goal; repeat des_hyp; ss; clarify.
  split; eauto.
  split; ii; eauto.
  exists []. split. reflexivity.
  split. ii. contradict. ii; ss.
  unfold step_pre in INV. des.
  assert (step_pre n m acc) as PRE.
  {
    split; eauto. ii.
    exploit INV0; eauto; ii; ss; repeat des_hyp; clarify.
  }
  repeat des_hyp; ss; clarify. (* 2 goals *)
  - assert (None = read (memify acc) t) as NREAD.
    {
      clear IHm INV HDES PRE.
      assert (InL (Ptr t) acc = false).
      refl_bool. intros contra.
      apply INV0 in contra. rewrite t_refl in *. clarify.
      clear INV0 n m x e0 C.
      ginduction acc; ii; ss;
      repeat des_goal; repeat des_hyp; des; clarify; eauto.
      ss. clarify.
      rewrite eqb_eq in *. clarify.
      rewrite eqb_neq in *. contradict.
    }
    split. split; ii. (* 3 goals *)
    + rewrite in_app_iff. rewrite app_memify.
      rewrite reach_C_memify_empty. simpl.
      split; intros IN; des. (* 5 goals *)
      * rewrite <- reach_C_eq_def in IN.
        rewrite reachable_eq_def in IN. des; clarify.
        split. destruct e; repeat des_hyp; ss; clarify.
        right. exists (Ev (Ptr t) (v_fn x e0) (Ctx C)).
        rewrite in_app_iff. ss. eauto.
        split.
        destruct e; ss; repeat des_hyp; des; clarify.
        right. exists e'. rewrite in_app_iff. split; eauto.
        left. rewrite <- reach_C_eq_def. eauto.
      * clarify. ss. rewrite t_refl.
        split. exists (Closure x e0 C). eauto.
        right. rewrite InR_In in HDES. des.
        exists e. rewrite in_app_iff. ss. eauto.
      * rewrite INV in IN. destruct IN as [VAL LEFT].
        split.
        destruct e; ss; repeat des_hyp; clarify.
        des; repeat des_hyp; des; clarify;
        exists (Closure x0 e C0); des_goal; eauto;
        rewrite eqb_eq in *; clarify; rewrite <- VAL in *; clarify.
        des; eauto. right. exists e'. rewrite in_app_iff; ss; eauto.
      * destruct n.
        destruct (eqb t0 t) eqn:CASE;
        try rewrite eqb_eq in *; clarify;
        destruct e; ss; repeat des_hyp; clarify;
        des; des_hyp; des; clarify; eauto.
        rewrite <- NREAD in *. clarify.
        rewrite eqb_eq in *; clarify. rewrite t_refl in *. clarify.
        right. right. rewrite INV.
        split. ss. exists (Closure x0 e C0). eauto.
        ss. eauto.
        right. right. rewrite INV.
        rewrite valid_edge_C in *; eauto.
      * rewrite in_app_iff in *. ss; des.
        (* case 1 *)
        destruct e; ss; repeat des_hyp; clarify;
        try (left; rewrite <- reach_C_eq_def in *;
            rewrite reachable_eq_def; split;
            solve [ss; rw; reflexivity
            | right; exists e'; ss]).
        rewrite eqb_eq in *. clarify.
        des. clarify. des. clarify. eauto.
        des. right. right. rewrite INV.
        des_hyp. des. clarify.
        assert (In (Ev (Ptr t0) (v_fn x0 e) (Ctx C0)) acc) as HINT.
        rewrite <- read_memify_In; eauto.
        ii. rewrite INV in *. des; eauto.
        rewrite INV in HINT.
        des; eauto.
        (* case 2 *)
        clarify; ss. left.
        rewrite <- reach_C_eq_def.
        rewrite valid_edge_C in IN; eauto.
        rewrite reachable_eq_def. eauto.
        (* case 3 *)
        destruct (lvertex e) eqn:CASE.
        destruct e; ss; repeat des_hyp; clarify.
        rewrite eqb_eq in *; clarify. des. des_hyp. des. clarify. eauto.
        right. right. rewrite INV. ss. eauto.
        rewrite valid_edge_C in IN; eauto.
        rewrite <- valid_edge_C with (m := memify acc) in IN; eauto.
        right. right. rewrite INV. split; eauto.
        right. exists e'. split; eauto. repeat rw. eauto.
    + rewrite InL_app_iff in *.
      des. rewrite reach_C_no_t in *. clarify.
      ss. des_hyp. rewrite eqb_eq in *; clarify.
      apply remove_t_read.
      exploit INV0; eauto. des_goal. clarify.
      rewrite eqb_neq in *.
      ii. rewrite remove_t_read_some; eauto.
    + split.
      * rewrite app_memify. rewrite reach_C_memify_empty. simpl.
        repeat match goal with
        | |- context [(?t, ?v) :: ?l] =>
          lazymatch l with
          | [] => fail
          | _ => replace ((t, v) :: l) with ([(t, v)] ++ l) by reflexivity
          end
        end.
        repeat rewrite app_assoc.
        eapply same_trans.
        instantiate (1 := (memify acc ++ [(t, Closure x e0 C)]) ++ remove_t m t).
        repeat rewrite <- app_assoc. apply app_same. ii; ss.
        ii; ss. des_goal; clarify. rewrite eqb_neq in *.
        rewrite remove_t_read_some; eauto.
        apply app_same. apply app_disj_same.
        ii. ss. des_goal; clarify. rewrite eqb_eq in *. clarify.
        ii. ss.
      * exists (reach_C [] [] C C ++ [Ev (Ptr t) (v_fn x e0) (Ctx C)]).
        split. rewrite <- app_assoc. ss.
        split. ii. exists t. rewrite t_refl.
        split; ii; clarify.
        rewrite InL_In. exists (Ev (Ptr t) (v_fn x e0) (Ctx C)).
        rewrite in_app_iff. split; ss; eauto.
        ii. refl_bool. ii.
        rewrite InL_app_iff in *. des.
        rewrite reach_C_no_t in *. clarify.
        ss. des_hyp. rewrite eqb_eq in *. clarify.
  - exploit IHm; eauto. intros POST.
    repeat des_hyp; des; clarify.
    unfold step_pre in POST. des.
    assert (InL (Ptr t) acc = false) as NIN.
    refl_bool. ii. exploit INV0; eauto. rewrite t_refl. clarify.
    assert (InL (Ptr t) acc'' = false) as NIN'. eauto.
    split; split; try assumption. (* 3 goals *)
    + ii. exploit POST1; eauto. ii.
      ss. des_goal; clarify. rewrite eqb_eq in *; clarify.
      rewrite InL_app_iff in IN. des; clarify.
    + repeat match goal with
      | |- context [(?t, ?v) :: ?l] =>
        lazymatch l with
        | [] => fail
        | _ => replace ((t, v) :: l) with ([(t, v)] ++ l) by reflexivity
        end
      end.
      repeat rewrite app_assoc.
      eapply same_trans.
      instantiate (1 := ([(t, e)] ++ memify acc) ++ m).
      apply app_same.
      apply app_disj_same.
      ii; ss. des_goal; eauto.
      rewrite eqb_eq in *. clarify.
      destruct (read (memify acc) t0) eqn:READ'; clarify.
      symmetry in READ'.
      destruct e0. rewrite read_memify_In in *.
      assert (InL (Ptr t0) acc = true).
      rewrite InL_In. exists (Ev (Ptr t0) (v_fn x e0) (Ctx C)). ss.
      clarify.
      ii. rewrite INV in *. des; eauto.
      ii; ss.
      eapply same_trans.
      instantiate (1 := ([(t, e)] ++ memify (acc'' ++ acc)) ++ l2).
      repeat rewrite <- app_assoc. ss.
      solve [ii; ss; des_goal; eauto].
      apply  app_same.
      apply app_disj_same.
      ii; ss. des_hyp; clarify.
      rewrite eqb_eq in *. clarify.
      match goal with |- None = ?x => destruct x eqn:CASE end; try reflexivity.
      symmetry in CASE.
      destruct e0. rewrite read_memify_In in CASE.
      rewrite in_app_iff in *. des.
      assert (InL (Ptr t0) acc'' = true).
      rewrite InL_In. exists (Ev (Ptr t0) (v_fn x e0) (Ctx C)). ss.
      clarify.
      assert (InL (Ptr t0) acc = true).
      rewrite InL_In. exists (Ev (Ptr t0) (v_fn x e0) (Ctx C)). ss.
      clarify.
      ii. rewrite POST in *. des; eauto.
      ii; ss.
    + exists acc''. split; eauto.
      split; ii; eauto.
      des_hyp; clarify.
      rewrite eqb_eq in *; clarify.
      exploit POST2; eauto. ii. des.
      exists t'. split; eauto.
      des_goal; clarify.
Qed.

Lemma step_spec_left `{Eq T} :
  forall E n
    (PRE : forall e, (valid_edge (memify E) e /\
      (n = lvertex e \/
      exists e',
        In e' E /\
        rvertex e' = lvertex e)) -> In e E)
    e (REACH : reachable n (memify E) e),
  In e E.
Proof.
  ii.
  unfold reachable in REACH. des.
  ginduction p; ii; ss; repeat des_hyp; clarify;
  des; clarify; try des_hyp; des; clarify.
  - apply PRE. ss. rw. eauto.
  - eapply IHp with (n := (Ptr t0)); eauto.
    ii. apply PRE. split; des; eauto.
    right. exists (Ex (Ctx C) x (Ptr t0)).
    split; ss; eauto. apply PRE. ss. rw. eauto.
  - apply PRE. ss. rw. eauto.
  - eapply IHp with (n := (Ctx d)); eauto.
    ii. apply PRE. split; des; eauto.
    right. exists (EM (Ctx C0) M (Ctx d)).
    split; ss; eauto. apply PRE. ss. rw. eauto.
  - apply PRE. ss. split; eauto.
    exists (Closure x e C0); ss.
  - eapply IHp with (n := (Ctx C0)); eauto.
    ii. apply PRE. split; des; eauto.
    right. exists (Ev (Ptr t) (v_fn x e0) (Ctx C0)).
    split; ss; eauto. apply PRE. ss. split; eauto.
    exists (Closure x e0 C0); ss.
Qed.

Lemma vpath_less_then_vpath_more `{Eq T} :
  forall a b p n (VAL : valid_path n a p),
  valid_path n (a ++ b) p.
Proof.
  ii.
  ginduction p; ii; ss;
  repeat des_hyp; des; clarify; eauto.
  des_hyp; des; clarify.
  exists (Closure x e C0).
  rewrite read_top. rewrite <- VAL. eauto.
Qed.

Lemma vedge_less_then_vedge_more `{Eq T} :
  forall a b e (VAL : valid_edge a e),
  valid_edge (a ++ b) e.
Proof.
  ii.
  destruct e; ss; repeat des_hyp; des; clarify.
  des_hyp; des; clarify.
  exists (Closure x e C).
  rewrite read_top. rewrite <- VAL. eauto.
Qed.

Lemma paste_vpath `{Eq T} :
  forall n m e (REACH : reachable n m e) e'
    (REACH' : reachable (rvertex e) m e'),
  reachable n m e'.
Proof.
  ii. destruct REACH as [p [VAL IN]].
  ginduction p; ii; ss; repeat des_hyp; des; clarify; ss.
  - destruct REACH' as [p' [VAL' IN']].
    exists (Px x (Ptr t0) p').
    ss. rw. eauto.
  - exploit IHp; eauto. intros REACH.
    destruct REACH as [p' [VAL' IN']].
    exists (Px x (Ptr t0) p').
    ss. rw. eauto.
  - destruct REACH' as [p' [VAL' IN']].
    exists (PM M (Ctx d) p').
    ss. rw. eauto.
  - exploit IHp; eauto. intros REACH.
    destruct REACH as [p' [VAL' IN']].
    exists (PM M (Ctx d) p').
    ss. rw. eauto.
  - des_hyp; des; clarify.
    destruct REACH' as [p' [VAL' IN']].
    exists (Pv (v_fn x e) (Ctx C0) p').
    ss. split; eauto.
    exists (Closure x e C0). eauto.
  - des_hyp; des; clarify.
    exploit IHp; eauto. intros REACH.
    destruct REACH as [p' [VAL' IN']].
    exists (Pv (v_fn x e0) (Ctx C0) p').
    ss. split; eauto.
    exists (Closure x e0 C0). eauto.
Qed.

Lemma step_spec_right `{Eq T} :
  forall m n E
    (PRE : forall e, In e E -> reachable n (memify E) e)
    (DISJ : forall t, InL (Ptr t) E = true -> None = read m t),
    let (E', m') := reach_m_step E m in
    (forall e (IN : In e E'), reachable n (memify E') e) /\
    (forall t (LEFT : InL (Ptr t) E' = true), None = read m' t) /\
    (forall t (LEFT : InL (Ptr t) E' = true /\ InL (Ptr t) E = false),
      InR (Ptr t) E = true).
Proof.
  ii.
  match goal with
  | |- match ?E with _ => _ end =>
    destruct E as [E' m'] eqn:STEP
  end; ii.
  ginduction m; ii; ss; clarify; eauto.
  assert (forall e, In e E' -> valid_edge (memify E') e) as HINT.
  {
    ii. exploit PRE; eauto. ii.
    rewrite reachable_eq_def in *. des; eauto.
  }
  repeat split; eauto. ii.
  {
    des. rewrite InL_In in LEFT. des.
    apply PRE in LEFT. rewrite reachable_eq_def in LEFT.
    destruct LEFT as [VAL ?].
    destruct e; ss; repeat des_hyp; des; clarify;
    des_hyp; des; clarify;
    rewrite read_memify_In in VAL; eauto;
    assert (InL (Ptr t0) E' = true);
    try solve [rewrite InL_In; exists (Ev (Ptr t0) (v_fn x e) (Ctx C)); eauto];
    clarify.
  }
  des_hyp.
  assert (InL (Ptr t) E = false) as DISJ'.
  { refl_bool. intros contra. apply DISJ in contra. rewrite t_refl in *. clarify. }
  assert (forall e, In e E -> valid_edge (memify E) e) as HINT.
  {
    ii. exploit PRE; eauto. ii.
    rewrite reachable_eq_def in *. des; eauto.
  }
  split.
  repeat des_hyp; clarify; ii.
  - rewrite InR_In in *. des. rename IN into IN'.
    match goal with
    | H : _ |- _ => 
      apply PRE in H;
      unfold reachable in H;
      destruct H as [p [VAL IN]]
    end.
    rewrite app_memify. rewrite reach_C_memify_empty. s.
    assert (forall p', valid_path n (memify E) p' -> 
      valid_path n ((t, Closure x e0 C) :: memify E) p').
    {
      clear IHm PRE DISJ e1 IN HDES1 e IN'.
      ii. ginduction p'; ii; ss; repeat des_goal; clarify.
      des; clarify. split; eauto.
      des; clarify. split; eauto.
      rewrite eqb_eq in *. clarify.
      des. des_hyp. rewrite read_memify_In in *; eauto.
      des; clarify.
      assert (InL (Ptr t0) E = true).
      rewrite InL_In.
      exists (Ev (Ptr t0) (v_fn x0 e) (Ctx C1)). ss.
      clarify.
      des. des_hyp. des. clarify.
      exists (Closure x0 e C1); eauto.
    }
    rewrite in_app_iff in *.
    ss. des; clarify.
    + rewrite <- reach_C_eq_def in IN'.
      eapply paste_vpath. instantiate (1 := e1).
      exists p. split; eauto.
      rewrite <- HDES1.
      match goal with
      | _ : context [(?t, Closure ?x ?e ?C)] |- _ =>
        eapply paste_vpath;
        first [
          instantiate (1 := (Ev (Ptr t) (v_fn x e) (Ctx C)));
          exists (Pv (v_fn x e) (Ctx C) Pnil);
          ss; rewrite t_refl; split; eauto;
          exists (Closure x e C); eauto |
          idtac]
      end.
      ss. destruct IN' as [p' [VAL' IN']].
      exists p'. split; eauto.
      eapply vpath_less_then_vpath_more with (a := []). eauto.
    + eapply paste_vpath. instantiate (1 := e1). exists p. split; eauto.
      rewrite <- HDES1.
      match goal with
      | _ : context [(?t, Closure ?x ?e ?C)] |- _ =>
        exists (Pv (v_fn x e) (Ctx C) Pnil);
        ss; rewrite t_refl; split; eauto;
        exists (Closure x e C); eauto
      end.
    + apply PRE in IN'.
      destruct IN' as [p' [VAL' IN']].
      exists p'. split; eauto.
  - exploit IHm; ii; des; eauto.
    exploit DISJ; eauto.
    des_goal; clarify.
  - repeat des_hyp; clarify. repeat split.
    + ii. rewrite InL_app_iff in LEFT.
      des. rewrite reach_C_no_t in LEFT. clarify.
      ss. des_hyp. rewrite eqb_eq in *; clarify.
      apply remove_t_read.
      exploit DISJ; eauto.
      ii. des_hyp; clarify.
      rewrite eqb_neq in *.
      rewrite remove_t_read_some; eauto.
    + ii. rewrite InL_app_iff in LEFT.
      des. rewrite reach_C_no_t in LEFT. clarify.
      ss. des_hyp; clarify. rewrite eqb_eq in *; clarify.
    + exploit IHm; ii; des; eauto.
      exploit DISJ; eauto.
      des_goal; clarify.
      repeat split; eauto.
      ii. ss. des_goal; eauto.
      rewrite eqb_eq in *. clarify.
      assert (InR (Ptr t0) E = true).
      eauto. clarify.
Qed.

Lemma step_spec_lemma `{Eq T} :
  forall m n E
    (IN : forall e, In e E <-> reachable n (memify E) e)
    (DISJ : forall t, InL (Ptr t) E || InR (Ptr t) E = true ->
      None = read m t)
    (INn : InL n E || InR n E = true) e,
    In e E <-> reachable n (memify E ++ m) e.
Proof.
  ii. rewrite IN.
  split; intros REACH;
  destruct REACH as [p [VAL INV]];
  exists p; split; try assumption.
  apply vpath_less_then_vpath_more. eauto.
  assert (forall e, reachable n (memify E) e -> In e E) as REACH.
  ii. rewrite IN. eauto.
  clear IN e INV.
  ginduction p; ii; ss;
  repeat des_goal; des; clarify.
  - exploit (REACH (Ex (Ctx C) x (Ptr t0))).
    exists (Px x (Ptr t0) Pnil). ss. rw. eauto.
    ii.
    assert (InR (Ptr t0) E = true).
    rewrite InR_In. exists (Ex (Ctx C) x (Ptr t0)). ss.
    split; eauto. eapply IHp; eauto. rw. des_goal; eauto.
    intros e' REACH'. apply REACH.
    eapply paste_vpath.
    instantiate (1 := Ex (Ctx C) x (Ptr t0)).
    exists (Px x (Ptr t0) Pnil). ss. rw. eauto.
    ss.
  - exploit (REACH (EM (Ctx C0) M (Ctx d))).
    exists (PM M (Ctx d) Pnil). ss. rw. eauto.
    ii.
    assert (InR (Ctx d) E = true).
    rewrite InR_In. exists (EM (Ctx C0) M (Ctx d)). ss.
    split; eauto. eapply IHp; eauto. rw. des_goal; eauto.
    intros e' REACH'. apply REACH.
    eapply paste_vpath.
    instantiate (1 := EM (Ctx C0) M (Ctx d)).
    exists (PM M (Ctx d) Pnil). ss. rw. eauto.
    ss.
  - destruct ev; des; clarify.
    rewrite read_top in *.
    destruct (read (memify E) t) eqn:READ.
    + clarify. exists (Closure x e C0).
      repeat split; eauto.
      eapply IHp; eauto.
      assert (InR (Ctx C0) E = true).
      rewrite InR_In.
      exists (Ev (Ptr t) (v_fn x e) (Ctx C0)).
      split; eauto. apply REACH.
      exists (Pv (v_fn x e) (Ctx C0) Pnil).
      ss. split; eauto. exists (Closure x e C0); eauto.
      rw. des_goal; eauto.
      intros e' REACH'. apply REACH.
      eapply paste_vpath.
      instantiate (1 := Ev (Ptr t) (v_fn x e) (Ctx C0)).
      exists (Pv (v_fn x e) (Ctx C0) Pnil).
      ss. split; eauto. exists (Closure x e C0); eauto.
      ss.
    + assert (None = read m t) as RR.
      apply DISJ. rw. eauto.
      rewrite <- RR in *. clarify.
Qed.

Fixpoint prefixof {T} (p p' : path T) :=
  match p, p' with
  | Pnil, _ => True
  | Px x ntx p, Px x' ntx' p' =>
    x = x' /\ ntx = ntx' /\ prefixof p p'
  | PM M nCM p, PM M' nCM' p' =>
    M = M' /\ nCM = nCM' /\ prefixof p p'
  | Pv v nCv p, Pv v' nCv' p' =>
    v = v' /\ nCv = nCv' /\ prefixof p p'
  | _, _ => False
  end.

Lemma prefixof_app {T} :
  forall (p a b : path T),
    prefixof p (a +++ b) <->
      prefixof p a \/ (exists p', p = a +++ p' /\ prefixof p' b).
Proof.
  assert (forall (pfx a b : path T), (prefixof a b) -> prefixof (pfx +++ a) (pfx +++ b)).
  { induction pfx; intros; simpl; repeat split; eauto. }
  induction p; intros; split; intros PFX; ss;
  match goal with
  | |- True \/ _ => left; auto
  | _ => repeat des_goal; repeat des_hyp; clarify; des; ss; clarify
  end;
  match goal with
  | _ => rewrite IHp in *; des; clarify; eauto
  | _ => idtac
  end;
  match goal with
  | |- False \/ _ =>
    right; eexists; split; try reflexivity; s; auto
  | _ => repeat split; try reflexivity; rewrite <- IHp; auto
  end.
Qed.

Lemma iso_comm `{Eq T} `{Eq TT} :
  forall (C : dy_ctx T) m (C' :dy_ctx TT) m' f f',
  iso C m C' m' f f' <-> iso C' m' C m f' f.
Proof.
  ii; split; ii; unfold iso in *; des;
  repeat (split; eauto).
Qed.

Lemma asame_comm `{Eq T} :
  forall m m',
  asame m m' <-> asame m' m.
Proof.
  intros; unfold asame; split; ii; rw; eauto.
Qed.

Lemma aiso_comm `{Eq T} `{Eq TT} :
  forall (C : dy_ctx T) m (C' :dy_ctx TT) m' f f',
  aiso C m C' m' f f' <-> aiso C' m' C m f' f.
Proof.
  ii; split; ii; unfold aiso in *; des;
  repeat (split; eauto).
Qed.

Lemma same_valid `{Eq T} :
  forall p n m m' (SAME : same m m')
    (VALp : valid_path n m p),
  valid_path n m' p.
Proof.
  ii; unfold same in *;
  ginduction p; intros; ss;
  repeat des_goal; repeat des_hyp; clarify;
  des; try split; eauto.
  - exists ev. split. rewrite <- SAME. eauto.
    des_hyp; des; repeat split; eauto.
Qed.

Lemma asame_avalid `{Eq T} :
  forall p n m m' (SAME : asame m m')
    (VALp : avalid_path n m p),
  avalid_path n m' p.
Proof.
  ii; unfold asame in *;
  ginduction p; intros; ss;
  repeat des_goal; repeat des_hyp; clarify;
  des; try split; eauto.
  - exists ev. split. rewrite <- SAME. eauto.
    des_hyp; des; repeat split; eauto.
Qed.

Lemma same_equiv `{Eq T} `{Eq TT} :
  forall (V : dy_value T) m (V' : dy_value TT) m' m''
    (EQUIV : <|V m ≃ V' m'|>) (SAME : same m' m''),
  <|V m ≃ V' m''|>.
Proof.
  intros. red in EQUIV; repeat des_hyp; des; clarify; red;
  repeat split; try reflexivity; exists f; exists f';
  unfold iso in *; des;
  (split; 
  first [assumption | split];
  first [assumption | split]); ii;
  match goal with
  | H : _ |- context [valid_path (Ctx ?C) m''] =>
    specialize (H p VALp); des; split; eauto;
    remember (pmap f p) as p';
    remember (Ctx C) as n;
    clear Heqn Heqp' VALp
  | H : context [valid_path (Ctx ?C) m'] |- _ =>
    apply H; remember (Ctx C) as n;
    clear Heqn
  end; 
  solve [eapply same_valid; eauto |
  rewrite same_comm in *; eapply same_valid; eauto].
Qed.


Lemma asame_aequiv `{Eq T} `{Eq TT} :
  forall (V : dy_value T) m (V' : dy_value TT) m' m''
    (EQUIV : <|V m ≃# V' m'|>) (SAME : asame m' m''),
  <|V m ≃# V' m''|>.
Proof.
  intros. red in EQUIV; repeat des_hyp; des; clarify; red;
  repeat split; try reflexivity; exists f; exists f';
  unfold aiso in *; des;
  (split; 
  first [assumption | split];
  first [assumption | split]); ii;
  match goal with
  | H : _ |- context [avalid_path (Ctx ?C) m''] =>
    specialize (H p VALp); des; split; eauto;
    remember (pmap f p) as p';
    remember (Ctx C) as n;
    clear Heqn Heqp' VALp
  | H : context [avalid_path (Ctx ?C) m'] |- _ =>
    apply H; remember (Ctx C) as n;
    clear Heqn
  end;
  solve [eapply asame_avalid; eauto |
  rewrite asame_comm in *; eapply asame_avalid; eauto].
Qed.

(* lift unreachable Cs *)
Fixpoint lift_C `{Eq T} `{Eq aT}
  (inv_α : (T * aT) -> T) (t : T) (C : dy_ctx aT) :=
  match C with
  | [||] => [||]
  | dy_binde x tx C =>
    let tx := inv_α (t, tx) in
    let C := lift_C inv_α t C in
    dy_binde x tx C
  | dy_bindm M C_M C =>
    let C_M := lift_C inv_α t C_M in
    let C := lift_C inv_α t C in
    dy_bindm M C_M C
  end.

Fixpoint fst_trans `{Eq T} `{Eq TT} 
  (trans : list (node T * node TT)) (n : node T) :=
  match trans with
  | [] => None
  | (f, s) :: tl =>
    if eqb f n then Some s else fst_trans tl n
  end.

Fixpoint snd_trans `{Eq T} `{Eq TT} 
  (trans : list (node T * node TT)) (n : node TT) :=
  match trans with
  | [] => None
  | (f, s) :: tl =>
    if eqb s n then Some f else snd_trans tl n
  end.

(* assumed : f (α C) ≃# aC except for paths starting with
 * x in seenx and M in seenM, when f is a graph isomorphism *)
(* trans: holds translated equivalent nodes *)
Fixpoint trans_equiv_C_aux `{Eq T} `{Eq TT} `{Eq aTT}
  (inv_α : (TT * aTT) -> TT)
  (t : TT) (trans : list (node T * node TT)) seenx seenM
  (C : dy_ctx T) (aC : dy_ctx aTT) :=
  match fst_trans trans (Ctx C) with
  | Some (Ctx C) => Some (t, trans, C) (* already translated *)
  | Some (Ptr _) => None
  | None =>
  let ret := match aC with
  | [||] => Some (t, trans, [||])
  | dy_binde x tx aC =>
    if Inb x seenx then (* unreachable *)
      let tx := inv_α (t, tx) in
      match trans_equiv_C_aux inv_α t trans seenx seenM C aC with
      | None => None
      | Some (t, trans, C) => Some (t, trans, dy_binde x tx C)
      end
    else match addr_x C x with (* reachable *)
    | None => None
    | Some addr =>
      let seenx := x :: seenx in
      match fst_trans trans (Ptr addr) with
      | Some (Ctx _) => None
      | Some (Ptr tx) =>
        match trans_equiv_C_aux inv_α t trans seenx seenM C aC with
        | None => None
        | Some (t, trans, C) => Some (t, trans, dy_binde x tx C)
        end
      | None =>
        let tx := inv_α (t, tx) in
        let trans := (Ptr addr, Ptr tx) :: trans in
        match trans_equiv_C_aux inv_α tx trans seenx seenM C aC with
        | None => None
        | Some (t, trans, C) => Some (t, trans, dy_binde x tx C)
        end
      end
    end
  | dy_bindm M C_M aC =>
    if Inb M seenM then (* unreachable *)
      let C_M := lift_C inv_α t C_M in
      match trans_equiv_C_aux inv_α t trans seenx seenM C aC with
      | None => None
      | Some (t, trans, C) => Some (t, trans, dy_bindm M C_M C)
      end
    else match ctx_M C M with (* reachable *)
    | None => None
    | Some C_M' =>
      let seenM := M :: seenM in
      match fst_trans trans (Ctx C_M') with
      | Some (Ptr _) => None
      | Some (Ctx C_M) =>
        match trans_equiv_C_aux inv_α t trans seenx seenM C aC with
        | None => None
        | Some (t, trans, C) => Some (t, trans, dy_bindm M C_M C)
        end
      | None =>
        match trans_equiv_C_aux inv_α t trans [] [] C_M' C_M with
        | None => None
        | Some (t, trans, C_M) =>
          match trans_equiv_C_aux inv_α t trans seenx seenM C aC with
          | None => None
          | Some (t, trans, C) => Some (t, trans, dy_bindm M C_M C)
          end
        end
      end
    end
  end in
  let top := match seenx, seenM with
  | [], [] => true
  | _, _ => false
  end in
  match ret with
  | None => None
  | Some (t, trans, C') =>
    if top
    then Some (t, (Ctx C, Ctx C') :: trans, C')
    else Some (t, trans, C')
  end end.


Definition trans_equiv_m :=
  (* check oracle, if reachable trans_equiv_C
     if unreachable lift_C *)
0.

Definition trans_equiv := 0.
