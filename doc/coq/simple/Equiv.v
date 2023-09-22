From Simple Require Export Abstract.
From Simple Require Export Concrete.

Ltac lebt x :=
  apply leb_trans with (t' := x);
  try assumption; try apply tick_lt; try apply leb_refl.

Generalizable Variables T aT TT aTT.

Definition time_bound_C `{TotalOrder T} C t :=
  forall t', supp_C C t' -> leb t' t = true.

Definition time_bound_m `{TotalOrder T} m t :=
  forall t', supp_m m t' -> leb t' t = true.

Definition time_bound_v `{TotalOrder T} v t :=
  match v with
  | Closure _ _ C => time_bound_C C t
  end.

Definition time_bound_V `{TotalOrder T} V t :=
  match V with
  | EVal ev => time_bound_v ev t
  | MVal mv => time_bound_C mv t
  end.

Definition time_bound_ρ `{TotalOrder T} (ρ : config T) :=
  match ρ with
  | Cf _ C m t =>
    time_bound_C C t /\ time_bound_m m t
  | Rs V m t =>
    time_bound_V V t /\ time_bound_m m t
  end.

Lemma not_le_lt `{TotalOrder T} :
  forall (p : T) t,
    (leb p t = false) <-> (t < p).
Proof.
  intros; unfold "<"; red; split; intros NLE;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- context [leb ?p ?t] =>
    let RR := fresh "RR" in
    destruct (leb p t) eqn:RR
  | |- context [eqb ?p ?t] =>
    let RR := fresh "RR" in
    destruct (eqb p t) eqn:RR
  | H : context [leb ?p ?t] |- _ =>
    match goal with
    | _ : leb p t = true |- _ => idtac
    | _ : leb p t = false |- _ => idtac
    | _ =>
      let RR := fresh "RR" in
      destruct (leb p t) eqn:RR
    end
  end;
  try rewrite eqb_eq in *;
  try rewrite eqb_neq in *; subst;
  try rewrite leb_refl in *;
  clarify; exfalso; eauto using leb_sym.
  pose proof leb_or as contra.
  specialize (contra p t).
  rewrite NLE in *. rewrite RR in *. clarify.
Qed.

Lemma time_bound_or_not `{TotalOrder T} :
  forall (p : T) t,
    (p < t) \/ ~(p < t).
Proof.
  intros.
  rewrite <- not_le_lt.
  destruct (leb t p); eauto.
Qed.

Lemma time_increase `{time T} :
  forall e C m t cf' (EVAL : {|(Cf e C m t) ~> cf'|}),
    match cf' with
    | Cf _ _ _ t'
    | Rs _ _ t' => leb t t' = true
    end.
Proof.
  intros.
  remember (Cf e C m t) as cf. ginduction EVAL;
  intros; clarify; try apply leb_refl; eauto 2;
  try (exploit IHEVAL3; eauto 1);
  try (exploit IHEVAL2; eauto 1);
  try (exploit IHEVAL1; eauto 1);
  try (exploit IHEVAL; eauto 1); intros;
  try lebt t';
  try lebt t_f;
  try lebt t_a;
  match goal with
  | _ : context [tick ?C ?m ?t ?x ?v] |- _ =>
    lebt (tick C m t x v)
  end.
Qed.

Lemma relax_ctx_bound `{time T} :
  forall C t1 t2 (BOUND : time_bound_C C t1) (LE : leb t1 t2 = true),
         time_bound_C C t2.
Proof.
  induction C; unfold time_bound_C;
  intros; ss; des; clarify;
  match goal with
  | H : supp_C ?C ?t |- _ =>
    match goal with
    | H : context [time_bound_C C _] |- _ => eapply H; eauto
    end
  | _ => idtac
  end; try red; intros; try apply BOUND; eauto.
  - lebt t1. apply BOUND. left; eauto.
Qed.

Lemma relax_p_bound `{time T} :
  forall p t1 t2 (BOUND : p < t1) (LE : leb t1 t2 = true),
    p < t2.
Proof.
  intros. destruct BOUND as [? EQ]. split.
  - lebt t1.
  - rewrite eqb_neq in *. red; intros.
    subst. apply EQ. apply leb_sym; eauto.
Qed.

Lemma relax_mem_bound `{time T} :
  forall m t1 t2 (BOUND : time_bound_m m t1) (LE : leb t1 t2 = true),
         time_bound_m m t2.
Proof.
  induction m; unfold time_bound_m;
  intros; ss; repeat des_hyp; clarify.
  lebt t1. apply BOUND. eauto.
Qed.

Lemma time_bound_addr `{time T} :
  forall C x t (BOUND : time_bound_C C t),
    match addr_x C x with
    | None => True
    | Some addr => leb addr t = true
    end.
Proof.
  induction C; unfold time_bound_C; intros; simpl in *; eauto;
  repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | IH : forall _ t, _ |- _ =>
    match type of IH with
    | context [addr_x ?C _] =>
      match goal with
      | RR : addr_x C ?x = _ |- _ =>
        specialize (IH x t);
        rewrite RR in IH;
        apply IH; red; intros
      end
    end
  | _ => idtac
  end; apply BOUND; eauto.
Qed.

Lemma time_bound_read `{time T} :
  forall m t addr (BOUND : time_bound_m m t),
    match read m addr with
    | None => True
    | Some v => time_bound_v v t
    end.
Proof.
  induction m; intros; simpl; eauto;
  repeat des_goal; repeat des_hyp; eauto;
  try rewrite eqb_eq in *; clarify;
  match goal with
  | _ => 
    unfold time_bound_m in *;
    unfold time_bound_v;
    des_goal; red; intros; simpl in *;
    apply BOUND; eauto; fail
  | RR : read ?m ?addr = Some ?v |- _ => 
    specialize (IHm t addr);
    rewrite RR in IHm;
    apply IHm; red; intros; apply BOUND; simpl; eauto
  end.
Qed.

Lemma time_bound_ctx_M `{time T} :
  forall C M t (BOUND : time_bound_C C t),
    match ctx_M C M with
    | None => True
    | Some CM => time_bound_C CM t
    end.
Proof.
  induction C; unfold time_bound_C; intros; simpl in *; eauto;
  repeat des_goal; repeat des_hyp; clarify;
  match goal with
  | IH : forall _ t, _ |- _ =>
    match type of IH with
    | context [ctx_M ?C _] =>
      match goal with
      | RR : ctx_M C ?M = _ |- _ =>
        specialize (IH M t);
        rewrite RR in IH;
        apply IH; red; intros
      end
    end
  | _ => idtac
  end; try apply BOUND; eauto.
Qed.

Lemma leb_t_neq_tick `{time T} :
  forall C m x v (t' t : T) (LE : leb t' t = true),
  eqb t' (tick C m t x v) = false.
Proof.
  intros. refl_bool. intros contra.
  rewrite eqb_eq in *.
  assert (t <> tick C m t x v) as NEQ.
  { rewrite <- eqb_neq. apply tick_lt. }
  apply NEQ. apply leb_sym. 
  - apply tick_lt.
  - subst. eauto.
Qed.

Lemma time_bound_tick `{time T} :
  forall C m t x v
         (BOUNDv : time_bound_v v t)
         (BOUNDm : time_bound_m m t),
  time_bound_m ((tick C m t x v) !-> v; m) (tick C m t x v).
Proof.
  intros.
  unfold time_bound_v in *.
  unfold time_bound_m in *. des_hyp.
  unfold time_bound_C in *.
  ii; ss; des; clarify;
  match goal with
  | |- leb ?t ?t = true => apply leb_refl
  | H : supp_C ?C _, 
    BD : forall _, supp_C ?C _ -> _
    |- leb _ (tick _ _ ?t _ _) = true  =>
    apply BD in H; lebt t
  | H : supp_m ?m _,
    BD : forall _, supp_m ?m _ -> _ 
    |- leb _ (tick _ _ ?t _ _) = true =>
    apply BD in H; lebt t
  end.
Qed.

Lemma trans_m_update `{TotalOrder T} {TT} (α : T -> TT) :
  forall m t t' v (BOUND : time_bound_m m t) (LT : t < t'),
    trans_m α (t' !-> v; m) =
    (α t' !-> trans_v α v; trans_m α m).
Proof.
  intros.
  assert (
    forall l l' 
      (IN : forall t'', (In t'' l' -> t' = t'' \/ In t'' l) /\ (In t'' l -> In t'' l')),
    trans_m_aux α m l = trans_m_aux α m l') as RR.
  {
    intros. ginduction m; intros; simpl; eauto.
    repeat des_goal; try rewrite eqb_eq in *; clarify;
    try rewrite Inb_eq in *; try rewrite Inb_neq in *;
    match goal with
    | _ : In ?t _ |- _ = _ :: _ =>
      specialize (IN t) as [L R];
      match goal with
      | H : In _ _ |- _ => apply R in H; contradict
      end
    | _ : In ?t _ |- _ :: _ = _ =>
      specialize (IN t) as [L R];
      match goal with
      | H : In _ _ |- _ => apply L in H; des; clarify
      end; rewrite <- not_le_lt in LT;
      match goal with
      | _ => contradict
      | _ => 
        assert (false = true);
        try (rewrite <- LT; apply BOUND; s; auto);
        contradict
      end
    | _ => erewrite IHm; eauto;
      match goal with
      | |- context [time_bound_m] => red; ii; apply BOUND; s; auto
      | |- forall _, _ =>
        ii; split; ii; ss; des; auto;
        match goal with
        | H : In ?t _ |- _ =>
          specialize (IN t) as [L R];
          first [apply L in H | apply R in H]; des; eauto
        end
      end
    end.
  }
  unfold trans_m, update_m. s.
  symmetry. erewrite RR; eauto.
  intros; simpl; split; intros; eauto.
Qed.

Lemma time_bound `{time T} :
  forall e C m t cf'
         (EVAL : {|(Cf e C m t) ~> cf'|})
         (BOUND : time_bound_ρ (Cf e C m t)),
    time_bound_ρ cf'.
Proof.
  intros. remember (Cf e C m t) as cf.
  ginduction EVAL; intros; simpl; clarify;
  unfold time_bound_ρ in *; eauto; destruct BOUND;
  split; try assumption;
  match goal with
  | RR : read ?m ?addr = Some _ |- _ =>
    match goal with
    | H : time_bound_m m ?t |- _ =>
      pose proof (time_bound_read m t addr H);
      rewrite RR in *; assumption
    end
  | RR : ctx_M ?C ?M = Some _ |- _ =>
    let HINT := fresh "HINT" in
    pose proof (time_bound_ctx_M C M) as HINT;
    rewrite RR in HINT; apply HINT; eauto
  | _ =>
    repeat match goal with
    | EVAL : {|(Cf ?e ?C ?m ?t) ~> ?cf|} |- _ =>
      lazymatch goal with
      | _ : leb t _ = true |- _ => fail
      | _ => pose proof (time_increase e C m t cf EVAL); simpl in *
      end
    end
  end;
  repeat match goal with
  | IH : forall e C m t, _ -> _ -> ?P /\ ?Q |- _ =>
    edestruct IH; eauto;
    match goal with
    | _ : P |- _ => 
      clear IH; unfold time_bound_v in *;
      repeat des_goal; repeat des_hyp
    | |- _ /\ _ => split;
      match goal with
      | |- time_bound_C ?C ?t =>
        match goal with
        | _ : time_bound_C C ?t' |- _ =>
          apply relax_ctx_bound with (t1 := t'); assumption
        end
      | |- time_bound_m ?m ?t => assumption
      end
    end
  end; subst;
  try (edestruct IHEVAL3; eauto);
  try (edestruct IHEVAL2; eauto);
  repeat match goal with
  | |- _ /\ _ => split
  | |- time_bound_C ?C ?t =>
    red; intros; simpl in *;
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H; subst; try apply tick_lt
    | _ : supp_C ?C ?t |- leb ?t _ = true =>
      match goal with
      | H : time_bound_C C ?t' |- _ =>
        lebt t'; try apply H; eauto 3
      end
    end
  | |- time_bound_m ?m ?t => 
    first [assumption |
    apply time_bound_tick; simpl; assumption]
  end;
  first [apply leb_refl | lebt t_a | lebt t'].
Qed.

Fixpoint remove_x {T} (C : dy_ctx T) x :=
  match C with
  | [||] => [||]
  | dy_binde x' t C' =>
    let C' := remove_x C' x in
    if eqb_ID x x' then C' else dy_binde x' t C'
  | dy_bindm M C' C'' =>
    dy_bindm M C' (remove_x C'' x)
  end.

Fixpoint remove_M {T} (C : dy_ctx T) M :=
  match C with
  | [||] => [||]
  | dy_binde x t C' =>
    dy_binde x t (remove_M C' M)
  | dy_bindm M' C' C'' =>
    let C'' := remove_M C'' M in
    if eqb_ID M M' then C'' else dy_bindm M' C' C''
  end.

Fixpoint remove_t `{Eq T} (m : memory T) t :=
  match m with
  | [] => []
  | (t', v) :: tl =>
    let tl := remove_t tl t in
    if eqb t t' then tl else (t', v) :: tl
  end.

Fixpoint reach_C `{Eq T} seenx seenM (C : dy_ctx T) :=
  match C with
  | [||] => []
  | dy_binde x t C =>
    if Inb x seenx then reach_C seenx seenM C
    else t :: reach_C (x :: seenx) seenM C
  | dy_bindm M C C' =>
    if Inb M seenM then reach_C seenx seenM C
    else reach_C [] [] C ++ reach_C seenx (M :: seenM) C'
  end.

Fixpoint reach_m_step `{Eq T} acc (m : memory T) :=
  match m with
  | [] => (acc, [])
  | (t, v) :: m =>
    if Inb t acc then match v with
    | Closure _ _ C =>
      (reach_C [] [] C ++ acc, remove_t m t)
    end else match reach_m_step acc m with
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

Definition reach_m `{Eq T} init (m : memory T) :=
  reach_m_aux init m (List.length m).

Lemma remove_t_dec_len `{Eq T} :
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

Lemma reach_m_step_dec_len `{Eq T} :
  forall (m : memory T) acc,
  match reach_m_step acc m with
  | (_, m') => List.length m' <= List.length m
  end.
Proof.
  induction m; intros; simpl; eauto;
  repeat des_goal; repeat des_hyp; clarify; simpl.
  - pose proof (remove_t_dec_len m t). nia.
  - specialize (IHm acc).
    repeat des_hyp; clarify. nia.
Qed.

Lemma reach_m_aux_some `{Eq T} :
  forall fuel m init (GE : (List.length m) <= fuel),
    exists reached, reach_m_aux init m fuel = Some reached.
Proof.
  induction fuel; intros; destruct m; simpl in *; eauto;
  try (inversion GE; fail).
  assert (List.length m <= fuel). { nia. }
  repeat des_goal; repeat des_hyp; clarify; eauto; apply IHfuel;
  match goal with
  | _ => pose proof (remove_t_dec_len m t); nia
  | _ => idtac
  end.
  - pose proof (reach_m_step_dec_len m init).
    repeat des_hyp; ss; clarify.
    rewrite Nat.eqb_neq in *. nia.
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

Lemma reach_m_some `{Eq T} :
  forall m init, exists reached, reach_m init m = Some reached.
Proof.
  intros. unfold reach_m. apply reach_m_aux_some. eauto.
Qed.

Inductive Mpath {T} : path T -> Prop :=
  | Mnil
    : Mpath Pnil
  | Mcons
    (p : path T) (M : ID) (C : dy_ctx T) (Mp : Mpath p)
    : Mpath (p +++ (PM M (Ctx C) Pnil))
.

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

Lemma asame_aequiv `{Eq T} `{Eq TT} :
  forall (V : dy_value T) m (V' : dy_value TT) m' m''
    (EQUIV : <|V m ≃# V' m'|>) (SAME : asame m' m''),
  <|V m ≃# V' m''|>.
Proof.
  intros. red in EQUIV.
  destruct EQUIV as [f [f' [EQl EQr]]].
  unfold asame in SAME.
  red. exists f. exists f'. split; simpl in *.
  - intros. specialize (EQl p VALp).
    split; try apply EQl.
    destruct EQl as [EQ ELSE].
    clear ELSE EQr VALp. remember (pmap f p) as p'.
    clear Heqp' p f f' m V.
    ginduction p'; intros; simpl in *;
    repeat des_goal; repeat des_hyp; clarify; eauto.
    + destruct EQ as [? [ev [IN VALp]]]; subst.
      split; eauto. exists ev.
      split. rewrite <- SAME. eauto.
      eapply IHp'; eauto.
    + destruct EQ as [? VALp]; subst.
      split; eauto.
    + destruct EQ as [? [? VALp]]; subst.
      repeat split; eauto.
  - intros. apply EQr.
    clear EQl EQr f f' V.
    ginduction p'; intros; simpl in *;
    repeat des_goal; repeat des_hyp; clarify; eauto.
    + destruct VALp' as [? [ev [IN ?]]]; subst.
      split; eauto. exists ev.
      split. rewrite SAME. eauto.
      eapply IHp'; eauto.
    + destruct VALp' as [? ?]; subst.
      split; eauto.
    + destruct VALp' as [? [? ?]]; subst.
      repeat split; eauto.
Qed.

Lemma same_equiv `{Eq T} `{Eq TT} :
  forall (V : dy_value T) m (V' : dy_value TT) m' m''
    (EQUIV : <|V m ≃ V' m'|>) (SAME : same m' m''),
  <|V m ≃ V' m''|>.
Proof.
  intros. red in EQUIV.
  destruct EQUIV as [f [f' [EQl EQr]]].
  unfold same in SAME.
  red. exists f. exists f'. split; simpl in *.
  - intros. specialize (EQl p VALp).
    split; try apply EQl.
    destruct EQl as [EQ ELSE].
    clear ELSE EQr VALp. remember (pmap f p) as p'.
    clear Heqp' p f f' m V.
    ginduction p'; intros; simpl in *;
    repeat des_goal; repeat des_hyp; clarify; eauto.
    + destruct EQ as [? [ev [IN VALp]]]; subst.
      split; eauto. exists ev.
      split. rewrite <- SAME. eauto.
      eapply IHp'; eauto.
    + destruct EQ as [? VALp]; subst.
      split; eauto.
    + destruct EQ as [? [? VALp]]; subst.
      repeat split; eauto.
  - intros. apply EQr.
    clear EQl EQr f f' V.
    ginduction p'; intros; simpl in *;
    repeat des_goal; repeat des_hyp; clarify; eauto.
    + destruct VALp' as [? [ev [IN ?]]]; subst.
      split; eauto. exists ev.
      split. rewrite SAME. eauto.
      eapply IHp'; eauto.
    + destruct VALp' as [? ?]; subst.
      split; eauto.
    + destruct VALp' as [? [? ?]]; subst.
      repeat split; eauto.
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
