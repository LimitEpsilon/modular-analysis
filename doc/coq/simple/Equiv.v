From Simple Require Export Bound.

Generalizable Variables T TT aT aTT.

Lemma same_top_app {T} :
  forall (a b c : list T) (EQ : a ++ b = a ++ c), b = c.
Proof.
  induction a; ii; ss; clarify; eauto.
Qed.

Lemma same_top_capp {T} :
  forall (a b c : dy_ctx T) (EQ : a +++ b = a +++ c), b = c.
Proof.
  induction a; ii; ss; clarify; eauto.
Qed.

Lemma capp_nil_r {T} :
  forall (C : dy_ctx T), C +++ ([||]) = C.
Proof.
  induction C; ii; ss; rw; exact eq_refl.
Qed.

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

Lemma eq_root_neq `{Eq T} :
  forall r r', eq_root r r' = false <-> r <> r'.
Proof.
  assert (eq_root = eqb) as RR. reflexivity.
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

Fixpoint remove_x `{Eq T} (C : dy_ctx T) x :=
  match C with
  | [||] => [||]
  | dy_binde x' tx C =>
    if eqb x x'
    then remove_x C x
    else dy_binde x' tx (remove_x C x)
  | dy_bindm M CM C =>
    dy_bindm M CM (remove_x C x)
  end.

Fixpoint remove_M `{Eq T} (C : dy_ctx T) M :=
  match C with
  | [||] => [||]
  | dy_binde x tx C =>
    dy_binde x tx (remove_M C M)
  | dy_bindm M' CM C =>
    if eqb M M'
    then remove_M C M
    else dy_bindm M' CM (remove_M C M)
  end.

Lemma remove_x_read_none `{Eq T} :
  forall C x, addr_x (remove_x C x) x = None.
Proof.
  induction C; ii; ss.
  repeat des_goal; eauto. clarify.
Qed.

Lemma remove_x_read_some `{Eq T} :
  forall C x x' (NEQ : x <> x'),
    addr_x (remove_x C x) x' = addr_x C x'.
Proof.
  induction C; ii; ss; eauto.
  repeat des_goal; eauto.
  rewrite eqb_ID_eq in *; clarify.
Qed.

Lemma remove_x_ctx `{Eq T} :
  forall C x M,
    ctx_M (remove_x C x) M = ctx_M C M.
Proof.
  induction C; ii; ss;
  repeat des_goal; clarify.
Qed.

Lemma remove_M_read_none `{Eq T} :
  forall C M, ctx_M (remove_M C M) M = None.
Proof.
  induction C; ii; ss.
  repeat des_goal; eauto. clarify.
Qed.

Lemma remove_M_read_some `{Eq T} :
  forall C M M' (NEQ : M <> M'),
    ctx_M (remove_M C M) M' = ctx_M C M'.
Proof.
  induction C; ii; ss; eauto.
  repeat des_goal; eauto.
  rewrite eqb_ID_eq in *; clarify.
Qed.

Lemma remove_M_addr `{Eq T} :
  forall C M x,
    addr_x (remove_M C M) x = addr_x C x.
Proof.
  induction C; ii; ss;
  repeat des_goal; clarify.
Qed.

Fixpoint read_fst `{Eq T} `{Eq TT}
  (ϕ : list (T * TT)) (t : T) :=
  match ϕ with
  | [] => None
  | (t', t'') :: tl =>
    if eqb t t' then Some t'' else read_fst tl t
  end.

Fixpoint read_snd `{Eq T} `{Eq TT}
  (ϕ : list (T * TT)) (t : TT) :=
  match ϕ with
  | [] => None
  | (t'', t') :: tl =>
    if eqb t t' then Some t'' else read_snd tl t
  end.

Lemma read_fst_top `{Eq T} `{Eq TT} :
  forall (a b : list (T * TT)) t,
  read_fst (a ++ b) t = 
  match read_fst a t with
  | None => read_fst b t
  | Some _ => read_fst a t
  end.
Proof.
  induction a; ii; ss;
  repeat des_goal; repeat des_hyp; clarify;
  repeat rw; reflexivity.
Qed.

Lemma read_snd_top `{Eq T} `{Eq TT} :
  forall (a b : list (T * TT)) t,
  read_snd (a ++ b) t = 
  match read_snd a t with
  | None => read_snd b t
  | Some _ => read_snd a t
  end.
Proof.
  induction a; ii; ss;
  repeat des_goal; repeat des_hyp; clarify;
  repeat rw; reflexivity.
Qed.

Fixpoint check_iso `{Eq T} `{Eq TT}
  (C' : dy_ctx TT) φ φ' (Cout Cin : dy_ctx T) :=
  match Cin with
  | [||] => if eqb C' ([||]) then true else false
  | dy_binde x tx Cin =>
    match addr_x Cout x with (* is it shadowed? *)
    | Some _ => check_iso C' φ φ' Cout Cin
    | None =>
      let Cout := dy_binde x tx Cout in
      match addr_x C' x with
      | Some tx' =>
        if eqb (φ tx) tx' && eqb tx (φ' tx') then
          check_iso (remove_x C' x) φ φ' Cout Cin
        else false
      | None => false
      end
    end
  | dy_bindm M CM Cin =>
    match ctx_M Cout M with (* is it shadowed? *)
    | Some _ => check_iso C' φ φ' Cout Cin
    | None =>
      let Cout := dy_bindm M CM Cout in
      match ctx_M C' M with
      | Some CM' =>
        if check_iso CM' φ φ' ([||]) CM then
          check_iso (remove_M C' M) φ φ' Cout Cin
        else false
      | None => false
      end
    end
  end.

Definition check_iso_spec `{Eq T} `{Eq TT}
  (C' : dy_ctx TT) φ φ' (Cout Cin : dy_ctx T) :=
  (forall x (VIS : addr_x Cout x = None) tx p
    (VALp : valid_path (Ctx Cin) [] (Px x tx p)),
    let p' := pmap φ p in
    valid_path (Ctx C') [] (Px x (φ tx) p') /\
    φ' (φ tx) = tx /\ p = pmap φ' p') /\
  (forall M (VIS : ctx_M Cout M = None) p
    (VALp : valid_path (Ctx Cin) [] (PM M p)),
    let p' := pmap φ p in
    valid_path (Ctx C') [] (PM M p') /\
    p = pmap φ' p') /\
  (forall x (VIS : addr_x Cout x = None) tx' p'
    (VALp' : valid_path (Ctx C') [] (Px x tx' p')),
    let p := pmap φ' p' in
    valid_path (Ctx Cin) [] (Px x (φ' tx') p) /\
    φ (φ' tx') = tx' /\ p' = pmap φ p) /\
  (forall M (VIS : ctx_M Cout M = None) p'
    (VALp' : valid_path (Ctx C') [] (PM M p')),
    let p := pmap φ' p' in
    valid_path (Ctx Cin) [] (PM M p) /\
    p' = pmap φ p).

Definition check_aiso_spec `{Eq T} `{Eq TT}
  (C' : dy_ctx TT) φ φ' (Cout Cin : dy_ctx T) :=
  (forall x (VIS : addr_x Cout x = None) tx p
    (VALp : avalid_path (Ctx Cin) [] (Px x tx p)),
    let p' := pmap φ p in
    avalid_path (Ctx C') [] (Px x (φ tx) p') /\
    φ' (φ tx) = tx /\ p = pmap φ' p') /\
  (forall M (VIS : ctx_M Cout M = None) p
    (VALp : avalid_path (Ctx Cin) [] (PM M p)),
    let p' := pmap φ p in
    avalid_path (Ctx C') [] (PM M p') /\
    p = pmap φ' p') /\
  (forall x (VIS : addr_x Cout x = None) tx' p'
    (VALp' : avalid_path (Ctx C') [] (Px x tx' p')),
    let p := pmap φ' p' in
    avalid_path (Ctx Cin) [] (Px x (φ' tx') p) /\
    φ (φ' tx') = tx' /\ p' = pmap φ p) /\
  (forall M (VIS : ctx_M Cout M = None) p'
    (VALp' : avalid_path (Ctx C') [] (PM M p')),
    let p := pmap φ' p' in
    avalid_path (Ctx Cin) [] (PM M p) /\
    p' = pmap φ p).

Lemma check_iso_spec_true `{Eq T} `{Eq TT} :
  forall (C' : dy_ctx TT) φ φ' (Cout Cin : dy_ctx T)
  (PREx : forall x, addr_x Cout x <> None -> addr_x C' x = None)
  (PREM : forall M, ctx_M Cout M <> None -> ctx_M C' M = None),
  check_iso C' φ φ' Cout Cin = true <->
  check_iso_spec C' φ φ' Cout Cin.
Proof.
  ii. split; intros ISO.
  - ginduction Cin; ii; ss; repeat des_hyp; des; clarify.
    + rewrite eqb_C_eq in *. clarify.
    + apply IHCin in ISO; eauto.
      unfold check_iso_spec in *. des.
      split. ii; ss.
      exploit ISO; eauto.
      repeat des_hyp; des; clarify.
      rewrite eqb_ID_eq in *. clarify.
      rw. eauto.
      split. eauto.
      split; eauto. ii; ss.
      exploit ISO1; eauto.
      ii. repeat des_goal; repeat des_hyp; des; clarify.
      rewrite eqb_ID_eq in *. clarify.
    + repeat rewrite eqb_eq in *. clarify.
      apply IHCin in ISO.
      unfold check_iso_spec in *. des.
      split. ii; ss.
      repeat des_hyp; des; clarify.
      rewrite eqb_ID_eq in *. clarify.
      rw. destruct p; ss; des; clarify.
      exploit ISO; eauto. rw. eauto. rw. eauto.
      rewrite remove_x_read_some. eauto.
      rewrite eqb_ID_neq in *. eauto.
      split. ii; ss.
      exploit ISO0; eauto.
      rewrite remove_x_ctx. eauto.
      split. ii; ss.
      des_goal; repeat des_hyp; des; clarify;
      match goal with
      | _ : eqb_ID _ _ = true |- _ =>
        rewrite eqb_ID_eq in *; clarify; rrw;
        destruct p'; ss; des; clarify
      | _ =>
        exploit ISO1; try rw; eauto;
        rewrite remove_x_read_some; try rw; eauto;
        rewrite eqb_ID_neq in *; eauto
      end.
      ii; ss. des_hyp; clarify.
      exploit ISO2; eauto.
      rewrite remove_x_ctx. rw. eauto.
      ii; ss. repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *. clarify.
      apply remove_x_read_none.
      rewrite remove_x_read_some. eauto.
      rewrite eqb_ID_neq in *. eauto.
      ii; ss. rewrite remove_x_ctx. eauto.
    + apply IHCin2 in ISO; eauto.
      unfold check_iso_spec in *. des.
      split. eauto.
      split. ii. ss.
      repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *; clarify.
      exploit ISO0; eauto. rw. eauto.
      split. eauto.
      ii. ss.
      repeat des_hyp; clarify.
      exploit ISO2; eauto. rw. eauto.
      ii. repeat des_hyp; des; clarify.
      split; eauto.
      des_goal; repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *; clarify.
    + match goal with 
      | H : _ |- _ =>
        let ISO := fresh "ISO'" in
        apply IHCin1 in H;
        first [solve [ii; ss] | rename H into ISO]
      end.
      apply IHCin2 in ISO. clear IHCin1 IHCin2.
      unfold check_iso_spec in *. des.
      split. ii. ss.
      exploit ISO; eauto. ii.
      rewrite remove_M_addr in *. eauto.
      split. ii. ss.
      repeat des_hyp; clarify.
      rewrite eqb_ID_eq in *. clarify. rw.
      destruct p; ss.
      exploit ISO'; eauto.
      ii; des; clarify. rw. rrw. eauto.
      exploit ISO'0; eauto.
      ii; des; clarify. rrw. eauto.
      exploit ISO0; eauto.
      rw. eauto. rw. eauto.
      rewrite remove_M_read_some. eauto.
      rewrite eqb_ID_neq in *. eauto.
      split. ii; ss.
      exploit ISO1; eauto.
      rewrite remove_M_addr. eauto.
      ii; ss.
      des_goal; repeat des_hyp; clarify;
      match goal with
      | _ : eqb_ID _ _ = true |- _ =>
        rewrite eqb_ID_eq in *; clarify;
        destruct p'; ss;
        match goal with
        | |- context [addr_x] =>
          exploit ISO'1; eauto;
          ii; repeat des_hyp; des; clarify;
          rw; rrw; eauto
        | |- context [ctx_M] =>
          exploit ISO'2; eauto;
          ii; repeat des_hyp; des; clarify;
          rrw; eauto
        end
      | _ : eqb_ID _ _ = false |- _ =>
        exploit ISO2; eauto;
        repeat match goal with
        | _ => rw
        | _ => solve [eauto]
        | _ => rewrite remove_M_read_some
        | _ => rewrite eqb_ID_neq in *
        end
      end.
      ii; ss. rewrite remove_M_addr. eauto.
      ii; ss. des_hyp; clarify.
      rewrite eqb_ID_eq in *. clarify.
      rewrite remove_M_read_none. eauto.
      rewrite remove_M_read_some. eauto.
      rewrite eqb_ID_neq in *. eauto.
  - ginduction Cin; ii; ss; clarify.
    assert (forall x, addr_x C' x = None) as contrax.
    {
      ii. destruct (addr_x Cout x) eqn:CASE.
      apply PREx. rw. ss.
      unfold check_iso_spec in *. des.
      destruct (addr_x C' x) eqn:CASE'; eauto.
      exploit ISO1; eauto. ss. rw. split. reflexivity.
      instantiate (1 := Pnil). ss.
      ii; des; ss.
    }
    assert (forall M, ctx_M C' M = None) as contraM.
    {
      ii. destruct (ctx_M Cout M) eqn:CASE.
      apply PREM. rw. ss.
      unfold check_iso_spec in *. des.
      destruct (ctx_M C' M) eqn:CASE'; eauto.
      exploit ISO2; eauto. ss. rw.
      instantiate (1 := Pnil). ss.
      ii; des; ss.
    }
    assert (C' = [||]) as RR.
    {
      destruct C'; ss.
      specialize (contrax x). rewrite ID_refl in *. clarify.
      specialize (contraM M). rewrite ID_refl in *. clarify.
    }
    rewrite RR. assert (eqb_C = eqb) as RR'. eauto.
    rewrite RR'. rewrite t_refl. eauto.
    + repeat des_goal; unfold check_iso_spec in *; des.
      apply IHCin; eauto.
      split. ii; ss.
      des_hyp; des; clarify.
      exploit ISO; eauto. des_goal; des_hyp; clarify.
      rewrite eqb_ID_eq in *. clarify.
      split. eauto.
      split; eauto.
      ii. ss. des_hyp; des; clarify.
      exploit ISO1; eauto. rw. eauto.
      eauto. ii. repeat des_hyp; des; clarify.
      rewrite eqb_ID_eq in *. clarify.
      repeat rw. eauto.
      apply IHCin; eauto.
      ii; ss. des_hyp; clarify.
      rewrite eqb_ID_eq in *. clarify. apply remove_x_read_none.
      rewrite remove_x_read_some. eauto.
      rewrite eqb_ID_neq in *. eauto.
      ii; ss. rewrite remove_x_ctx. eauto.
      repeat rewrite eqb_eq in *. clarify.
      unfold check_iso_spec in *. des.
      split. ii; ss.
      repeat des_hyp; des; clarify.
      exploit ISO; eauto.
      rw. rw. eauto.
      rewrite remove_x_read_some. eauto.
      rewrite eqb_ID_neq in *. eauto.
      split. ii; ss.
      repeat des_hyp; des; clarify.
      exploit ISO0; eauto.
      rw. eauto. rewrite remove_x_ctx. eauto.
      split; ii; ss; repeat des_hyp; des; clarify.
      exploit ISO1; eauto.
      rewrite remove_x_read_some in *.
      rw. split; eauto. rewrite eqb_ID_neq in *. eauto.
      rw. eauto.
      exploit ISO2; eauto.
      rewrite remove_x_ctx in *. rw. eauto.
      rewrite eqb_eq in *. clarify.
      exploit ISO1. eauto.
      ss. rw. split. reflexivity.
      instantiate (1 := Pnil). ss.
      ii; des; ss. rewrite ID_refl in *.
      des; clarify. rewrite eqb_neq in *. contradict.
      exploit ISO1. eauto. ss. rw.
      split. reflexivity. instantiate (1 := Pnil). ss.
      ii; des; ss. rewrite ID_refl in *.
      des; clarify. rewrite eqb_neq in *. contradict.
      exploit ISO. eauto.
      ss. rewrite ID_refl. split; eauto.
      instantiate (1 := Pnil). ss.
      ii; des; ss. des_hyp; clarify.
    + repeat des_goal; unfold check_iso_spec in *; des.
      apply IHCin2; eauto.
      split. eauto.
      split. ii. ss.
      des_hyp; clarify.
      exploit ISO0; eauto. rw.
      des_goal; des_hyp; clarify.
      rewrite eqb_ID_eq in *; clarify.
      split; eauto. ii. ss.
      des_hyp; clarify.
      exploit ISO2; eauto. rw. eauto.
      ii. repeat des_hyp; des; clarify.
      rewrite eqb_ID_eq in *; clarify.
      des_goal; clarify.
      apply IHCin2.
      ii; ss. rewrite remove_M_addr. eauto.
      ii; ss. des_hyp; clarify.
      rewrite eqb_ID_eq in *; clarify.
      apply remove_M_read_none.
      rewrite remove_M_read_some; eauto.
      rewrite eqb_ID_neq in *. eauto.
      split. ii. ss.
      des_hyp; des; clarify.
      rewrite remove_M_addr.
      exploit ISO; eauto. rw. eauto.
      split. ii; ss.
      repeat des_hyp; clarify.
      rewrite remove_M_read_some.
      exploit ISO0; eauto. rw. rw. eauto.
      rewrite eqb_ID_neq in *. eauto.
      split; ii; ss.
      rewrite remove_M_addr in *. eauto.
      repeat des_hyp; clarify.
      rewrite remove_M_read_some in *.
      exploit ISO2; eauto. rw. eauto.
      rw. eauto. rewrite eqb_ID_neq in *. eauto.
      assert (iso (Ctx d) [] (Ctx Cin1) [] φ' φ) as [HINT HINT'].
      {
        split; ii; ss.
        exploit (ISO2 M). eauto. rw. eauto.
        rewrite ID_refl. subst p'. ii; des; eauto.
        exploit (ISO0 M). eauto.
        rewrite ID_refl. eauto. rw. subst p.
        ii; des; eauto.
      }
      assert (check_iso d φ φ' ([||]) Cin1 <> true) as RR.
      refl_bool. eauto.
      exfalso. apply RR. apply IHCin1; try solve [ii; ss].
      repeat first [ii;
      solve [exploit HINT'; eauto;
            ii; ss; des; clarify|
            exploit HINT; eauto;
            ii; ss; des; clarify] | split].
      exploit ISO0. eauto. instantiate (1 := Pnil). ss.
      rewrite ID_refl. eauto.
      ii; des; ss. des_hyp; clarify.
Qed.

Lemma empty_then_avalid_valid `{Eq T} :
  forall p r,
  avalid_path r [] p <-> valid_path r [] p.
Proof.
  induction p; ii; ss;
  repeat des_goal; clarify.
  rw. eauto.
  split; ii; des; clarify.
Qed.

Lemma check_aiso_spec_true `{Eq T} `{Eq TT} :
  forall (C' : dy_ctx TT) φ φ' (Cout Cin : dy_ctx T)
  (PREx : forall x, addr_x Cout x <> None -> addr_x C' x = None)
  (PREM : forall M, ctx_M Cout M <> None -> ctx_M C' M = None),
  check_iso C' φ φ' Cout Cin = true <->
  check_aiso_spec C' φ φ' Cout Cin.
Proof.
  ii. pose proof (check_iso_spec_true C' φ φ' Cout Cin PREx PREM) as RR.
  rewrite RR. clear RR.
  split; intros ISO;
  unfold check_iso_spec in *;
  unfold check_aiso_spec in *;
  des.
  - split. ii. exploit (ISO x VIS tx p);
    rewrite empty_then_avalid_valid in *; eauto.
    split. ii. exploit (ISO0 M VIS p);
    rewrite empty_then_avalid_valid in *; eauto.
    split. ii. exploit (ISO1 x VIS tx' p');
    rewrite empty_then_avalid_valid in *; eauto.
    ii. exploit (ISO2 M VIS p');
    rewrite empty_then_avalid_valid in *; eauto.
  - split. ii. exploit (ISO x VIS tx p);
    rewrite empty_then_avalid_valid in *; eauto.
    split. ii. exploit (ISO0 M VIS p);
    rewrite empty_then_avalid_valid in *; eauto.
    split. ii. exploit (ISO1 x VIS tx' p');
    rewrite empty_then_avalid_valid in *; eauto.
    ii. exploit (ISO2 M VIS p');
    rewrite empty_then_avalid_valid in *; eauto.
Qed.

Definition iso_C `{Eq T} `{Eq TT} 
  (C : dy_ctx T) (C' :dy_ctx TT) φ φ' := 
  check_iso C' φ φ' ([||]) C
.

Lemma check_iso_iso `{Eq T} `{Eq TT} :
  forall (C' : dy_ctx TT) φ φ' (C : dy_ctx T),
  iso_C C C' φ φ' = true <->
  iso (Ctx C) [] (Ctx C') [] φ φ'.
Proof.
  unfold iso_C.
  ii; split; intros ISO;
  rewrite check_iso_spec_true in *; ii; ss.
  - unfold check_iso_spec in *. des.
    split. ii. subst p'. destruct p; try solve [ss].
    exploit ISO; eauto. ii; des.
    split; eauto. s. rrw. rw. eauto.
    exploit ISO0; eauto. ii; des.
    split; eauto. s. rrw. eauto.
    ii. subst p. destruct p'; try solve [ss].
    exploit ISO1; eauto. ii; des.
    split; eauto. s. rrw. rw. eauto.
    exploit ISO2; eauto. ii; des.
    split; eauto. s. rrw. eauto.
  - destruct ISO as [ISO ISO'].
    repeat first [ii;
      solve [exploit ISO; eauto; ii; ss; des; clarify
      | exploit ISO'; eauto; ii; ss; des; clarify]
      | split].
Qed.

Definition aiso_C `{Eq T} `{Eq TT} 
  (C : dy_ctx T) (C' :dy_ctx TT) φ φ' := 
  check_iso C' φ φ' ([||]) C
.

Lemma check_aiso_aiso `{Eq T} `{Eq TT} :
  forall (C' : dy_ctx TT) φ φ' (C : dy_ctx T),
  aiso_C C C' φ φ' = true <->
  aiso (Ctx C) [] (Ctx C') [] φ φ'.
Proof.
  unfold aiso_C.
  ii; split; intros ISO;
  rewrite check_aiso_spec_true in *; ii; ss.
  - unfold check_aiso_spec in *. des.
    split. ii. subst p'. destruct p; try solve [ss].
    exploit ISO; eauto. ii; des.
    split; eauto. s. rrw. rw. eauto.
    exploit ISO0; eauto. ii; des.
    split; eauto. s. rrw. eauto.
    ii. subst p. destruct p'; try solve [ss].
    exploit ISO1; eauto. ii; des.
    split; eauto. s. rrw. rw. eauto.
    exploit ISO2; eauto. ii; des.
    split; eauto. s. rrw. eauto.
  - destruct ISO as [ISO ISO'].
    repeat first [ii;
      solve [exploit ISO; eauto; ii; ss; des; clarify
      | exploit ISO'; eauto; ii; ss; des; clarify]
      | split].
Qed.

Lemma iso_C_is_aiso_C `{Eq T} `{Eq TT} (C : dy_ctx T) (C' : dy_ctx TT) φ φ' :
  iso_C C C' φ φ' = aiso_C C C' φ φ'.
Proof. reflexivity. Qed.

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

Fixpoint trans_iso_C `{Eq TT} `{TotalOrder T} `{Eq aT} (inv_α : (T * aT) -> T)
  (C' : dy_ctx TT) (ϕ : list (TT * T)) (t : T) (Cout : dy_ctx T) (Cin : dy_ctx aT) :=
  match Cin with
  | [||] => Some (Cout, ϕ, t)
  | dy_binde x tx Cin =>
    match addr_x Cout x with (* is it shadowed? *)
    | Some _ =>
      let tx := inv_α (t, tx) in
      trans_iso_C inv_α C' ϕ t (Cout +++ dy_binde x tx ([||])) Cin
    | None =>
      match addr_x C' x with
      | Some tx' =>
        match read_fst ϕ tx' with
        | Some tx =>
          trans_iso_C inv_α C' ϕ t (Cout +++ dy_binde x tx ([||])) Cin
        | None =>
          let tx := inv_α (t, tx) in
          let ϕ := (tx', tx) :: ϕ in
          trans_iso_C inv_α C' ϕ tx (Cout +++ dy_binde x tx ([||])) Cin
        end
      | None => None
      end
    end
  | dy_bindm M CM Cin =>
    match ctx_M Cout M with (* is it shadowed? *)
    | Some _ =>
      let CM := lift_C inv_α t CM in
      trans_iso_C inv_α C' ϕ t (Cout +++ dy_bindm M CM ([||])) Cin
    | None =>
      match ctx_M C' M with
      | Some CM' =>
        match trans_iso_C inv_α CM' ϕ t ([||]) CM with
        | Some (CM, ϕ, t) =>
          trans_iso_C inv_α C' ϕ t (Cout +++ dy_bindm M CM ([||])) Cin
        | None => None
        end
      | None => None
      end
    end
  end.

Definition inv_α_spec `{TotalOrder T} `{Eq aT}
  (α : T -> aT) (inv_α : (T * aT) -> T) :=
  forall t abs_t,
    t << inv_α (t, abs_t) /\
    abs_t = α (inv_α (t, abs_t)).

Lemma lift_C_lower `{TotalOrder T} `{Eq aT}
  (α : T -> aT) inv_α (SPEC : inv_α_spec α inv_α) :
  forall C t, trans_C α (lift_C inv_α t C) = C.  
Proof.
  induction C; ii; ss; repeat rw; eauto.
  destruct (SPEC t tx). rrw. eauto.
Qed.

Definition ϕ_spec `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (α : T -> aT) (φ : aTT -> aT) (φ' : aT -> aTT)
  (ϕ : list (TT * T)) (t : T) :=
  forall t'' t' (IN : In (t'', t') ϕ),
    Some t' = read_fst ϕ t'' /\
    Some t'' = read_snd ϕ t' /\
    leb t' t = true /\
    α t' = φ (α' t'') /\
    α' t'' = φ' (α t').

Lemma read_fst_in `{Eq T} `{Eq TT} (ϕ : list (T * TT)) :
  forall t t' (READ : Some t' = read_fst ϕ t),
    In (t, t') ϕ.
Proof.
  induction ϕ; ii; ss; repeat des_hyp; clarify; eauto.
  rewrite eqb_eq in *; clarify; eauto.
Qed.

Lemma in_read_fst `{Eq T} `{Eq TT} (ϕ : list (T * TT)) :
  forall t t' (IN : In (t, t') ϕ),
    exists t'', Some t'' = read_fst ϕ t.
Proof.
  induction ϕ; ii; ss; repeat des_hyp; des; clarify; eauto.
  rewrite t_refl. eauto.
  exploit IHϕ; eauto. ii; des; clarify.
  repeat des_goal; clarify; eauto.
Qed.

Lemma read_snd_in `{Eq T} `{Eq TT} (ϕ : list (T * TT)) :
  forall t t' (READ : Some t = read_snd ϕ t'),
    In (t, t') ϕ.
Proof.
  induction ϕ; ii; ss; repeat des_hyp; clarify; eauto.
  rewrite eqb_eq in *; clarify; eauto.
Qed.

Lemma in_read_snd `{Eq T} `{Eq TT} (ϕ : list (T * TT)) :
  forall t t' (IN : In (t, t') ϕ),
    exists t'', Some t'' = read_snd ϕ t'.
Proof.
  induction ϕ; ii; ss; repeat des_hyp; des; clarify; eauto.
  rewrite t_refl. eauto.
  exploit IHϕ; eauto. ii; des; clarify.
  repeat des_goal; clarify; eauto.
Qed.

Lemma ϕ_spec_app `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (α : T -> aT) (φ : aTT -> aT) (φ' : aT -> aTT) :
  forall (ϕ1 ϕ2 : list (TT * T)) (t : T)
    (SPECϕ : ϕ_spec α' α φ φ' (ϕ1 ++ ϕ2) t),
  ϕ_spec α' α φ φ' ϕ1 t /\ ϕ_spec α' α φ φ' ϕ2 t.
Proof.
  induction ϕ1; ii; ss.
  assert (ϕ_spec α' α φ φ' (ϕ1 ++ ϕ2) t).
  {
    ii. exploit (SPECϕ t'' t'); eauto.
    ss. rewrite in_app_iff in *. des; eauto.
    ii. des. ss. repeat des_hyp; clarify;
    first [rewrite t_refl in *; clarify |
      rewrite eqb_eq in *; clarify].
    repeat split; eauto.
    apply in_read_fst in IN as READ. des.
    apply read_fst_in in READ as IN'.
    exploit (SPECϕ t0 t''); ss; eauto.
    rewrite t_refl. ii; des; clarify.
    apply in_read_snd in IN as READ. des.
    apply read_snd_in in READ as IN'.
    exploit (SPECϕ t'' t1); ss; eauto.
    rewrite t_refl. ii; des; clarify.
  }
  exploit IHϕ1; eauto.
  ii. des. split; eauto.
  ii. ss.
  exploit (SPECϕ t'' t'). ss. rewrite in_app_iff.
  des; eauto. ii. des; clarify.
  - repeat rewrite t_refl. eauto.
  - exploit (x0 t'' t'). eauto.
    ii. des; clarify.
    ss.
    rewrite read_fst_top in *.
    rewrite read_snd_top in *.
    repeat des_hyp; clarify.
Qed.

Fixpoint pmap_fst `{Eq T} `{Eq TT} (ϕ: list (T * TT)) (p : path T) :=
  match p with
  | Pnil => Some Pnil
  | Px x tx p =>
    match read_fst ϕ tx with
    | Some tx =>
      match pmap_fst ϕ p with
      | Some p => Some (Px x tx p)
      | None => None
      end
    | None => None
    end
  | PM M p =>
    match pmap_fst ϕ p with
    | Some p => Some (PM M p)
    | None => None
    end
  | Pv v p =>
    match pmap_fst ϕ p with
    | Some p => Some (Pv v p)
    | None => None
    end
  end.

Fixpoint pmap_snd `{Eq T} `{Eq TT} (ϕ : list (T * TT)) (p : path TT) :=
  match p with
  | Pnil => Some Pnil
  | Px x tx p =>
    match read_snd ϕ tx with
    | Some tx =>
      match pmap_snd ϕ p with
      | Some p => Some (Px x tx p)
      | None => None
      end
    | None => None
    end
  | PM M p =>
    match pmap_snd ϕ p with
    | Some p => Some (PM M p)
    | None => None
    end
  | Pv v p =>
    match pmap_snd ϕ p with
    | Some p => Some (Pv v p)
    | None => None
    end
  end.

Lemma pmap_ϕ_bij `{Eq T} `{Eq TT} (ϕ : list (T * TT))
  (PRE : forall t t' (IN : In (t, t') ϕ),
    Some t' = read_fst ϕ t /\
    Some t = read_snd ϕ t') :
  forall p p',
    Some p' = pmap_fst ϕ p <-> Some p = pmap_snd ϕ p'.
Proof.
  assert (forall t t', In (t, t') ϕ <-> Some t' = read_fst ϕ t) as RR.
  { ii; split; ii. exploit PRE; ii; des; eauto. apply read_fst_in; assumption. }
  assert (forall t t', In (t, t') ϕ <-> Some t = read_snd ϕ t') as RR'.
  { ii; split; ii. exploit PRE; ii; des; eauto. apply read_snd_in; assumption. }
  clear PRE.
  induction p; ii; ss;
  destruct p'; split; ii; ss; repeat des_hyp; clarify;
  repeat des_goal; clarify;
  repeat match goal with
  | H : read_snd _ _ = _ |- _ => symmetry in H
  | H : read_fst _ _ = _ |- _ => symmetry in H
  | H : pmap_snd _ _ = _ |- _ => symmetry in H
  | H : pmap_fst _ _ = _ |- _ => symmetry in H
  end;
  try match goal with
  | H : Some _ = read_fst _ _ |- _ =>
    rewrite <- RR in H; rewrite RR' in *;
    rewrite <- H in *
  | H : Some _ = read_snd _ _ |- _ =>
    rewrite <- RR' in H; rewrite RR in *;
    rewrite <- H in *
  end; clarify;
  match goal with
  | H : _ = pmap_snd _ ?p |- _ =>
    first [
      rewrite <- IHp in H |
      assert (Some p = Some p) as RR'' by reflexivity;
      rewrite IHp in RR''; rewrite <- RR'' in *]; clarify
  end.
Qed.

Definition trans_iso_C_pre `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (α : T -> aT) (φ : aTT -> aT) (φ' : aT -> aTT) (ϕ : list (TT * T))
  (C' : dy_ctx TT) (Cout : dy_ctx T) (Cin : dy_ctx aT) :=
  iso (Ctx (trans_C α' C')) []
      (Ctx (trans_C α Cout +++ Cin)) [] 
      φ φ' /\
  (forall p (VALp : valid_path (Ctx Cout) [] p),
    match pmap_snd ϕ p with
    | Some p' => valid_path (Ctx C') [] p'
    | None => False
    end)
.

Definition trans_iso_C_post `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT)
  (φ : aTT -> aT) (φ' : aT -> aTT) (ϕ : list (TT * T)) (t : T)
  (C' : dy_ctx TT) (Cout : dy_ctx T) (Cin : dy_ctx aT) :=
  match trans_iso_C inv_α C' ϕ t Cout Cin with
  | Some (C, ϕ', t') =>
    (exists Cin', C = Cout +++ Cin') /\
    trans_C α Cout +++ Cin = trans_C α C /\
    (exists ϕ'', ϕ' = ϕ'' ++ ϕ /\
      forall t (IN : None <> read_fst ϕ'' t),
        reachable (Ctx C') [] t) /\
    ϕ_spec α' α φ φ' ϕ' t' /\
    (forall p (VALp : valid_path (Ctx C) [] p),
      match pmap_snd ϕ' p with
      | Some p' => valid_path (Ctx C') [] p'
      | None => False
      end) /\
    (forall p' (VALp' : valid_path (Ctx C') [] p'),
      match pmap_fst ϕ' p' with
      | Some p => valid_path (Ctx C) [] p
      | None => False
      end)
  | None => False
  end.

Definition trans_root {T aT} (α : T -> aT) (r : root T) :=
  match r with
  | Ctx C => Ctx (trans_C α C)
  | Ptr t => Ptr (α t)
  end.

Lemma avp_then_vp `{Eq T} `{Eq aT} (α : T -> aT) :
  forall p' r (VALp : valid_path (trans_root α r) [] p'),
  exists p, valid_path r [] p /\ p' = pmap α p.
Proof.
  induction p'; ii; ss; repeat des_hyp; des; clarify.
  - exists Pnil. ss.
  - destruct r; ss; clarify.
    rewrite trans_C_addr in *.
    des_hyp; clarify.
    exploit (IHp' (Ptr t)); eauto.
    ii; des.
    exists (Px x t p). ss. repeat rw. eauto.
  - destruct r; ss; clarify.
    rewrite trans_C_ctx_M in *.
    des_hyp; clarify.
    exploit (IHp' (Ctx d0)); eauto.
    ii; des.
    exists (PM M p). ss. repeat rw. eauto.
Qed.

Lemma vp_then_avp_empty `{Eq T} `{Eq aT} (α : T -> aT) :
  forall p r (VALp : valid_path r [] p),
  valid_path (trans_root α r) [] (pmap α p).
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify; ss.
  - rewrite trans_C_addr. rw.
    exploit IHp; eauto.
  - rewrite trans_C_ctx_M. rw.
    exploit IHp; eauto.
Qed.

Lemma vp_then_avp `{Eq T} `{Eq aT} (α : T -> aT) :
  forall p r m (VALp : valid_path r m p),
  avalid_path (trans_root α r) (trans_m α m) (pmap α p).
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify; ss.
  - rewrite trans_C_addr. rw.
    exploit IHp; eauto.
  - rewrite trans_C_ctx_M. rw.
    exploit IHp; eauto.
  - des_hyp; des; clarify.
    exists (Closure x e (trans_C α C)).
    rewrite trans_m_aread.
    split. exists t. exists (Closure x e C). eauto.
    split. eauto.
    exploit IHp; eauto.
Qed.

Lemma avp_unique `{Eq T} `{Eq aT} (α : T -> aT) :
  forall (p p' : path T) r (VALp : valid_path r [] p)
    (VALp' : valid_path r [] p')
    (EQ : pmap α p = pmap α p'),
  p = p'.
Proof.
  induction p; ii; destruct p';
  ss; repeat des_hyp; des; clarify;
  exploit IHp; eauto; ii; rw; exact eq_refl.
Qed.

Lemma pmap_fst_sound `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (α : T -> aT) (φ : aTT -> aT) (φ' : aT -> aTT) :
  forall p p'
    (ϕ : list (TT * T)) (t : T) (SPECϕ : ϕ_spec α' α φ φ' ϕ t)
    (TRANS : Some p = pmap_fst ϕ p'),
  pmap α' p' = pmap φ' (pmap α p).
Proof.
  induction p; ii; destruct p'; ss;
  repeat des_hyp; des; clarify;
  exploit IHp; eauto; ii; rrw; eauto.
  match goal with
  | H : read_fst _ _ = _ |- _ =>
    symmetry in H;
    apply read_fst_in in H as HH
  end.
  exploit SPECϕ; eauto.
  ii. des. rw. eauto.
Qed.

Lemma pmap_snd_sound `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (α : T -> aT) (φ : aTT -> aT) (φ' : aT -> aTT) :
  forall p p'
    (ϕ : list (TT * T)) (t : T) (SPECϕ : ϕ_spec α' α φ φ' ϕ t)
    (TRANS : Some p' = pmap_snd ϕ p),
  pmap α p = pmap φ (pmap α' p').
Proof.
  induction p; ii; destruct p'; ss;
  repeat des_hyp; des; clarify;
  exploit IHp; eauto; ii; rrw; eauto.
  match goal with
  | H : read_snd _ _ = _ |- _ =>
    symmetry in H;
    apply read_snd_in in H as HH
  end.
  exploit SPECϕ; eauto.
  ii. des. rrw. eauto.
Qed.

Lemma pmap_fst_app `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (α : T -> aT) (φ : aTT -> aT) (φ' : aT -> aTT) :
  forall p p'
    (ϕ ϕ' : list (TT * T)) (t t' : T)
    (SPECϕ : ϕ_spec α' α φ φ' ϕ t)
    (SPECϕ' : ϕ_spec α' α φ φ' (ϕ' ++ ϕ) t')
    (TRANS : pmap_fst ϕ p = Some p'),
  pmap_fst (ϕ' ++ ϕ) p = Some p'.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify;
  try match goal with
  | H : read_fst _ ?tx = Some ?t |- _ =>
    symmetry in H;
    apply read_fst_in in H as HH;
    exploit (SPECϕ' tx t); auto;
    try rewrite in_app_iff; auto;
    ii; des; rrw
  end;
  exploit IHp;
  first [exact SPECϕ | eauto];
  ii; rw; reflexivity.
Qed.

Lemma pmap_snd_app `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (α : T -> aT) (φ : aTT -> aT) (φ' : aT -> aTT) :
  forall p p'
    (ϕ ϕ' : list (TT * T)) (t t' : T)
    (SPECϕ : ϕ_spec α' α φ φ' ϕ t)
    (SPECϕ' : ϕ_spec α' α φ φ' (ϕ' ++ ϕ) t')
    (TRANS : pmap_snd ϕ p = Some p'),
  pmap_snd (ϕ' ++ ϕ) p = Some p'.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify;
  try match goal with
  | H : read_snd _ ?tx = Some ?t |- _ =>
    symmetry in H;
    apply read_snd_in in H as HH;
    exploit (SPECϕ' t tx); auto;
    try rewrite in_app_iff; auto;
    ii; des; rrw
  end;
  exploit IHp;
  first [exact SPECϕ | eauto];
  ii; rw; reflexivity.
Qed.

Lemma trans_iso_C_pre_post `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT) 
  (SPECα : inv_α_spec α inv_α) (φ : aTT -> aT) (φ' : aT -> aTT) :
  forall (Cin : dy_ctx aT) (Cout : dy_ctx T) (C' : dy_ctx TT)
    (ϕ : list (TT * T)) (t : T)
    (SPECϕ : ϕ_spec α' α φ φ' ϕ t)
    (PRE : trans_iso_C_pre α' α φ φ' ϕ C' Cout Cin),
    trans_iso_C_post α' inv_α α φ φ' ϕ t C' Cout Cin.
Proof.
  induction Cin; ii;
  unfold trans_iso_C_pre in *;
  unfold trans_iso_C_post in *;
  ss; des.
  - rewrite capp_nil_r in *.
    split. exists ([||]). rewrite capp_nil_r. eauto.
    split. eauto.
    split. exists []. split; eauto. ii; contradict.
    split. eauto.
    split. eauto.
    destruct PRE as [PRE PRE'].
    ii. specialize (PRE (pmap α' p')).
    exploit PRE. apply (vp_then_avp_empty α' p' (Ctx C')). eauto.
    ii; ss; des.
    match goal with H : _ |- _ =>
      apply (avp_then_vp α _ (Ctx Cout)) in H;
      destruct H as [p'' [? RR]]
    end. rewrite RR in *.
    exploit PRE0; eauto. ii; des_hyp; clarify.
    symmetry in HDES.
    rewrite <- pmap_ϕ_bij in *.
    assert (pmap α' p = pmap α' p').
    { rrw. eapply pmap_fst_sound; eauto. }
    assert (p = p').
    { eapply (@avp_unique TT _ aTT _); eauto. }
    clarify. rrw. eauto.
    ii. exploit SPECϕ; eauto. ii; des; eauto.
  - des_goal.
    all:cycle 1.
    (* Contradictory *)
    des_hyp.
    (* shadowed *)
    exploit (IHCin (Cout +++ dy_binde x (inv_α (t, tx)) ([||])) C' _ _ _); eauto.
    rewrite trans_C_app. ss.
    destruct (SPECα t tx). rrw.
    rewrite <- capp_assoc. ss. split. eauto.
    ii. apply PRE0.
    destruct p; ss;
    first [rewrite capp_addr_x in *
    | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify;
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto.
    (* not shadowed *)
    destruct PRE as [PRE' PRE].
    specialize (PRE (Px x tx Pnil)) as HINT.
    exploit HINT; ss.
    rewrite capp_addr_x.
    rewrite trans_C_addr. rw. ss.
    rewrite ID_refl. eauto.
    rewrite trans_C_addr. clear HINT.
    ii; des_hyp; des; clarify.
    des_hyp; clarify.
    des_hyp;
    match goal with
    | _ : context [(?t', inv_α (?t, ?tx))],
      _ : read_fst _ _ = None |- _ =>
      assert (ϕ_spec α' α φ φ' ((t', inv_α (t, tx)) :: ϕ) (inv_α (t, tx))) as SPECϕ'
    | _ => idtac
    end;
    match goal with
    | |- ϕ_spec _ _ _ _ _ _ => idtac
    | H : trans_iso_C _ ?C' ?phi ?t ?Cout _ = None |- _ =>
      exploit (IHCin Cout C' phi t);
      first [rw; eauto | assumption | idtac]
    end;
    try rewrite trans_C_app; s;
    try rewrite <- capp_assoc; s.
    (* addr is already inside ϕ *)
    assert (α t1 = φ (α' t0)).
    {
      symmetry in HDES0.
      apply read_fst_in in HDES0.
      exploit SPECϕ; eauto. ii; des. eauto.
    }
    rw. rw. rw. 
    split. split; eauto.
    ii. destruct p; ss;
    first [rewrite capp_addr_x in *
      | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify.
    exploit (PRE0 (Px x0 t2 p)). ss. rw. eauto.
    ii. ss.
    rewrite eqb_ID_eq in *; clarify.
    symmetry in HDES0. apply read_fst_in in HDES0 as HH.
    exploit SPECϕ; eauto.
    ii; des. rrw.
    destruct p; ss; des; clarify. rw. eauto.
    exploit (PRE0 (PM M p)); ss; rw; eauto.
    (* proof of ϕ_spec *)
    ii. ss. des; clarify.
    repeat rewrite t_refl.
    repeat split; eauto using leb_refl.
    destruct (SPECα t tx). rrw. rw. eauto.
    destruct (SPECα t tx). rrw. eauto.
    assert (eqb t'' t0 = false).
    {
      refl_bool. i. rewrite eqb_eq in *. clarify.
      exploit SPECϕ; eauto. ii. des. rewrite HDES0 in *.
      clarify.
    }
    assert (eqb t' (inv_α (t, tx)) = false).
    {
      refl_bool. i. rewrite eqb_eq in *. clarify.
      exploit SPECϕ; eauto. ii. des.
      destruct (SPECα t tx) as [LT RR].
      rewrite <- RR in *.
      destruct LT as [LE NEQ].
      rewrite eqb_neq in *. apply NEQ.
      apply leb_sym; eauto.
    }
    rw. rw. exploit SPECϕ; eauto.
    ii; des. repeat (split; try assumption).
    destruct (SPECα t tx) as [[? ?] ?]. lebt t.
    destruct (SPECα t tx). rrw.
    (* iso again *)
    split. split; eauto.
    ii. destruct p; simpl in VALp;
    first [rewrite capp_addr_x in *
      | rewrite capp_ctx_M in * | idtac];
    repeat des_hyp; des; clarify;
    match goal with
    | _ =>
      s; rewrite t_refl; rewrite eqb_ID_eq in *;
      destruct p; ss; des; clarify; rw; eauto
    | |- context [pmap_snd _ ?p] =>
      exploit (PRE0 p); first [ss; rw; eauto | idtac];
      ii; des_hyp; clarify;
      match goal with
      | |- context [?a :: ?l] =>
        replace (a :: l) with ([a] ++ l) by reflexivity
      end;
      erewrite (@pmap_snd_app TT _ aTT _ T _ _ aT _);
      eauto; first [exact SPECϕ | exact SPECϕ']
    end.
    (* now the non-contradictory cases *)
    des_hyp.
    (* shadowed *)
    exploit (IHCin (Cout +++ dy_binde x (inv_α (t, tx)) ([||])) C' _ _ _); eauto.
    rewrite trans_C_app. ss.
    destruct (SPECα t tx). rrw.
    rewrite <- capp_assoc. ss. split. eauto.
    ii. apply PRE0.
    destruct p0; ss;
    first [rewrite capp_addr_x in *
    | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify;
    rewrite eqb_ID_eq in *; clarify.
    rw. ii. repeat des_hyp; des; clarify.
    rewrite trans_C_app in *. ss.
    rewrite <- capp_assoc in *. ss.
    split. exists (dy_binde x (inv_α (t, tx)) Cin'). eauto.
    split. rewrite trans_C_app in *. ss.
    destruct (SPECα t tx). rewrite <- H5 in *.
    rewrite <- capp_assoc in *. ss.
    split. exists ϕ''. eauto. eauto.
    (* not shadowed *)
    des_hyp; clarify.
    destruct PRE as [PRE' PRE].
    specialize (PRE (Px x tx Pnil)) as HINT.
    exploit HINT; ss.
    rewrite capp_addr_x.
    rewrite trans_C_addr. rw. s.
    rewrite ID_refl. eauto. clear HINT.
    rewrite trans_C_addr. rw.
    ii. des; clarify.
    des_hyp;
    match goal with
    | _ : read_fst _ _ = None |- _ =>
      assert (ϕ_spec α' α φ φ' ((t0, inv_α (t, tx)) :: ϕ) (inv_α (t, tx))) as SPECϕ'
    | _ => idtac
    end;
    match goal with
    | |- ϕ_spec _ _ _ _ _ _ => idtac
    | H : trans_iso_C _ ?C' ?phi ?t ?Cout _ = _ |- _ =>
      exploit (IHCin Cout C' phi t);
      first [rw; eauto | assumption | idtac]
    end;
    try rewrite trans_C_app; s;
    try rewrite <- capp_assoc; s.
    (* in ϕ *)
    assert (α t1 = φ (α' t0)).
    {
      symmetry in HDES1.
      apply read_fst_in in HDES1.
      exploit SPECϕ; eauto. ii; des. eauto.
    }
    rw. rewrite <- x1. rw. 
    split. split; eauto.
    ii. destruct p0; ss;
    first [rewrite capp_addr_x in *
      | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify.
    exploit (PRE0 (Px x0 t2 p0)). ss. rw. eauto.
    ii. ss.
    rewrite eqb_ID_eq in *; clarify.
    symmetry in HDES1. apply read_fst_in in HDES1 as HH.
    exploit SPECϕ; eauto.
    ii; des. rrw.
    destruct p0; ss; des; clarify. rw. eauto.
    exploit (PRE0 (PM M p0)); ss; rw; eauto.
    all:cycle 1.
    (* prove ϕ_spec *)
    ii. ss. des; clarify.
    repeat rewrite t_refl.
    repeat split; eauto using leb_refl.
    destruct (SPECα t tx). rrw. rrw. eauto.
    destruct (SPECα t tx). rrw. eauto.
    assert (eqb t'' t0 = false).
    {
      refl_bool. i. rewrite eqb_eq in *. clarify.
      exploit SPECϕ; eauto. ii. des. rewrite HDES1 in *.
      clarify.
    }
    assert (eqb t' (inv_α (t, tx)) = false).
    {
      refl_bool. i. rewrite eqb_eq in *. clarify.
      exploit SPECϕ; eauto. ii. des.
      destruct (SPECα t tx) as [LT RR].
      rewrite <- RR in *.
      destruct LT as [LE NEQ].
      rewrite eqb_neq in *. apply NEQ.
      apply leb_sym; eauto.
    }
    rw. rw. exploit SPECϕ; eauto.
    ii; des. repeat (split; try assumption).
    destruct (SPECα t tx) as [[? ?] ?]. lebt t.
    (* iso when not in ϕ *)
    destruct (SPECα t tx). rrw.
    split. split; eauto.
    ii. destruct p0; simpl in VALp;
    first [rewrite capp_addr_x in *
      | rewrite capp_ctx_M in * | idtac];
    repeat des_hyp; des; clarify;
    match goal with
    | _ =>
      s; rewrite t_refl; rewrite eqb_ID_eq in *;
      destruct p0; ss; des; clarify; rw; eauto
    | |- context [pmap_snd _ ?p] =>
      exploit (PRE0 p); first [ss; rw; eauto | idtac];
      ii; des_hyp; clarify;
      match goal with
      | |- context [?a :: ?l] =>
        replace (a :: l) with ([a] ++ l) by reflexivity
      end;
      erewrite (@pmap_snd_app TT _ aTT _ T _ _ aT _);
      eauto; first [exact SPECϕ | exact SPECϕ']
    end.
    (* main proofs *)
    + ii. repeat des_hyp; des; clarify.
      repeat rewrite trans_C_app in *.
      repeat rewrite <- capp_assoc in *. ss.
      split. eauto.
      split. destruct (SPECα t tx) as [? RR]. rewrite <- RR in *. eauto.
      split. exists (ϕ'' ++ [(t0, inv_α (t, tx))]).
      rewrite <- app_assoc. s. split; eauto.
      ii. rewrite read_fst_top in *. ss.
      repeat des_hyp; clarify.
      match goal with H : _ |- _ => apply H; rw; eauto end.
      rewrite eqb_eq in *. clarify.
      exists (Px x t0 Pnil). ss. rw. eauto.
      eauto.
    + ii. repeat des_hyp; des; clarify.
      repeat rewrite trans_C_app in *.
      repeat rewrite <- capp_assoc in *. ss.
      split. eauto.
      split.
      assert (φ (α' t0) = α t1).
      {
        symmetry in HDES1.
        apply read_fst_in in HDES1.
        exploit SPECϕ; eauto. ii; des. eauto.
      }
      assert (tx = α t1).
      { rrw. rrw. rw. reflexivity. }
      rw. eauto.
      split; eauto.
  - des_goal.
    all:cycle 1.
    (* Contradictory *)
    des_hyp.
    (* shadowed *)
    exploit (IHCin2 (Cout +++ dy_bindm M (lift_C inv_α t Cin1) ([||])) C' _ _ _); eauto.
    rewrite trans_C_app. ss.
    rewrite lift_C_lower; eauto.
    rewrite <- capp_assoc. ss. split. eauto.
    ii. apply PRE0.
    destruct p; ss;
    first [rewrite capp_addr_x in *
    | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify;
    rewrite eqb_ID_eq in *; clarify.
    rw. eauto.
    (* not shadowed *)
    destruct PRE as [PRE' PRE].
    specialize (PRE (PM M Pnil)) as HINT.
    exploit HINT; ss.
    rewrite capp_ctx_M.
    rewrite trans_C_ctx_M. rw. ss.
    rewrite ID_refl. eauto.
    rewrite trans_C_ctx_M. clear HINT.
    ii; des_hyp; des; clarify.
    des_hyp; clarify.
    repeat des_hyp; clarify;
    match goal with
    | IHC : context [match trans_iso_C _ _ _ _ _ ?Cin with _ => _ end],
      _ : trans_iso_C _ ?C' ?phi ?t ?Cout ?Cin = None |- _ =>
      match goal with
      | IHC : context [match trans_iso_C _ _ _ _ _ ?Cin with _ => _ end],
        _ : trans_iso_C _ ?C' ?phi ?t ?Cout ?Cin = Some _ |- _ =>
        exploit (IHC Cout C' phi t);
        first [rw; eauto | assumption | idtac]
      | _ =>
        exploit (IHC Cout C' phi t);
        first [rw; eauto | assumption | idtac]
      end
    end;
    try match goal with
    | |- context [iso] =>
      s; split; try solve [ii; destruct p; ss];
      split; ii;
      match goal with
      | _ =>
        exploit (PRE' (PM M p)); s;
        first [solve [rewrite trans_C_ctx_M; rw; eauto] |
          rewrite capp_ctx_M; rewrite trans_C_ctx_M;
          rw; s; rewrite ID_refl; subst p']
      | _ =>
        exploit (PRE (PM M p')); s;
        first [solve [rewrite capp_ctx_M; rewrite trans_C_ctx_M;
          rw; s; rewrite ID_refl; eauto] |
          rewrite trans_C_ctx_M; rw; subst p]
      end
    end; ii; des; clarify.
    ss.
    match goal with
    | IHC : context [match trans_iso_C _ _ _ _ _ ?Cin with _ => _ end],
      _ : trans_iso_C _ ?C' ?phi ?t ?Cout ?Cin = None |- _ =>
      exploit (IHC Cout C' phi t);
      first [rw; eauto | assumption | idtac]
    end. clear IHCin1 IHCin2.
    rewrite trans_C_app. s. rrw.
    rewrite <- capp_assoc. s.
    split. split; assumption.
    ii. destruct p; ss;
    first [rewrite capp_addr_x in *
      | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify.
    exploit (PRE0 (Px x t1 p)). s. rw. eauto.
    ii. repeat des_hyp; clarify.
    eapply (@pmap_snd_app TT _ aTT) with (ϕ' := ϕ'') in HDES2 as RR; eauto.
    clear HDES2. ss. rw. eauto.
    exploit (PRE0 (PM M0 p)). s. rw. eauto.
    ii. repeat des_hyp; clarify.
    eapply (@pmap_snd_app TT _ aTT) in HDES2 as RR; eauto.
    clear HDES2. ss. rw. eauto.
    rewrite eqb_ID_eq in *; clarify.
    exploit x6; eauto. ii.
    des_hyp; clarify. s. rw. eauto.
    (* now the non-contradictory cases *)
    des_hyp.
    (* shadowed *)
    match goal with
    | IHC : context [match trans_iso_C _ _ _ _ _ ?Cin with _ => _ end],
      _ : trans_iso_C _ ?C' ?phi ?t ?Cout ?Cin = Some _ |- _ =>
      exploit (IHC Cout C' phi t); 
      first [rw | assumption | idtac]
    end;
    ii; repeat des_hyp; des; clarify;
    repeat rewrite trans_C_app in *; ss;
    rewrite lift_C_lower in *; eauto;
    repeat rewrite <- capp_assoc in *; ss.
    split. assumption.
    ii. apply PRE0.
    destruct p0; ss;
    first [rewrite capp_addr_x in *
      | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify.
    rewrite eqb_ID_eq in *; clarify.
    repeat (split; eauto).
    (* not shadowed *)
    destruct PRE as [PRE' PRE].
    specialize (PRE (PM M Pnil)) as HINT.
    exploit HINT; ss.
    rewrite capp_ctx_M.
    rewrite trans_C_ctx_M. rw. ss.
    rewrite ID_refl. eauto.
    rewrite trans_C_ctx_M. clear HINT.
    ii; des_hyp; des; clarify.
    des_hyp; clarify.
    repeat des_hyp; clarify.
    exploit (IHCin1 ([||]) d0 ϕ t); eauto; clear IHCin1.
    match goal with
    | |- context [iso] =>
      s; split; try solve [ii; destruct p0; ss];
      split; ii;
      match goal with
      | p : path aTT |- _ =>
        exploit (PRE' (PM M p)); s;
        first [solve [rewrite trans_C_ctx_M; rw; eauto] |
          rewrite capp_ctx_M; rewrite trans_C_ctx_M;
          rw; s; rewrite ID_refl]
      | p' : path aT |- _ =>
        exploit (PRE (PM M p')); s;
        first [solve [rewrite capp_ctx_M; rewrite trans_C_ctx_M;
          rw; s; rewrite ID_refl; eauto] |
          rewrite trans_C_ctx_M; rw]
      end
    end; ii; des; clarify.
    rw. ii. des. clarify.
    match goal with
    | IHC : context [match trans_iso_C _ _ _ _ _ ?Cin with _ => _ end],
      _ : trans_iso_C _ ?C' ?phi ?t ?Cout ?Cin = Some _ |- _ =>
      exploit (IHC Cout C' phi t); 
      first [rw | assumption | idtac]
    end;
    ii; repeat des_hyp; des; clarify;
    repeat rewrite trans_C_app in *; ss;
    repeat rewrite <- capp_assoc in *; ss; repeat rrw.
    split. split; eauto.
    ii. destruct p0; ss;
    first [rewrite capp_addr_x in *
      | rewrite capp_ctx_M in *];
    repeat des_hyp; des; clarify.
    exploit (PRE0 (Px x t1 p0)). s. rw. eauto.
    ii. repeat des_hyp; clarify.
    eapply (@pmap_snd_app TT _ aTT) with (ϕ' := ϕ'') in HDES2 as RR; eauto.
    clear HDES2. ss. rw. eauto.
    exploit (PRE0 (PM M0 p0)). s. rw. eauto.
    ii. repeat des_hyp; clarify.
    eapply (@pmap_snd_app TT _ aTT) in HDES2 as RR; eauto.
    clear HDES2. ss. rw. eauto.
    rewrite eqb_ID_eq in *; clarify.
    exploit x6; eauto. ii.
    des_hyp; clarify. s. rw. eauto.
    (* finish off *)
    repeat (split; eauto).
    rewrite app_assoc. eexists. split. reflexivity.
    ii. rewrite read_fst_top in *.
    repeat des_hyp. 
    match goal with H : _ |- _ => apply H; rw; eauto end.
    assert (reachable (Ctx d0) [] t2) as HINT. eauto.
    unfold reachable in HINT. des.
    exists (PM M p). s. rw. eauto.
Qed.

Fixpoint find_iso `{Eq aTT} `{Eq aT}
  (v : expr_value aTT) (vl : list (expr_value aT)) φ φ' :=
  match vl with
  | [] => None
  | v' :: vl' =>
    match v, v' with
    | Closure x e C, Closure x' e' C' =>
      if eqb_ID x x' && eq_tm e e' && iso_C C C' φ φ'
      then Some v'
      else find_iso v vl' φ φ'
    end
  end.

Fixpoint remove_t `{Eq T} (m : memory T) t :=
  match m with
  | [] => []
  | (t', v) :: tl =>
    let tl := remove_t tl t in
    if eqb t t' then tl else (t', v) :: tl
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

Lemma vpath_less_then_vpath_more `{Eq T} :
  forall a b p r (VAL : valid_path r a p),
  valid_path r (a ++ b) p.
Proof.
  ii.
  ginduction p; ii; ss;
  repeat des_hyp; des; clarify; eauto.
  des_hyp; des; clarify.
  exists (Closure x e C).
  rewrite read_top. rewrite <- VAL. eauto.
Qed.

Fixpoint plen {T} (p : path T) :=
  match p with
  | Pnil => 0
  | PM _ p
  | Pv _ p
  | Px _ _ p => S (plen p)
  end.

Lemma separate_vpath `{Eq T} :
  forall n p C m t tr
    (LE : plen p <= n)
    (VAL : valid_path (Ctx C) m p)
    (NIN : ~ Inp tr p)
    (IN : Inp t p),
  exists p' t',
    valid_path (Ctx C) [] p' /\
    ~ Inp tr p' /\
    Inp t' p' /\
    (t' = t \/
    exists p'', 
      ~ Inp tr p'' /\ valid_path (Ptr t') m p'' /\ Inp t p'' /\
      plen p' + plen p'' <= n).
Proof.
  induction n; ii; ss.
  destruct p; ss; nia.
  destruct p; ss; repeat des_hyp; des; clarify.
  - exists (Px x t0 Pnil). exists t0.
    s. rw. repeat (split; eauto).
    red; ii; des; clarify. apply NIN. eauto.
  - exists (Px x t0 Pnil). exists t0.
    s. rw. repeat (split; eauto).
    red; ii; des; clarify. apply NIN. eauto.
    right. exists p. repeat (split; eauto).
  - exploit IHn; eauto. nia.
    ii; des; clarify.
    exists (PM M p'). exists t. s. rw. eauto.
    exists (PM M p'). exists t'. s. rw.
    repeat (split; eauto).
    right. exists p''. repeat (split; eauto).
    nia.
Qed.

Lemma reachable_remove_aux `{Eq T} :
  forall n p r m tr (* time to be removed *) t
    (LE : plen p <= n)
    (VAL : valid_path r m p)
    (IN : Inp t p)
    (NEQ : t <> tr),
  (exists p', ~ Inp tr p' /\ valid_path r m p' /\ Inp t p' /\ plen p' <= n) \/
  match read m tr with
  | Some (Closure _ _ C) =>
    exists p' t',
      valid_path (Ctx C) [] p' /\
      Inp t' p' /\
      ~ Inp tr p' /\
      (t' = t \/
      exists p'',
        ~ Inp tr p'' /\ valid_path (Ptr t') m p'' /\ Inp t p'' /\
        plen p' + plen p'' <= n)
  | None => False
  end.
Proof.
  induction n.
  ii. destruct p; ss; nia.
  ii. destruct p; ss; repeat des_hyp; des; clarify.
  - left. exists (Px x t0 Pnil). s. rw.
    repeat (split; eauto). red; ii; des; clarify.
    nia.
  - destruct (eqb t0 tr) eqn:CASE.
    rewrite eqb_eq in *. clarify.
    destruct p; ss. des. des_hyp. des. clarify.
    rrw. right.
    exploit IHn; eauto. nia. rrw.
    ii; des; clarify.
    exploit separate_vpath; eauto.
    ii; des; clarify.
    eexists. eexists. eauto.
    eexists. eexists. repeat (split; eauto).
    right. exists p''. eauto.
    exists p'. exists t. eauto.
    exists p'. exists t'. repeat split; eauto.
    right. exists p''. eauto.
    rewrite eqb_neq in *.
    exploit IHn; eauto. nia. ii. des; eauto.
    left. exists (Px x t0 p').
    s. rw. repeat (split; eauto).
    red; ii; des; clarify. nia. right.
    repeat des_hyp; des; clarify.
    exists p'. exists t. eauto.
    exists p'. exists t'. repeat split; eauto.
    right. exists p''. eauto.
  - exploit IHn; eauto. nia.
    ii. des; eauto.
    left. exists (PM M p'). s. rw. repeat (split; eauto). nia.
    repeat des_hyp; des; clarify.
    right. exists p'. exists t. eauto.
    right. exists p'. exists t'. repeat (split; eauto).
    right. exists p''. eauto.
  - des_hyp; des; clarify.
    destruct (eqb t0 tr) eqn:CASE.
    rewrite eqb_eq in *. clarify.
    rrw. right.
    exploit IHn; eauto. nia.
    ii. des; clarify.
    exploit separate_vpath; eauto.
    ii. des; clarify.
    eexists. eexists. eauto.
    eexists. eexists. repeat (split; eauto).
    right. exists p''. eauto.
    rewrite <- VAL in *. des; clarify.
    exists p'. exists t. eauto.
    exists p'. exists t'. repeat (split; eauto).
    right. exists p''. eauto.
    rewrite eqb_neq in *.
    exploit IHn; eauto. nia.
    ii. des; clarify.
    left. exists (Pv (v_fn x e) p').
    s. repeat (split; eauto).
    exists (Closure x e C). eauto.
    nia.
    repeat des_hyp; des; clarify.
    right. exists p'. exists t. eauto.
    right. exists p'. exists t'. repeat (split; eauto).
    right. exists p''. eauto.
Qed.

Lemma reachable_remove `{Eq T} :
  forall r m tr (* time to be removed *) t
    (REACH : reachable r m t)
    (NEQ : t <> tr),
  (exists p', ~ Inp tr p' /\ valid_path r m p' /\ Inp t p') \/
  match read m tr with
  | Some (Closure _ _ C) =>
    exists p' t',
      valid_path (Ctx C) [] p' /\
      Inp t' p' /\
      ~ Inp tr p' /\
      (t' = t \/
      exists p'',
        ~ Inp tr p'' /\ valid_path (Ptr t') m p'' /\ Inp t p'')
  | None => False
  end.
Proof.
  ii. unfold reachable in REACH. des.
  exploit reachable_remove_aux; eauto.
  ii; des. eauto.
  right. repeat des_hyp; des; clarify; eauto 10.
Qed.

Inductive trans_res T TT :=
  | Unchanged
  | Changed (t : T) (v : expr_value T)
            (t' : TT) (v' : expr_value TT) 
            (ϕ : list (T * TT)) (tϕ : TT)
  | Failed
.

Arguments Unchanged {T TT}.
Arguments Changed {T TT}.
Arguments Failed {T TT}.

Fixpoint trans_m_step `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) φ φ'
  (ϕ : list (TT * T)) (tϕ : T)
  (m : memory aT) (m' : memory TT) :=
  match m' with
  | [] => Unchanged
  | (t', v') :: tl' =>
    match read_fst ϕ t' with
    | None => trans_m_step α' inv_α φ φ' ϕ tϕ m tl'
    | Some t =>
      match v' with
      | Closure x' e' C' =>
      match find_iso (trans_v α' v') (aread m (φ (α' t'))) φ φ' with
      | None => Failed
      | Some (Closure x e C) =>
        match trans_iso_C inv_α C' ϕ tϕ ([||]) C with
        | None => Failed
        | Some (C, ϕ, tϕ) =>
          Changed t' v' t (Closure x e C) ϕ tϕ
        end
      end end
    end
  end.

Definition trans_m_step_pre `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) φ φ' 
  (ϕ : list (TT * T)) (m : memory aT) (m' : memory TT) :=
  forall t' (IN : None <> read_fst ϕ t'),
    match read m' t' with
    | None => True
    | Some v' =>
      exists v, In v (aread m (φ (α' t'))) /\
      match (trans_v α' v'), v with
      | Closure x' e' C', Closure x e C =>
        x' = x /\ e' = e /\
        iso (Ctx C') [] (Ctx C) [] φ φ'
      end
    end.

Definition trans_m_step_post `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT) φ φ'
  (ϕ : list (TT * T)) (tϕ : T)
  (m : memory aT) (m' : memory TT) :=
  match trans_m_step α' inv_α φ φ' ϕ tϕ m m' with
  | Unchanged =>
    forall t' (IN : None <> read_fst ϕ t'),
      None = read m' t'
  | Changed t' (Closure x' e' C') t (Closure x e C) ϕ_af tϕ_af =>
    None <> read_fst ϕ t' /\ x' = x /\ e' = e /\
    Some (Closure x' e' C') = read m' t' /\
    In (Closure x e (trans_C α C)) (aread m (α t)) /\
    ϕ_spec α' α φ φ' ϕ_af tϕ_af /\
    (exists ϕ', ϕ_af = ϕ' ++ ϕ /\
      forall t' (IN : None <> read_fst ϕ' t'),
        reachable (Ctx C') [] t') /\
    (forall p (VALp : valid_path (Ctx C) [] p),
      match pmap_snd ϕ_af p with
      | Some p' => valid_path (Ctx C') [] p'
      | None => False
      end) /\
    (forall p' (VALp' : valid_path (Ctx C') [] p'),
      match pmap_fst ϕ_af p' with
      | Some p => valid_path (Ctx C) [] p
      | None => False
      end)
  | Failed => False
  end.

Lemma find_iso_spec `{Eq aTT} `{Eq aT} φ φ' :
  forall (vl : list (expr_value aT)) (v' : expr_value aTT)
  (PRE : exists v, In v vl /\
    match v', v with
    | Closure x' e' C', Closure x e C =>
      x' = x /\ e' = e /\
      iso (Ctx C') [] (Ctx C) [] φ φ'
    end),
  exists v, Some v = find_iso v' vl φ φ' /\
    In v vl /\
    match v', v with
    | Closure x' e' C', Closure x e C =>
      x' = x /\ e' = e /\
      iso (Ctx C') [] (Ctx C) [] φ φ'
    end.
Proof.
  induction vl; ii; des; repeat des_hyp; clarify.
  ss; des; clarify.
  - rewrite <- check_iso_iso in *. rw.
    rewrite ID_refl. assert (eq_tm = eqb) as RR. eauto.
    rewrite RR. rewrite t_refl. s.
    eexists. split. reflexivity.
    rewrite check_iso_iso in *.
    eauto.
  - repeat des_goal; repeat des_hyp.
    rewrite eqb_ID_eq in *;
    rewrite eq_tm_eq in *;
    rewrite check_iso_iso in *; clarify.
    eexists. split. reflexivity. s. eauto.
    all:(exploit IHvl);
    first [solve[
      eexists; split; eauto;
      instantiate (1 := Closure x0 e0 C); s; eauto] |
      ii; des; eauto].
Qed.

Definition reachϕ `{Eq T} `{Eq TT} (ϕ : list (T * TT)) (m : memory T) t :=
  None <> read_fst ϕ t \/
  exists t', None <> read_fst ϕ t' /\ reachable (Ptr t') m t.

Lemma trans_m_step_pre_post `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT) 
  (SPECα : inv_α_spec α inv_α) φ φ' :
  forall (m' : memory TT) (m : memory aT)
    (ϕ : list (TT * T)) (tϕ : T)
    (SPECϕ : ϕ_spec α' α φ φ' ϕ tϕ)
    (PRE : trans_m_step_pre α' φ φ' ϕ m m'),
  trans_m_step_post α' inv_α α φ φ' ϕ tϕ m m'.
Proof.
  induction m'; ii; ss.
  destruct a as [t' v'].
  destruct (read_fst ϕ t') eqn:CASE;
  red; s; rw.
  - exploit (PRE t'). rw. ii; clarify.
    s. rewrite t_refl. intros [v [INv ISOv]].
    exploit (find_iso_spec φ φ' (aread m (φ (α' t'))) (trans_v α' v')); eauto.
    intros [v'' [RR ISOv'']]. rrw. clear RR.
    destruct v' as [x' e' C'].
    destruct v'' as [x'' e'' C''].
    ss; repeat des_hyp; des; clarify.
    exploit (trans_iso_C_pre_post α' inv_α α SPECα φ φ' C'' ([||]) C' ϕ tϕ SPECϕ).
    split. s. eauto.
    ii; ss. destruct p; ss.
    intros POST. unfold trans_iso_C_post in POST.
    repeat des_hyp; clarify.
    rewrite t_refl. des; clarify.
    repeat (split; eauto). rw. ii. clarify.
    exploit (SPECϕ t' t).
    symmetry in CASE. apply read_fst_in in CASE. eauto.
    ii. des. rw. eauto.
  - assert (trans_m_step_pre α' φ φ' ϕ m m') as PRE'.
    {
      ii. exploit PRE; eauto.
      s. des_goal; des_hyp.
      rewrite eqb_eq in *. clarify. contradict.
      rw. eauto. rw. eauto.
    }
    exploit IHm'; eauto.
    intros POST. unfold trans_m_step_post in POST.
    des_hyp; clarify.
    ii. des_goal; eauto.
    rewrite eqb_eq in *. clarify. contradict.
    repeat des_hyp; des; clarify.
    assert (eqb t' t = false).
    {
      rewrite eqb_neq. ii. clarify. eauto.
    }
    rw. repeat (split; eauto).
Qed.

Lemma reachable_disj `{Eq T} :
  forall r m m' t (REACH : reachable r m t)
    (DISJ : forall t (READ : None <> read m t), None = read m' t),
  reachable r (m' ++ m) t.
Proof.
  ii. destruct REACH as [p [VALp INp]].
  ginduction p; ii; ss;
  repeat des_hyp; des; clarify.
  - exists (Px x t0 Pnil). s. rw. eauto.
  - exploit IHp; eauto. intros [p' [VALp' INp']].
    exists (Px x t0 p'). s. rw. eauto.
  - exploit IHp; eauto. intros [p' [VALp' INp']].
    exists (PM M p'). s. rw. eauto.
  - des_hyp; des; clarify.
    exploit IHp; eauto. intros [p' [VALp' INp']].
    exists (Pv (v_fn x e) p').
    s. split; eauto. exists (Closure x e C).
    rewrite read_top.
    exploit (DISJ t0). rrw; ii; clarify.
    ii. rrw. eauto.
Qed.

Lemma paste_vpath `{Eq T} :
  forall r m t t' (REACH : reachable r m t)
    (REACH' : reachable (Ptr t) m t'),
  reachable r m t'.
Proof.
  ii. destruct REACH as [p [VALp INp]].
  ginduction p; ii; ss;
  repeat des_hyp; des; clarify.
  - destruct REACH' as [p' [VALp' INp']].
    exists (Px x t0 p'). s. rw. eauto.
  - exploit IHp; eauto. intros [p' [VALp' INp']].
    exists (Px x t0 p'). s. rw. eauto.
  - exploit IHp; eauto. intros [p' [VALp' INp']].
    exists (PM M p'). s. rw. eauto.
  - des_hyp; des; clarify.
    exploit IHp; eauto. intros [p' [VALp' INp']].
    exists (Pv (v_fn x e) p'). s. split; eauto.
    exists (Closure x e C). eauto.
Qed.

Lemma tail_vpath `{Eq T} :
  forall r m t (REACH : reachable r m t),
    reachable r [] t \/
    exists t' x e C,
      (r = Ptr t' \/ reachable r m t') /\
      Some (Closure x e C) = read m t' /\
      reachable (Ctx C) [] t.
Proof.
  intros. destruct REACH as [p [VALp INp]].
  ginduction p; ii; ss;
  repeat des_hyp; des; clarify.
  - left. exists (Px x t0 Pnil). s. rw. eauto.
  - exploit IHp; eauto.
    intros REACH'; des.
    destruct REACH' as [p' [? ?]].
    destruct p'; ss; des; clarify.
    clarify.
    right. exists t'. exists x0. exists e. exists C0.
    repeat (split; try assumption). right.
    exists (Px x t' Pnil). s. rw. eauto.
    right. exists t'. exists x0. exists e. exists C0.
    repeat (split; try assumption). right.
    eapply paste_vpath; eauto.
    exists (Px x t0 Pnil). s. rw. eauto.
  - exploit IHp; eauto.
    intros REACH'; des; clarify;
    destruct REACH' as [p' [? ?]].
    left. exists (PM M p'). s. rw. eauto.
    right. exists t'. exists x. exists e. exists C0.
    repeat (split; try assumption). right.
    exists (PM M p'). s. rw. eauto.
  - des_hyp; des; clarify. right.
    exploit IHp; eauto.
    intros REACH'; des; clarify;
    destruct REACH' as [p' [? ?]].
    exists t0. exists x. exists e. exists C.
    repeat (split; eauto). exists p'. eauto.
    exists t'. exists x0. exists e0. exists C0.
    repeat (split; try assumption). right.
    exists (Pv (v_fn x e) p').
    s. split; eauto.
    exists (Closure x e C). eauto.
Qed.

Lemma vpath_root_bound `{TotalOrder T} :
  forall p r m m' t
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQm : forall t', leb t' t = true -> read m t' = read m' t'),
  valid_path r m p <-> valid_path r m' p.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify.
  - des_goal; eauto.
    exploit (time_bound_addr C x); eauto. rw.
    ii. exploit EQm; eauto.
    ii. split; ii; des; clarify; split; eauto.
    erewrite <- IHp; eauto.
    erewrite IHp; eauto.
  - des_goal; eauto.
    exploit (time_bound_ctx_M C M); eauto. rw.
    ii. exploit IHp; eauto. s. eauto.
  - split; ii; des; des_hyp; des; clarify;
    exists (Closure x e C).
    split. rewrite <- EQm; eauto.
    split. eauto.
    exploit (time_bound_read m t t0); eauto.
    rrw. ii; ss; des. erewrite <- IHp; eauto.
    rewrite <- EQm in *; eauto.
    split. eauto.
    split. eauto.
    erewrite IHp; eauto.
    exploit (time_bound_read m t t0); eauto. rrw.
    ii; ss; des; eauto.
Qed.

Lemma pmap_root_bound `{TotalOrder T} {TT} :
  forall p r m (f f' : T -> TT) t
    (VALp : valid_path r m p)
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQf : forall t', leb t' t = true -> f' t' = f t'),
  pmap f' p = pmap f p.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify.
  - exploit (time_bound_addr C x); eauto.
    rewrite HDES0. ii.
    rewrite EQf; eauto. erewrite IHp; eauto. s. eauto.
  - exploit (time_bound_ctx_M C M); eauto.
    rewrite HDES0. ii.
    erewrite IHp; eauto. s. eauto.
  - des_hyp; des; clarify.
    exploit (time_bound_read m t t0). eauto.
    rewrite <- VALp. ii; ss; des.
    erewrite IHp; eauto. s. eauto.
Qed.

Lemma update_equiv `{time T} `{time TT} :
  forall (t t_up : T) (t' t_up' : TT) v v' C C' m m' f f' x
    (BOUNDv : time_bound_v v t)
    (BOUNDC : time_bound_C C t)
    (BOUNDm : time_bound_m m t)
    (LT : t << t_up)
    (BOUNDv' : time_bound_v v' t')
    (BOUNDC' : time_bound_C C' t')
    (BOUNDm' : time_bound_m m' t')
    (LT' : t' << t_up')
    (EQUIVv : <| (EVal v) m f ≃ (EVal v') m' f' |>)
    (EQUIVC : <| (MVal C) m f ≃ (MVal C') m' f' |>),
  let g t := if eqb t t_up then t_up' else f t in
  let g' t' := if eqb t' t_up' then t_up else f' t' in
  iso (Ctx (dy_binde x t_up C)) (t_up !-> v; m)
      (Ctx (dy_binde x t_up' C')) (t_up' !-> v'; m')
      g g'.
Proof.
  ii. subst g g'.
  assert (forall t'', leb t'' t = true -> eqb t_up t'' = false).
  {
    ii. refl_bool. ii. rewrite eqb_eq in *; clarify.
    assert (t = t'').
    apply leb_sym. apply LT. eauto.
    assert (t <> t'').
    rewrite <- eqb_neq. apply LT.
    eauto.
  }
  assert (forall t'', leb t'' t' = true -> eqb t_up' t'' = false).
  {
    ii. refl_bool. ii. rewrite eqb_eq in *; clarify.
    assert (t' = t'').
    apply leb_sym. apply LT'. eauto.
    assert (t' <> t'').
    rewrite <- eqb_neq. apply LT'.
    eauto.
  } split; ii.
  - subst p'.
    destruct p; ss;
    repeat des_hyp; des; clarify.
    + repeat rewrite t_refl. rewrite eqb_ID_eq in *. clarify.
      destruct p; ii; ss. repeat rewrite t_refl in *.
      des; des_hyp; des; clarify.
      exploit (vpath_root_bound p (Ctx C0) m (t0 !-> Closure x2 e0 C0; m)); eauto.
      ii. s. rw; eauto.
      intros RR. rewrite <- RR in *.
      exploit (pmap_root_bound p (Ctx C0) m f (fun t1 : T => if eqb t1 t0 then t_up' else f t1) t);
      eauto. ii. rewrite eqb_comm. rw; eauto.
      intros RR'. rewrite RR'.
      destruct EQUIVv1 as [EQv EQv'].
      exploit EQv; eauto. ii; des.
      exploit (pmap_root_bound (pmap f p) (Ctx C1) m' f' (fun t' => if eqb t' t_up' then t0 else f' t')); eauto.
      ii. rewrite eqb_comm. rw; eauto. rw. ii. rw.
      repeat (split; eauto).
      eexists. split. reflexivity. s. split. eauto.
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_addr C x0); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p (Ptr t0) m (t_up !-> Closure x2 e0 C0; m)); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC (Px x0 t0 p)); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound p (Ptr t0) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_addr C' x0); eauto. rw. rw.
      ii. rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound (pmap f p) (Ptr (f t0)) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_ctx_M C M); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p (Ctx d) m (t_up !-> Closure x1 e0 C0; m)); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC (PM M p)); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      exploit (pmap_root_bound p (Ctx d) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_ctx_M C' M); eauto. rw.
      ii.
      exploit (pmap_root_bound (pmap f p) (Ctx d0) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
  - subst p.
    destruct p'; ss;
    repeat des_hyp; des; clarify.
    + repeat rewrite t_refl. rewrite eqb_ID_eq in *. clarify.
      destruct p'; ii; ss. repeat rewrite t_refl in *.
      des; des_hyp; des; clarify.
      exploit (vpath_root_bound p' (Ctx C1) m' (t0 !-> Closure x2 e0 C1; m')); eauto.
      ii. s. rw; eauto.
      intros RR. rewrite <- RR in *.
      exploit (pmap_root_bound p' (Ctx C1) m' f' (fun t' => if eqb t' t0 then t_up else f' t') t');
      eauto. ii. rewrite eqb_comm. rw; eauto.
      intros RR'. rewrite RR'.
      destruct EQUIVv1 as [EQv EQv'].
      exploit EQv'; eauto. ii; des.
      exploit (pmap_root_bound (pmap f' p') (Ctx C0) m f (fun t' => if eqb t' t_up then t0 else f t')); eauto.
      ii. rewrite eqb_comm. rw; eauto. rw. ii. rw.
      repeat (split; eauto).
      eexists. split. reflexivity. s. split. eauto.
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_addr C' x0); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p' (Ptr t0) m' (t_up' !-> Closure x2 e0 C1; m')); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC' (Px x0 t0 p')); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound p' (Ptr t0) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_addr C x0); eauto. rw. rw.
      ii. rewrite eqb_comm. rw; eauto.
      exploit (pmap_root_bound (pmap f' p') (Ptr (f' t0)) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
    + exploit (time_bound_ctx_M C' M); eauto. rw.
      ii. destruct EQUIVC as [EQC EQC'].
      exploit (vpath_root_bound p' (Ctx d) m' (t_up' !-> Closure x1 e0 C1; m')); eauto.
      ii. s. rw; eauto. intros RR.
      rewrite <- RR in *.
      exploit (EQC' (PM M p')); eauto.
      s. rw. eauto.
      ii; ss; repeat des_hyp; des; clarify.
      exploit (pmap_root_bound p' (Ctx d) m' f' (fun t' => if eqb t' t_up' then t_up else f' t')); eauto.
      ii. rewrite eqb_comm. rw; eauto.
      ii. rw.
      exploit (time_bound_ctx_M C M); eauto. rw.
      ii.
      exploit (pmap_root_bound (pmap f' p') (Ctx d0) m f (fun t' => if eqb t' t_up then t_up' else f t')); eauto.
      ii. s. rewrite eqb_comm. rw; eauto. ii. rw. rw.
      repeat (split; eauto).
      erewrite <- vpath_root_bound; eauto.
      ii. s. rw; eauto.
Qed.

Lemma extend_mem_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall r r' m m_ext m' m_ext' (t : T) (t' : TT) f f'
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQm : forall addr, leb addr t = true -> read m addr = read m_ext addr)
    (BOUNDr' : match r' with Ctx C' => time_bound_C C' t' | Ptr addr' => leb addr' t' = true end)
    (BOUNDm' : time_bound_m m' t')
    (EQm' : forall addr', leb addr' t' = true -> read m' addr' = read m_ext' addr')
    (ISO : iso r m r' m' f f'),
  iso r m_ext r' m_ext' f f'.
Proof.
  intros. split; ii.
  - subst p'. destruct ISO as [ISO ?].
    rewrite <- vpath_root_bound; eauto.
    apply ISO. rewrite vpath_root_bound; eauto.
  - subst p. destruct ISO as [? ISO].
    rewrite <- vpath_root_bound; eauto.
    apply ISO. rewrite vpath_root_bound; eauto.
Qed.

Lemma extend_iso_equiv `{TotalOrder T} `{TotalOrder TT} :
  forall r r' m m' (t : T) (t' : TT) f f' f_ext f_ext'
    (BOUNDr : match r with Ctx C => time_bound_C C t | Ptr addr => leb addr t = true end)
    (BOUNDm : time_bound_m m t)
    (EQm : forall addr, leb addr t = true -> f addr = f_ext addr)
    (BOUNDr' : match r' with Ctx C' => time_bound_C C' t' | Ptr addr' => leb addr' t' = true end)
    (BOUNDm' : time_bound_m m' t')
    (EQm' : forall addr', leb addr' t' = true -> f' addr' = f_ext' addr')
    (ISO : iso r m r' m' f f'),
  iso r m r' m' f_ext f_ext'.
Proof.
  intros. split; ii.
  - subst p'. destruct ISO as [ISO ?].
    erewrite <- pmap_root_bound; eauto.
    exploit ISO; eauto. ii; ss; des.
    erewrite <- pmap_root_bound; eauto.
    split; eauto. erewrite pmap_root_bound; eauto.
    ii; symmetry; eauto.
  - subst p. destruct ISO as [? ISO].
    erewrite <- vpath_root_bound; eauto.
    exploit ISO; eauto. ii; ss; des.
    erewrite <- pmap_root_bound; eauto.
    split; eauto. erewrite pmap_root_bound; eauto.
    ii; symmetry; eauto.
Qed.

Theorem operational_equivalence `{time T} `{time TT} :
  forall e (C : dy_ctx T) m t cf_r (C' : dy_ctx TT) m' t' f f'
    (EVAL : {| (Cf e C m t) ~> cf_r |})
    (BOUND : time_bound_ρ (Cf e C m t))
    (BOUND' : time_bound_ρ (Cf e C' m' t'))
    (ISO : iso (Ctx C) m (Ctx C') m' f f'),
  exists cf_r' g g',
    (forall a (LE : leb a t = true), f a = g a) /\
    (forall a' (LE : leb a' t' = true), f' a' = g' a') /\
    {| (Cf e C' m' t') ~> cf_r' |} /\
    match cf_r, cf_r' with
    | Cf e_r C_r m_r t_r, Cf e_r' C_r' m_r' t_r' =>
      e_r = e_r' /\ <| (MVal C_r) m_r g ≃ (MVal C_r') m_r' g' |>
    | Rs V_r m_r t_r, Rs V_r' m_r' t_r' =>
      <| V_r m_r g ≃ V_r' m_r' g' |>
    | _, _ => False
    end.
Proof.
  ii. remember (Cf e C m t) as cf.
  ginduction EVAL; ii; ss; des; clarify;
  try gen_time_bound T.
  - destruct ISO as [ISO ISO'].
    destruct v as [x_v e_v C_v].
    exploit (ISO (Px x addr (Pv (v_fn x_v e_v) Pnil))).
    s. repeat rw. split; eauto.
    eexists. split; eauto. s. eauto.
    ii; ss; repeat des_hyp; des; clarify.
    des_hyp; des; clarify.
    exists (Rs (EVal (Closure x0 e C)) m' t'). exists f. exists f'.
    repeat match goal with
    | |- _ /\ _ => split; eauto
    end.
    split.
    ii. subst p'.
    exploit (ISO (Px x addr (Pv (v_fn x0 e) p))).
    s. repeat rw. split; eauto.
    eexists. split; eauto. s. eauto.
    ii; ss; repeat des_hyp; des; clarify.
    des_hyp; des; clarify.
    match goal with
    | RR : Some _ = read ?m ?t, H : Some _ = read ?m ?t |- _ =>
      rewrite <- RR in H; clarify
    end.
    ii. subst p.
    exploit (ISO' (Px x (f addr) (Pv (v_fn x0 e) p'))).
    s. repeat rw. split; eauto.
    rrw. eexists. split; eauto. s. eauto.
    ii; ss; repeat des_hyp; des; clarify.
    des_hyp; des; clarify.
    revert x5. repeat rw. ii; clarify.
  - exists (Rs (EVal (Closure x e C')) m' t').
    exists f. exists f'. repeat (split; eauto).
  - exists (Cf e1 C' m' t').
    exists f. exists f'. repeat (split; eauto).
  - exploit IHEVAL; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exists (Cf e2 C' m t). exists g. exists g'.
    split. eauto. split. eauto. split. eauto. split. eauto.
    ss. des.
    eapply extend_mem_equiv with (t := t0); eauto.
    exploit (@extend_mem T); eauto. s. eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT); eauto. s. eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0); eauto.
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto.
    ss; des. eauto using relax_ctx_bound.
    instantiate (1 := g'). instantiate (1 := g).
    eapply extend_mem_equiv with (t := t0); eauto.
    exploit (@extend_mem T); eauto. s. eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT); eauto. s. eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0); eauto.
    ii; des. repeat des_hyp; des; clarify.
    gen_time_bound TT.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure ?x ?e ?Cv)) ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f' |-
      context [iso (Ctx (dy_binde ?x ?t_up ?Cv')) (?t_up !-> ?v'; ?m_up) _ _ _ _] =>
      exists (Cf e (dy_binde x (tick C m'' t'' x v) Cv) 
        ((tick C m'' t'' x v) !-> v; m'') (tick C m'' t'' x v));
      exploit (update_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
      try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end.
    ss. des. eapply relax_ctx_bound; eauto.
    s.
    eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m_f); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t_f) (t' := t); eauto.
    ii.
    match goal with
    | _ : iso _ _ _ _ ?f ?f' |- _ =>
      exists f; exists f'
    end.
    repeat (split; eauto); ii;
    match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  - exploit IHEVAL1; eauto. ii; des.
    repeat des_hyp; des; clarify.
    gen_time_bound TT.
    exploit (IHEVAL2 _ _ _ _ _ C0 _ _ C' m t); eauto.
    ss; des. eauto using relax_ctx_bound.
    instantiate (1 := g'). instantiate (1 := g).
    eapply extend_mem_equiv with (t := t0); eauto.
    exploit (@extend_mem T); eauto. s. eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT); eauto. s. eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t0); eauto.
    ii; des. repeat des_hyp; des; clarify.
    gen_time_bound TT.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure ?x ?e ?Cv)) ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ ?m_up _ _ ?f ?f',
      E3 : @step T _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (update_equiv _ t_up _ (tick C m'' t'' x v) v' v Cv' Cv m_up m'' f f' x);
        try solve [apply tick_lt | ss; des; eauto using relax_ctx_bound]
    end.
    ss. des. eapply relax_ctx_bound; eauto.
    s.
    eapply extend_mem_equiv with (t := t_f) (m := m_f) (m' := m) (t' := t);
    ss; des; eauto.
    exploit (@extend_mem T _ _ _ _ _ m_f); eauto. s; eauto. s.
    ii. symmetry. eauto.
    exploit (@extend_mem TT _ _ _ _ _ m); eauto. s; eauto. s.
    ii. symmetry. eauto.
    eapply extend_iso_equiv with (t := t_f) (t' := t); eauto.
    ii.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs (EVal (Closure ?x ?e ?Cv)) ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') (Rs (EVal ?v) ?m'' ?t''),
      ISO : iso _ (?t_up !-> ?v'; ?m_up) (Ctx ?C_up') ?m_up' ?f ?f',
      E3 : @step T _ _ _ (Cf _ (dy_binde ?x ?t_up ?Cv') (?t_up !-> ?v'; ?m_up) _) _ |- _ =>
      exploit (IHEVAL3 _ _ _ _ _ _ (t_up !-> v'; m_up) t_up C_up' m_up' (tick C m'' t'' x v) f f');
      eauto
    end.
    split; ii; ss; des; clarify; do 5 solve_leb1.
    lebt t. eauto. apply leb_refl.
    ii. des; repeat des_hyp; des; clarify.
    match goal with
    | E1 : @step TT _ _ _ (Cf _ ?C ?m ?t) (Rs _ ?m' ?t'),
      E2 : @step TT _ _ _ (Cf _ ?C ?m' ?t') _,
      E3 : @step TT _ _ _ _ (Rs (EVal (Closure ?x' ?e' ?Cv')) ?m'' ?t''),
      ISO : iso _ _ (Ctx ?Cv') ?m'' ?f ?f' |- _ =>
      exists (Rs (EVal (Closure x' e' Cv')) m'' t''); exists f; exists f'
    end.
    repeat (split; eauto); ii;
    repeat rrw;
    try match goal with
    | |- context [eqb ?a (tick ?C ?m ?t ?x ?v)] =>
      exploit (leb_t_neq_tick C m x v a t);
      try solve_leb
    end; ii; repeat rw;
    solve [reflexivity | solve_leb].
  

(*


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
  - eapply paste_vpath; eauto.
    rw. destruct e; ss; repeat des_hyp; des; clarify.
    exists (Px x (Ptr t) Pnil). ss. rw. eauto.
    exists (PM M (Ctx C0) Pnil). ss. rw. eauto.
    des_hyp; des; clarify.
    exists (Pv (v_fn x e) (Ctx C) Pnil). ss.
    split; eauto.
    exists (Closure x e C). eauto.
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
      * destruct e; ss; repeat des_hyp; des; clarify;
        match goal with
        | _ => solve [rewrite eqb_eq in *; des; clarify; eauto]
        | _ => right; right; rewrite INV; ss; split; eauto
        end.
        rw. eauto. rw. eauto.
      * rewrite in_app_iff in *. ss; des.
        (* case 1 *)
        rewrite <- reach_C_eq_def in *.
        destruct e; ss; repeat des_hyp; clarify;
        match goal with
        | |- context [reachable _ _ ?e] =>
          left; eapply paste_vpath; eauto; rw;
          match e with
          | Ex _ ?x ?n =>
            exists (Px x n Pnil); ss; rw; eauto
          | EM _ ?M ?n =>
            exists (PM M n Pnil); ss; rw; eauto
          end
        | _ => rewrite eqb_eq in *; repeat (des; clarify; eauto)
        | _ => right; right; des; des_hyp; des; clarify
        end.
        rewrite <- read_memify_In; eauto.
        ii. rewrite INV in *. des; eauto.
        (* case 2 *)
        clarify; ss. left.
        rewrite <- reach_C_eq_def.
        rewrite valid_edge_C in IN; eauto.
        rewrite reachable_eq_def. eauto.
        (* case 3 *)
        destruct e; ss; repeat des_hyp; des; clarify;
        match goal with
        | _ => solve [rewrite eqb_eq in *; des; clarify; eauto]
        | _ => right; right; rewrite INV; ss; split; eauto
        end.
        rw. eauto. rw. eauto.
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
      apply app_same.
      apply app_disj_same.
      ii; ss. des_hyp; clarify.
      rewrite eqb_eq in *. clarify.
      match goal with |- None = ?x => destruct x eqn:CASE end; try reflexivity.
      symmetry in CASE.
      destruct e0. rewrite read_memify_In in CASE.
      rewrite in_app_iff in *. des.
      assert (InL (Ptr t0) acc'' = true).
      rewrite InL_In. eauto. clarify.
      assert (InL (Ptr t0) acc = true).
      rewrite InL_In. eauto. clarify.
      ii. rewrite POST in *. des; eauto.
      ii; ss.
    + exists acc''. split; eauto.
      split; ii; eauto.
      des_hyp; clarify.
      rewrite eqb_eq in *; clarify.
      exploit POST2; eauto. ii. des.
      exists t'. des_goal; clarify.
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
    solve [rewrite InL_In; exists (Ev (Ptr t0) (v_fn x e) (Ctx C)); eauto | clarify].
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
      ii. ginduction p'; ii; ss;
      repeat des_goal; des; clarify; eauto.
      rewrite eqb_eq in *. clarify.
      des. des_hyp. rewrite read_memify_In in *; eauto.
      des; clarify.
      assert (InL (Ptr t0) E = true).
      rewrite InL_In. eauto. clarify.
      des. des_hyp. des. clarify.
      exists (Closure x0 e C1); eauto.
    }
    rewrite in_app_iff in *.
    ss. des; clarify.
    + rewrite <- reach_C_eq_def in IN'.
      eapply paste_vpath. instantiate (1 := e1).
      exists p. split; eauto.
      rrw.
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
      rrw.
      match goal with
      | _ : context [(?t, Closure ?x ?e ?C)] |- _ =>
        exists (Pv (v_fn x e) (Ctx C) Pnil);
        ss; rewrite t_refl; split; eauto;
        exists (Closure x e C); eauto
      end.
    + apply PRE in IN'.
      destruct IN' as [p' [VAL' IN']].
      exists p'. eauto.
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
    rewrite InR_In. eauto.
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
    des_hyp; des; clarify; eauto.
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
    des_hyp; des; clarify; eauto.
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

(* for convenience: UNICODE ϕ φ *)
(* assumed : f (α C) ≃# aC except for paths starting with
 * x in seenx and M in seenM, when f is a graph isomorphism *)
(* trans: holds translated equivalent nodes *)
Fixpoint trans_equiv_C_aux `{Eq T} `{Eq TT} `{Eq aTT}
  (inv_α : (TT * aTT) -> TT)
  (t : TT) (ϕ : list (node T * node TT)) seenx seenM
  (C : dy_ctx T) (aC : dy_ctx aTT) :=
  match fst_trans ϕ (Ctx C) with
  | Some (Ctx C) => Some (t, ϕ, C) (* already translated *)
  | Some (Ptr _) => None
  | None =>
  let ret := match aC with
  | [||] => Some (t, ϕ, [||])
  | dy_binde x tx aC =>
    if Inb x seenx then (* unreachable *)
      let tx := inv_α (t, tx) in
      match trans_equiv_C_aux inv_α t ϕ seenx seenM C aC with
      | None => None
      | Some (t, ϕ, C) => Some (t, ϕ, dy_binde x tx C)
      end
    else match addr_x C x with (* reachable *)
    | None => None
    | Some addr =>
      let seenx := x :: seenx in
      match fst_trans ϕ (Ptr addr) with
      | Some (Ctx _) => None
      | Some (Ptr tx) =>
        match trans_equiv_C_aux inv_α t ϕ seenx seenM C aC with
        | None => None
        | Some (t, ϕ, C) => Some (t, ϕ, dy_binde x tx C)
        end
      | None =>
        let tx := inv_α (t, tx) in
        let ϕ := (Ptr addr, Ptr tx) :: ϕ in
        match trans_equiv_C_aux inv_α tx ϕ seenx seenM C aC with
        | None => None
        | Some (t, ϕ, C) => Some (t, ϕ, dy_binde x tx C)
        end
      end
    end
  | dy_bindm M C_M aC =>
    if Inb M seenM then (* unreachable *)
      let C_M := lift_C inv_α t C_M in
      match trans_equiv_C_aux inv_α t ϕ seenx seenM C aC with
      | None => None
      | Some (t, ϕ, C) => Some (t, ϕ, dy_bindm M C_M C)
      end
    else match ctx_M C M with (* reachable *)
    | None => None
    | Some C_M' =>
      let seenM := M :: seenM in
      match trans_equiv_C_aux inv_α t ϕ [] [] C_M' C_M with
      | None => None
      | Some (t, ϕ, C_M) =>
        match trans_equiv_C_aux inv_α t ϕ seenx seenM C aC with
        | None => None
        | Some (t, ϕ, C) => Some (t, ϕ, dy_bindm M C_M C)
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
  | Some (t, ϕ, C') =>
    if top
    then Some (t, (Ctx C, Ctx C') :: ϕ, C')
    else Some (t, ϕ, C')
  end end.


Definition trans_equiv_m :=
  (* check oracle, if reachable trans_equiv_C
     if unreachable lift_C *)
0.

Definition trans_equiv := 0.
*)
