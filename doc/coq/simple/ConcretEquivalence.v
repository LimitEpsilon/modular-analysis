From Simple Require Export Bound.

Generalizable Variables T TT aT aTT.

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

Lemma asame_comm `{Eq T} :
  forall m m',
  asame m m' <-> asame m' m.
Proof.
  intros; unfold asame; split; ii; rw; eauto.
Qed.

Lemma asame_trans `{Eq T} :
  forall m m' m'' (SAME : asame m m') (SAME' : asame m' m''),
  asame m m''.
Proof.
  ii. unfold asame in *. rewrite SAME. rewrite SAME'. eauto.
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
  induction m; intros; simpl; eauto;
  repeat des_goal; repeat des_hyp; clarify;
  try rewrite eqb_eq in *; subst;
  match goal with
  | |- context [remove_t _ ?t] =>
    specialize (IHm t); nia
  end.
Qed.

Lemma remove_t_strict_dec `{Eq T} :
  forall (m : memory T) t (READ : None <> read m t),
  (List.length (remove_t m t)) < (List.length m).
Proof.
  induction m; intros; simpl; eauto; clarify.
  des_goal. rewrite eqb_comm.
  repeat des_goal; repeat des_hyp; clarify;
  try rewrite eqb_eq in *; subst.
  pose proof (remove_t_dec m t). nia.
  ss.
  revert READ. rw. ii. exploit IHm; eauto.
  nia.
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

Lemma avpath_less_then_avpath_more `{Eq T} :
  forall a b p r (VAL : avalid_path r a p),
  avalid_path r (a ++ b) p.
Proof.
  ii.
  ginduction p; ii; ss;
  repeat des_hyp; des; clarify; eauto.
  des_hyp; des; clarify.
  exists (Closure x e C).
  rewrite aread_in in *. rewrite in_app_iff. eauto.
Qed.

Lemma avpath_trans_empty `{Eq T} `{Eq TT} (φ : T -> TT) :
  forall p C C' m' (VAL : avalid_path (Ctx C) [] p)
    (VAL' : avalid_path (Ctx C') m' (pmap φ p)),
  avalid_path (Ctx C') [] (pmap φ p).
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify.
  - destruct p; ss; des; clarify.
  - eapply IHp; eauto.
Qed.

Fixpoint plen {T} (p : path T) :=
  match p with
  | Pnil => 0
  | PM _ p
  | Pv _ p
  | Px _ _ p => S (plen p)
  end.

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
    Some t = read_fst ϕ t' /\ x' = x /\ e' = e /\
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
    repeat (split; eauto).
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
      rewrite eqb_neq. ii. clarify. rewrite CASE in *. clarify.
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

Definition equiv_fst_ϕ_m `{Eq T} `{Eq TT} (ϕ : list (T * TT)) m m' :=
  forall t p x e C
  (READ : Some (Closure x e C) = read m t)
  (VALp : valid_path (Ctx C) [] p),
  match read_fst ϕ t with
  | Some t' =>
    match pmap_fst ϕ p with
    | Some p' =>
      exists C', Some (Closure x e C') = read m' t' /\
        valid_path (Ctx C') [] p'
    | None => False
    end 
  | None => False
  end.

Definition equiv_snd_ϕ_m `{Eq T} `{Eq TT} (ϕ : list (T * TT)) m m' :=
  forall t p x e C
  (READ : Some (Closure x e C) = read m t)
  (VALp : valid_path (Ctx C) [] p),
  match read_snd ϕ t with
  | Some t' =>
    match pmap_snd ϕ p with
    | Some p' =>
      exists C', Some (Closure x e C') = read m' t' /\
        valid_path (Ctx C') [] p'
    | None => False
    end 
  | None => False
  end.

Definition equiv_fst_ϕ_C `{Eq T} `{Eq TT} (ϕ : list (T * TT)) C C' :=
  forall p
    (VALp : valid_path (Ctx C) [] p),
  match pmap_fst ϕ p with
  | Some p' => valid_path (Ctx C') [] p'
  | None => False
  end.

Definition equiv_snd_ϕ_C `{Eq T} `{Eq TT} (ϕ : list (T * TT)) C C' :=
  forall p
    (VALp : valid_path (Ctx C) [] p),
  match pmap_snd ϕ p with
  | Some p' => valid_path (Ctx C') [] p'
  | None => False
  end.

Lemma equiv_fst_ϕ_aux `{Eq T} `{Eq TT} (ϕ : list (T * TT)) 
  m m' (EQm : equiv_fst_ϕ_m ϕ m m') :
  forall n C C' (EQC : equiv_fst_ϕ_C ϕ C C')
    p (VALp : valid_path (Ctx C) m p)
    (LE : plen p <= n),
  match pmap_fst ϕ p with
  | Some p' => valid_path (Ctx C') m' p'
  | None => False
  end.
Proof.
  unfold equiv_fst_ϕ_m in *.
  unfold equiv_fst_ϕ_C in *.
  induction n.
  ii. destruct p; ss; nia.
  ii; ss. destruct p; ss.
  - des_hyp; des; clarify.
    exploit (EQC (Px x t Pnil)). s. rw. eauto.
    s. ii. repeat des_hyp; des; clarify.
    ss. des_hyp; des; clarify.
    destruct n; ss.
    destruct p; ss; first [rw; eauto | nia].
    destruct p; ss. rw. eauto.
    des. des_hyp; des; clarify.
    exploit (EQm t Pnil _ _ _); eauto.
    ii. repeat des_hyp; des; clarify.
    exploit (IHn C0 C'0 _ p); eauto.
    ii.
    exploit (EQm t p0); eauto. repeat rw.
    ii. repeat des_hyp; des; clarify.
    revert x3. rrw. ii. clarify. nia.
    ii. des_hyp.
    s. rw. split; eauto. eexists. split; eauto. s. eauto.
  - des_hyp.
    exploit (EQC (PM M Pnil)). s. rw. eauto.
    ii. ss. des_hyp.
    exploit (IHn d d0 _ p).
    ii. exploit (EQC (PM M p0)). s. rw. eauto.
    s. ii. repeat des_hyp; clarify.
    revert x1. s. rw. eauto. eauto. nia.
    ii. des_hyp. s. rw. eauto.
Qed.

Lemma equiv_snd_ϕ_aux `{Eq T} `{Eq TT} (ϕ : list (T * TT)) 
  m m' (EQm : equiv_snd_ϕ_m ϕ m m') :
  forall n C C' (EQC : equiv_snd_ϕ_C ϕ C C')
    p (VALp : valid_path (Ctx C) m p)
    (LE : plen p <= n),
  match pmap_snd ϕ p with
  | Some p' => valid_path (Ctx C') m' p'
  | None => False
  end.
Proof.
  unfold equiv_snd_ϕ_m in *.
  unfold equiv_snd_ϕ_C in *.
  induction n.
  ii. destruct p; ss; nia.
  ii; ss. destruct p; ss.
  - des_hyp; des; clarify.
    exploit (EQC (Px x t Pnil)). s. rw. eauto.
    s. ii. repeat des_hyp; des; clarify.
    ss. des_hyp; des; clarify.
    destruct n; ss.
    destruct p; ss; first [rw; eauto | nia].
    destruct p; ss. rw. eauto.
    des. des_hyp; des; clarify.
    exploit (EQm t Pnil _ _ _); eauto.
    ii. repeat des_hyp; des; clarify.
    exploit (IHn C0 C'0 _ p); eauto.
    ii.
    exploit (EQm t p0); eauto. repeat rw.
    ii. repeat des_hyp; des; clarify.
    revert x3. rrw. ii. clarify. nia.
    ii. des_hyp.
    s. rw. split; eauto. eexists. split; eauto. s. eauto.
  - des_hyp.
    exploit (EQC (PM M Pnil)). s. rw. eauto.
    ii. ss. des_hyp.
    exploit (IHn d d0 _ p).
    ii. exploit (EQC (PM M p0)). s. rw. eauto.
    s. ii. repeat des_hyp; clarify.
    revert x1. s. rw. eauto. eauto. nia.
    ii. des_hyp. s. rw. eauto.
Qed.

Inductive fix_result `{Eq T} `{Eq TT} :=
  | Fix (m mbot : memory T) (m' : memory TT) (ϕ : list (T * TT)) (tϕ : TT)
  | Unfix
.

Fixpoint trans_iso_m_aux `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) φ φ'
  (ϕ : list (TT * T)) (tϕ : T)
  (am : memory aT) (m1 : memory T) (m2 m : memory TT) fuel :=
  match trans_m_step α' inv_α φ φ' ϕ tϕ am m with
  | Unchanged => Fix m2 m m1 ϕ tϕ
  | Changed t' v' t v ϕ' tϕ' =>
    let m1' := (t, v) :: m1 in
    let m2' := (t', v') :: m2 in
    let m' := remove_t m t' in
    match fuel with
    | 0 => Unfix
    | S fuel' => trans_iso_m_aux α' inv_α φ φ' ϕ' tϕ' am m1' m2' m' fuel'
    end
  | Failed => Unfix
  end.

Definition trans_iso_m `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) φ φ'
  (ϕ : list (TT * T)) (tϕ : T)
  (am : memory aT) (m : memory TT) :=
  trans_iso_m_aux α' inv_α φ φ' ϕ tϕ am [] [] m (length m).

Definition trans_iso_m_pre `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT) φ φ'
  (ϕ : list (TT * T)) (tϕ : T) (C2 : dy_ctx TT) (C1 : dy_ctx T)
  (am : memory aT) (m1 : memory T) (m2 m : memory TT) :=
  (forall t, None <> read m2 t -> None = read m t) /\
  (forall t, reachable (Ctx C2) m2 t <-> None <> read_fst ϕ t) /\
  equiv_fst_ϕ_C ϕ C2 C1 /\
  equiv_snd_ϕ_C ϕ C1 C2 /\
  equiv_fst_ϕ_m ϕ m2 m1 /\
  equiv_snd_ϕ_m ϕ m1 m2 /\
  ϕ_spec α' α φ φ' ϕ tϕ /\
  inv_α_spec α inv_α /\
  aIso (Ctx (trans_C α' C2)) (trans_m α' (m2 ++ m))
       (Ctx (trans_C α C1)) am φ φ' /\
  (forall t v, Some v = read m1 t ->
    In (trans_v α v) (aread am (α t)))
.

Lemma pre_implies_pre `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT) φ φ'
  (ϕ : list (TT * T)) (tϕ : T) (C2 : dy_ctx TT) (C1 : dy_ctx T)
  (am : memory aT) (m1 : memory T) (m2 m : memory TT) :
  trans_iso_m_pre α' inv_α α φ φ' ϕ tϕ C2 C1 am m1 m2 m ->
  trans_m_step_pre α' φ φ' ϕ am m.
Proof.
  intros ISO.
  ii. unfold trans_iso_m_pre in ISO. des.
  assert (reachable (Ctx C2) m2 t') as REACH.
  { rewrite <- ISO0 in *. assumption. }
  unfold aIso in *.
  des_goal; eauto.
  des.
  assert (areachable (Ctx (trans_C α' C2)) (trans_m α' (m2 ++ m)) (α' t')).
  {
    destruct REACH as [p [VALp INp]].
    apply vpath_less_then_vpath_more with (b := m) in VALp.
    apply vp_then_avp with (α := α') in VALp.
    exists (pmap α' p). split; eauto.
    clear IN GDES VALp.
    generalize dependent t'.
    induction p; ii; ss; des; clarify; eauto.
  }
  exploit (ISO9 _ (trans_v α' e)); eauto.
  {
    rewrite trans_m_aread.
    rewrite <- disj_reflect in ISO.
    exploit (ISO t'). rw. ii; clarify. ii.
    exists t'. exists e. rewrite read_top. rrw. eauto.
  }
  ii; des. exists v'. split; eauto.
  repeat des_hyp; des; clarify.
  rewrite <- check_aiso_aiso in *.
  rewrite <- iso_C_is_aiso_C in *.
  rewrite check_iso_iso in *. eauto.
Qed.

Lemma pmap_fst_read `{Eq T} `{Eq TT} (ϕ: list (T * TT)) :
  forall p p' t (MAP : pmap_fst ϕ p = Some p') (IN : Inp t p),
  None <> read_fst ϕ t.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify.
  all:try solve [exploit IHp; eauto].
  rewrite HDES in *. clarify.
Qed.

Lemma pmap_snd_read `{Eq T} `{Eq TT} (ϕ: list (T * TT)) :
  forall p p' t (MAP : pmap_snd ϕ p = Some p') (IN : Inp t p),
  None <> read_snd ϕ t.
Proof.
  induction p; ii; ss; repeat des_hyp; des; clarify.
  all:try solve [exploit IHp; eauto].
  rewrite HDES in *. clarify.
Qed.

Lemma same_valid `{Eq T} :
  forall p r m1 m2 (SAME : same m1 m2),
    valid_path r m1 p <-> valid_path r m2 p.
Proof.
  induction p; ii; ss; split; ii; repeat des_hyp; des; clarify.
  rw; eauto. unfold same in *. ii. rw. eauto.
  rw; eauto. rw; eauto. unfold same in *; ii; rw; eauto.
  rw; eauto.
  des_hyp; des; clarify. unfold same in SAME. rewrite SAME in *.
  eexists. split; eauto. s. rw; eauto. ii. rw. eauto.
  des_hyp; des; clarify. unfold same in SAME. rewrite <- SAME in *.
  eexists. split; eauto. s. rw; eauto.
Qed.

Lemma asame_avalid `{Eq T} :
  forall p r m1 m2 (SAME : asame m1 m2),
    avalid_path r m1 p <-> avalid_path r m2 p.
Proof.
  induction p; ii; ss; split; ii; repeat des_hyp; des; clarify.
  rw; eauto. unfold asame in *. ii. rw. eauto.
  rw; eauto. rw; eauto. unfold asame in *; ii; rw; eauto.
  rw; eauto.
  des_hyp; des; clarify. unfold asame in SAME. rewrite SAME in *.
  eexists. split; eauto. s. rw; eauto. ii. rw. eauto.
  des_hyp; des; clarify. unfold asame in SAME. rewrite <- SAME in *.
  eexists. split; eauto. s. rw; eauto.
Qed.

Lemma asame_aIso `{Eq T} `{Eq TT} (φ : T -> TT) φ' :
  forall r m1 m2 r' m' (SAME : asame m1 m2) (ISO : aIso r m2 r' m' φ φ'),
  aIso r m1 r' m' φ φ'.
Proof.
  ii. destruct ISO as [[ISO ISO'] [ISO'' ISO''']]. ss.
  split. split; ss.
  ii. apply ISO. rewrite asame_avalid in *; eauto.
  split; ii; ss.
  ii. rewrite asame_avalid; eauto.
  split; ii. destruct REACH as [p [VALp INp]].
  apply ISO''. exists p. split; eauto. rewrite <- asame_avalid; eauto.
  unfold asame in SAME. rewrite <- SAME. eauto.
  exploit ISO'''; eauto. ii; des.
  exists v.
  unfold asame in *. rewrite SAME. eauto.
Qed.

Lemma trans_m_iso_pre_post `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  n (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT) φ φ'
  (ϕ : list (TT * T)) (tϕ : T) (C2 : dy_ctx TT) (C1 : dy_ctx T)
  (am : memory aT) (m1 : memory T) (m2 m : memory TT)
  (LE : length m <= n)
  (PRE : trans_iso_m_pre α' inv_α α φ φ' ϕ tϕ C2 C1 am m1 m2 m) :
  match trans_iso_m_aux α' inv_α φ φ' ϕ tϕ am m1 m2 m n with
  | Fix m2' m' m1' ϕ' tϕ' =>
    (trans_iso_m_pre α' inv_α α φ φ' ϕ' tϕ' C2 C1 am m1' m2' m') /\
    same (m2 ++ m) (m2' ++ m') /\
    (forall t' (IN : None <> read_fst ϕ' t'), None = read m' t')
  | Unfix => False
  end.
Proof.
  ginduction n; ii; ss.
  destruct m; ss; nia.
  apply pre_implies_pre in PRE as PRE'.
  unfold trans_iso_m_pre in PRE. des.
  exploit (@trans_m_step_pre_post TT _ aTT _ T _ _ aT); eauto.
  intros POST. unfold trans_m_step_post in *.
  repeat des_hyp; eauto.
  repeat (split; eauto).
  des; clarify.
  assert (read m2 t = None) as DISJ.
  {
    destruct (read m2 t) eqn:CASE; eauto.
    exploit (PRE t). rw. ii; clarify.
    repeat rrw. ii; clarify.
  }
  assert (same ((t, Closure x0 e0 C) :: m2 ++ remove_t m t) (m2 ++ m)) as SAME.
  {
    apply same_trans with (m' := m2 ++ ([(t, Closure x0 e0 C)] ++ remove_t m t)).
    rewrite app_assoc.
    match goal with
    | |- context [?a :: ?b ++ ?c] =>
      replace (a :: b ++ c) with (([a] ++ b) ++ c) by reflexivity
    end.
    apply app_same.
    apply app_disj_same. ii; ss. des_hyp; clarify.
    rewrite eqb_eq in *. clarify.
    split; ii; ss.
    apply app_same. split; ii; ss.
    split; ii; ss.
    repeat des_hyp; clarify. rewrite eqb_eq in *. clarify.
    rewrite remove_t_read_some in *; eauto. rewrite eqb_neq in *. eauto.
    des_goal. rewrite eqb_eq in *. clarify. repeat rw. eauto.
    rewrite remove_t_read_some; eauto. rewrite eqb_neq in *. eauto.
  }
  exploit (IHn TT _ aTT _ T _ _ aT _ α' inv_α α φ φ' (ϕ' ++ ϕ) tϕ0 C2 C1 am ((t', Closure x0 e0 C0) :: m1) ((t, Closure x0 e0 C) :: m2) (remove_t m t)); eauto.
  exploit (remove_t_strict_dec m t).
  repeat rrw. rw. ii; clarify. nia.
  split. ii; ss. des_hyp. rewrite eqb_eq in *; clarify.
  erewrite remove_t_read; eauto.
  exploit PRE; eauto. erewrite remove_t_read_some; eauto.
  rewrite <- eqb_neq. eauto.
  repeat match goal with |- _ /\ _ => split end.
  - ii. split; intros REACH. apply tail_vpath in REACH.
    des; clarify.
    destruct REACH as [p [VALp INp]].
    apply vpath_less_then_vpath_more with (b := m2) in VALp; ss.
    assert (None <> read_fst ϕ t0). rewrite <- PRE0. exists p. eauto.
    rewrite read_fst_top.
    repeat des_goal; clarify.
    destruct (eqb t t'0) eqn:CASE.
    rewrite eqb_eq in *. clarify. ss. rewrite t_refl in *. clarify.
    destruct REACH1 as [p [VALp INp]].
    exploit POST7; eauto.
    des_goal; clarify.
    ii. exploit (pmap_fst_read (ϕ' ++ ϕ) p); eauto.
    ss. rewrite CASE in *. destruct REACH1 as [p [VALp INp]].
    exploit PRE3; eauto.
    ii. repeat des_hyp; des; clarify.
    exploit (pmap_fst_read ϕ p); eauto.
    rewrite read_fst_top in *. repeat des_hyp; clarify.
    assert (reachable (Ctx C2) m2 t) as REACH'.
    { rewrite PRE0. rrw. ii; clarify. }
    rewrite read_fst_top in *. repeat des_hyp; clarify.
    exploit (POST8 t0). rw. ii; clarify. intros [p [VALp INp]].
    apply paste_vpath with (t := t).
    apply reachable_disj with (m' := [(t, Closure x0 e0 C)]); eauto.
    rewrite <- disj_reflect. ii; ss.
    des_hyp; clarify. rewrite eqb_eq in *; clarify.
    exists (Pv (v_fn x0 e0) p). s. split; eauto.
    rewrite t_refl. eexists. split; eauto.
    s. split; eauto.
    exploit (vpath_less_then_vpath_more [] _ p (Ctx C)); eauto.
    rewrite <- PRE0 in REACH.
    apply reachable_disj with (m' := [(t, Closure x0 e0 C)]); eauto.
    rewrite <- disj_reflect. ii; ss.
    des_hyp; clarify. rewrite eqb_eq in *; clarify.
  - ii. exploit PRE1; eauto. ii. des_hyp.
    erewrite (@pmap_fst_app TT _ aTT _ T _ _ aT); eauto.
  - ii. exploit PRE2; eauto. ii. des_hyp.
    erewrite (@pmap_snd_app TT _ aTT _ T _ _ aT); eauto.
  - ii; ss. des_hyp; clarify.
    rewrite eqb_eq in *. clarify. exploit POST7; eauto.
    assert (read_fst (ϕ' ++ ϕ) t0 = Some t').
    {
      apply read_fst_in in POST.
      exploit (POST4 t0 t'). rewrite in_app_iff; eauto.
      ii. des. rrw. eauto.
    }
    rw. ii. des_hyp. rewrite t_refl. eexists. split; eauto.
    exploit PRE3; eauto.
    ii. repeat des_hyp; des; clarify.
    assert (read_fst (ϕ' ++ ϕ) t0 = Some t1).
    {
      symmetry in HDES1.
      apply read_fst_in in HDES1.
      exploit (POST4 t0 t1). rewrite in_app_iff; eauto.
      ii. des. rrw. eauto.
    }
    rw. erewrite (@pmap_fst_app TT _ aTT _ T _ _ aT); eauto.
    assert (eqb t' t1 = false).
    {
      rewrite eqb_neq. ii. clarify.
      apply read_fst_in in POST.
      exploit (PRE5 t t1); eauto. ii; des.
      symmetry in HDES1. apply read_fst_in in HDES1.
      exploit (PRE5 t0 t1); eauto. ii; des.
      rewrite <- x3 in *. clarify. rewrite t_refl in *. clarify.
    }
    rw. eexists. split; eauto.
  - ii; ss. des_hyp; clarify.
    rewrite eqb_eq in *. clarify. exploit POST6; eauto.
    assert (read_snd (ϕ' ++ ϕ) t0 = Some t).
    {
      apply read_fst_in in POST.
      exploit (POST4 t t0). rewrite in_app_iff; eauto.
      ii. des. rrw. eauto.
    }
    rw. ii. des_hyp. rewrite t_refl. eexists. split; eauto.
    exploit PRE4; eauto.
    ii. repeat des_hyp; des; clarify.
    assert (read_snd (ϕ' ++ ϕ) t0 = Some t1).
    {
      symmetry in HDES1.
      apply read_snd_in in HDES1.
      exploit (POST4 t1 t0). rewrite in_app_iff; eauto.
      ii. des. rrw. eauto.
    }
    rw. erewrite (@pmap_snd_app TT _ aTT _ T _ _ aT); eauto.
    assert (eqb t t1 = false).
    {
      rewrite eqb_neq. ii. clarify.
      apply read_fst_in in POST.
      exploit (PRE5 t1 t'); eauto. ii; des.
      symmetry in HDES1. apply read_snd_in in HDES1.
      exploit (PRE5 t1 t0); eauto. ii; des.
      rewrite <- x4 in *. clarify. rewrite t_refl in *. clarify.
    }
    rw. eexists. split; eauto.
  - eauto.
  - eauto.
  - eapply asame_aIso with (m2 := trans_m α' (m2 ++ m)); eauto.
    apply trans_m_asame; eauto.
  - ii; ss. des_hyp; eauto.
    rewrite eqb_eq in *. clarify.
  - ii. des_hyp; des. split; eauto. split; eauto.
    eapply same_trans; eauto.
    rewrite same_comm. eauto.
Qed.

Lemma separate_mem `{Eq T} (P : T -> Prop) :
  forall p r m1 m2 
    (M1 : forall t, (r = Ptr t \/ reachable r m1 t) -> P t)
    (M2 : forall t, P t -> read m2 t = None)
    (VAL : valid_path r (m1 ++ m2) p),
  valid_path r m1 p.
Proof.
  induction p; ii; ss;
  repeat des_hyp; des; clarify.
  - split; eauto. eapply IHp; eauto.
    intros t' [? | [p' [VALp INp]]]; clarify; apply M1; right.
    exists (Px x t' Pnil). s. rw. eauto.
    exists (Px x t p'). s. rw. eauto.
  - eapply IHp; eauto.
    intros ? [? | [p' [VALp INp]]]; clarify; apply M1; right.
    exists (PM M p'). s. rw. eauto.
  - des_hyp; des; clarify.
    assert (P t).
    apply M1. eauto.
    exploit M2; eauto. ii.
    rewrite read_top in *.
    repeat des_hyp; clarify.
    eexists. split; eauto. s. split; eauto.
    eapply IHp; eauto.
    intros t' [? | [p' [VALp INp]]]; clarify; apply M1; right.
    exists (Pv (v_fn x e) p'). s. split; eauto.
    eexists. split; eauto. s. eauto.
    rewrite <- VAL in *. clarify.
Qed.

Fixpoint lift_m `{TotalOrder T} `{Eq aT}
  (inv_α : (T * aT) -> T) (t : T) (m : memory aT) :=
  match m with
  | [] => []
  | (t', Closure x e C) :: m' =>
    let t' := inv_α (t, t') in
    (t', Closure x e (lift_C inv_α t C)) ::
    lift_m inv_α t' m'
  end.

Lemma lift_m_lower_aux `{TotalOrder T} `{Eq aT} 
  (α : T -> aT) (inv_α : (T * aT) -> T) (SPECα : inv_α_spec α inv_α) :
  forall m t seen (LE : forall t', In t' seen -> leb t' t = true),
  trans_m_aux α (lift_m inv_α t m) seen = m.
Proof.
  induction m; ii; ss.
  repeat des_goal; clarify.
  - rewrite Inb_eq in *.
    exploit LE; eauto.
    specialize (SPECα t a0). des.
    rewrite <- not_le_lt in *.
    rewrite SPECα. ii; clarify.
  - specialize (SPECα t a0) as RR. des.
    rrw. rewrite lift_C_lower; eauto.
    rewrite IHm. reflexivity.
    ii; ss; des; clarify. solve_leb.
    lebt t. eauto. apply RR.
Qed.

Lemma lift_m_lower `{TotalOrder T} `{Eq aT} 
  (α : T -> aT) (inv_α : (T * aT) -> T) (SPECα : inv_α_spec α inv_α) :
  forall m t, trans_m α (lift_m inv_α t m) = m.
Proof.
  ii. apply lift_m_lower_aux; eauto.
Qed.

Lemma lift_m_disj `{TotalOrder T} `{Eq aT}
  (α : T -> aT) (inv_α : (T * aT) -> T) (SPECα : inv_α_spec α inv_α) :
  forall m t t', None <> read (lift_m inv_α t m) t' -> t << t'.
Proof.
  induction m; ii; ss.
  repeat des_hyp; clarify.
  - rewrite eqb_eq in *; clarify. apply SPECα.
  - exploit IHm; eauto.
    intros LT. rewrite <- not_le_lt.
    refl_bool. intros LE.
    assert (leb t t' = true).
    lebt (inv_α (t, a0)). apply SPECα. apply LT.
    assert (t = t'). apply leb_sym; eauto.
    clarify. destruct LT.
    assert (leb t' (inv_α (t', a0)) = true).
    apply SPECα.
    assert (t' = inv_α (t', a0)) as RR. apply leb_sym; eauto.
    rewrite <- RR in *. rewrite t_refl in *. clarify.
Qed.

Lemma app_disj_asame `{Eq T} `{Eq aT} (α : T -> aT) :
  forall m m' (DISJ : forall t, None <> read m t -> None = read m' t),
  asame (trans_m α (m ++ m')) (trans_m α m ++ trans_m α m').
Proof.
  ii.
  repeat rewrite aread_in. rewrite in_app_iff.
  repeat rewrite <- aread_in.
  repeat rewrite trans_m_aread.
  split; intros IN; des; clarify.
  rewrite read_top in *.
  des_hyp; clarify.
  - left. eexists. eexists. repeat (split; eauto).
  - right. eexists. eexists. repeat (split; eauto).
  - exists t'. exists v'. rewrite read_top.
    rrw. eauto.
  - exists t'. exists v'. rewrite read_top.
    rewrite disj_reflect in DISJ.
    exploit (DISJ t'). rrw. ii; clarify.
    ii. rrw. eauto.
Qed.

Definition trans_iso `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (init : T) φ φ'
  (C : dy_ctx TT) (m : memory TT) (aC : dy_ctx aT) (am : memory aT) :=
  match trans_iso_C inv_α C [] init ([||]) aC with
  | Some (CC, ϕ, tϕ) =>
    match trans_iso_m_aux α' inv_α φ φ' ϕ tϕ am [] [] m (length m) with
    | Fix m2' m' m1' ϕ' tϕ' =>
      Some (CC, m1' ++ lift_m inv_α tϕ' am, ϕ')
    | Unfix => None
    end
  | None => None
  end.

Lemma trans_iso_pre_post `{Eq TT} `{Eq aTT} `{TotalOrder T} `{Eq aT}
  (α' : TT -> aTT) (inv_α : (T * aT) -> T) (α : T -> aT) (SPECα : inv_α_spec α inv_α)
  (init : T) φ φ' (C : dy_ctx TT) (m : memory TT) 
  (aC : dy_ctx aT) (am : memory aT) 
  (ISO : aIso (Ctx (trans_C α' C)) (trans_m α' m) (Ctx aC) am φ φ') :
  match trans_iso α' inv_α init φ φ' C m aC am with
  | Some (CC, mm, ϕ) =>
    (forall t t' (IN : In (t, t') ϕ),
      Some t' = read_fst ϕ t /\
      Some t = read_snd ϕ t') /\
    trans_C α CC = aC /\
    asame (trans_m α mm) am /\
    (forall p (VALp : valid_path (Ctx C) m p),
      match pmap_fst ϕ p with
      | Some p' => valid_path (Ctx CC) mm p'
      | None => False
      end) /\
    (forall p (VALp : valid_path (Ctx CC) mm p),
      match pmap_snd ϕ p with
      | Some p' => valid_path (Ctx C) m p'
      | None => False
      end)
  | None => False
  end.
Proof.
  unfold trans_iso.
  assert (trans_iso_C_pre α' α φ φ' [] C ([||]) aC) as PREC.
  {
    split. s. destruct ISO as [ISO ELSE]. clear ELSE.
    rewrite <- check_iso_iso. rewrite iso_C_is_aiso_C.
    rewrite check_aiso_aiso.
    destruct ISO as [ISO ISO'].
    split; ss.
    ii. exploit (ISO p).
    eapply avpath_less_then_avpath_more with (a := []); eauto.
    ii; des. exploit (avpath_trans_empty φ p); eauto.
    ii. exploit (ISO' p').
    eapply avpath_less_then_avpath_more with (a := []); eauto.
    ii; des. exploit (avpath_trans_empty φ' p'); eauto.
    ii. destruct p; ss.
  }
  exploit (@trans_iso_C_pre_post TT _ aTT _ T _ _ aT); eauto.
  instantiate (1 := init). ii. ss.
  intros POSTC.
  unfold trans_iso_C_post in POSTC.
  des_hyp. repeat des_hyp; des; clarify.
  rewrite app_nil_r in *.
  assert (trans_iso_m_pre α' inv_α α φ φ' ϕ'' t C Cin' am [] [] m) as PREm.
  {
    split. ii; ss. split.
    ii. split; intros REACH; eauto.
    destruct REACH as [p [VALp INp]].
    exploit POSTC4; eauto. ii. des_hyp.
    exploit (@pmap_fst_read TT _ T); eauto.
    repeat (split; try solve [ii; ss | eauto]).
  }
  exploit (@trans_m_iso_pre_post TT _ aTT _ T _ _ aT); eauto.
  intros POSTm; ss. unfold trans_iso_m_pre in POSTm.
  des_hyp; des.
  split. ii. exploit POSTm7; eauto. ii; des. eauto.
  split; eauto.
  split. eapply asame_trans. apply app_disj_asame.
  - rewrite <- disj_reflect. ii.
    exploit lift_m_disj; eauto. intros LT.
    unfold equiv_snd_ϕ_m in *.
    destruct (read m' t0) eqn:CASE; eauto.
    destruct e as [xv ev Cv].
    symmetry in CASE.
    exploit (POSTm6 t0 Pnil xv ev Cv CASE); ss.
    des_goal; ss. symmetry in GDES.
    apply read_snd_in in GDES.
    exploit (POSTm7 t1 t0); eauto. ii; des.
    rewrite <- not_le_lt in *.
    rewrite LT in *. clarify.
  - rewrite lift_m_lower; eauto.
    split; ii; rewrite aread_in in *;
    rewrite in_app_iff in *; des; eauto.
    rewrite <- aread_in in *.
    rewrite trans_m_aread in *. des.
    exploit POSTm10; eauto. repeat rw. eauto.
  - split; ii.
    erewrite same_valid in VALp; eauto.
    exploit (separate_mem (fun t' => None <> read_fst ϕ t') p (Ctx C) m0 mbot).
    ii; des; clarify. rewrite POSTm2 in *. eauto.
    ii. symmetry. eauto. eauto.
    ii.
    exploit (@equiv_fst_ϕ_aux TT _ T); eauto.
    des_goal; ss. ii. apply vpath_less_then_vpath_more; eauto.
    exploit (separate_mem (fun t' => leb t' tϕ = true) p (Ctx Cin') m' (lift_m inv_α tϕ am)).
    intros t' [? | [p' [VALp' INp']]]; clarify.
    exploit (@equiv_snd_ϕ_aux TT _ T); eauto.
    des_goal; ss. ii.
    pose proof (@pmap_snd_read TT _ T _ ϕ p' p0 t' GDES INp').
    destruct (read_snd ϕ t') eqn:READ; ss.
    symmetry in READ. apply read_snd_in in READ.
    exploit (POSTm7 t0 t'); eauto. ii; des. eauto.
    ii. destruct (read (lift_m inv_α tϕ am) t0) eqn:READ; eauto.
    exploit lift_m_disj; eauto. rw. ii; clarify. intros LT.
    rewrite <- not_le_lt in *. rewrite LT in *. clarify. eauto.
    ii.
    exploit (@equiv_snd_ϕ_aux TT _ T); eauto.
    ii. des_hyp; clarify.
    rewrite same_valid. instantiate (1 := m0 ++ mbot).
    apply vpath_less_then_vpath_more. eauto. eauto.
Qed.

Definition derived_fst `{Eq T} `{Eq TT} (ϕ : list (T * TT)) (init' : TT) t :=
  match read_fst ϕ t with
  | Some t' => t'
  | None => init'
  end.

Definition derived_snd `{Eq T} `{Eq TT} (ϕ : list (T * TT)) (init : T) t' :=
  match read_snd ϕ t' with
  | Some t => t
  | None => init
  end.

Lemma derived_fst_map `{Eq T} `{Eq TT} (ϕ : list (T * TT)) (init' : TT) :
  forall p p' (MAP : pmap_fst ϕ p = Some p'),
  pmap (derived_fst ϕ init') p = p'.
Proof.
  induction p; ii; 
  unfold derived_fst in *; ss; repeat des_hyp; des; clarify;
  erewrite IHp; eauto.
Qed.

Lemma derived_snd_map `{Eq T} `{Eq TT} (ϕ : list (T * TT)) (init : T) :
  forall p p' (MAP : pmap_snd ϕ p = Some p'),
  pmap (derived_snd ϕ init) p = p'.
Proof.
  induction p; ii; 
  unfold derived_snd in *; ss; repeat des_hyp; des; clarify;
  erewrite IHp; eauto.
Qed.

Theorem concretization_preserves_equivalence `{Eq T} `{Eq aT} `{TotalOrder TT} `{Eq aTT}
  (α : T -> aT) (inv_α' : (TT * aTT) -> TT) (α' : TT -> aTT) (SPECα' : inv_α_spec α' inv_α')
  (init : T) (init' : TT) φ φ' 
  (C : dy_ctx T) (m : memory T) (aC : dy_ctx aTT) (am : memory aTT)
  (ISO : aIso (Ctx (trans_C α C)) (trans_m α m) (Ctx aC) am φ φ') :
  exists C' m' f f',
    trans_C α' C' = aC /\ asame (trans_m α' m') am /\
    iso (Ctx C) m (Ctx C') m' f f'.
Proof.
  exploit (@trans_iso_pre_post T _ aT _ TT _ _ aTT); eauto.
  instantiate (1 := init').
  intros HINT. repeat des_hyp; des.
  exists d. exists l0. exists (derived_fst l init'). exists (derived_snd l init).
  split; eauto. split; eauto.
  split; ss; ii.
  - exploit HINT2; eauto. ii; des_hyp.
    erewrite derived_fst_map; eauto.
    split; eauto. erewrite derived_snd_map; eauto.
    symmetry. rewrite <- pmap_ϕ_bij; eauto.
  - exploit HINT3; eauto. ii; des_hyp.
    erewrite derived_snd_map; eauto.
    split; eauto. erewrite derived_fst_map; eauto.
    symmetry. rewrite pmap_ϕ_bij; eauto.
Qed.
