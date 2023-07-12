From Simple Require Export ALinking.
From Simple Require Export Linking.

Module AL := ALinking.
Module CL := Linking.

Generalizable Variables BCT BAT ACT AAT.

Definition In_linked_t `{Conc.time BCT} `{Conc.time ACT}
  (final : BCT) (init : ACT) (t : @link BCT _ ACT _) :=
  match t with
  | L bf af =>
    if leb final bf then
      eqb final bf = true
    else
      eqb init af = true
  end.

Fixpoint In_linked_ctx `{Conc.time BCT} `{Conc.time ACT}
  (final : BCT) (init : ACT) (C : @dy_ctx (@link BCT _ ACT _)) :=
  match C with
  | [||] => True
  | dy_c_lam _ t C'
  | dy_c_lete _ t C' => In_linked_t final init t /\ In_linked_ctx final init C'
  | dy_c_letm _ C' C'' => In_linked_ctx final init C' /\ In_linked_ctx final init C''
  end.

Definition In_linked_v `{Conc.time BCT} `{Conc.time ACT}
  (final : BCT) (init : ACT) (v : @expr_value (@link BCT _ ACT _)) :=
  match v with
  | Closure _ _ C => In_linked_ctx final init C
  end.

Definition In_linked_mem `{Conc.time BCT} `{Conc.time ACT}
  (final : BCT) (init : ACT) (mem : (@link BCT _ ACT _) -> option (@expr_value (@link BCT _ ACT _))) :=
  forall t,
    match mem t with
    | Some v => In_linked_t final init t /\ In_linked_v final init v
    | None => True
    end.

Lemma bound_then_lift_in `{Conc.time BCT} `{Conc.time ACT}
  (final : BCT) (init : ACT) (C : @dy_ctx BCT) (BOUND : dy_ctx_bound C final) :
  In_linked_ctx final init (lift_ctx_bf init C).
Proof.
  induction C; eauto; destruct BOUND as [BOUND1 BOUND2].
  - simpl. replace (leb final tx) with false.
    split; try rewrite eqb_eq; eauto.
    symmetry. refl_bool. intros contra.
    assert (final = tx) as RR.
    apply leb_sym. assumption. apply BOUND1. subst.
    destruct BOUND1 as [? absurd]. rewrite t_refl in *. inversion absurd.
  - simpl. replace (leb final tx) with false.
    split; try rewrite eqb_eq; eauto.
    symmetry. refl_bool. intros contra.
    assert (final = tx) as RR.
    apply leb_sym. assumption. apply BOUND1. subst.
    destruct BOUND1 as [? absurd]. rewrite t_refl in *. inversion absurd.
  - simpl. split; eauto.
Qed.

Definition link_abs `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :=
  fun t =>
  match t with
  | L bf af =>
    if leb final bf then AF (αaf af) else BF (αbf bf)
  end.

Lemma trans_ctx_lift `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  let αlink := (link_abs final αbf αaf) in
  forall C (BOUND : dy_ctx_bound C final),
    trans_ctx αlink (lift_ctx_bf init C) =
    AL.lift_ctx_bf (trans_ctx αbf C).
Proof.
  induction C; simpl; eauto; intros [BOUND1 BOUND2].
  - replace (leb final tx) with false. rewrite IHC; eauto.
    symmetry. destruct BOUND1 as [LE NEQ].
    refl_bool. intros contra. assert (tx = final). apply leb_sym; eauto. subst.
    rewrite t_refl in NEQ. inversion NEQ.
  - replace (leb final tx) with false. rewrite IHC; eauto.
    symmetry. destruct BOUND1 as [LE NEQ].
    refl_bool. intros contra. assert (tx = final). apply leb_sym; eauto. subst.
    rewrite t_refl in NEQ. inversion NEQ.
  - rewrite IHC1; eauto. rewrite IHC2; eauto.
Qed.

Lemma trans_ctx_filter `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall C (INC : In_linked_ctx final init C),
  let αlink := (link_abs final αbf αaf) in
  let eqb' t t' := eqb (αlink t) (αlink t') in
  trans_ctx αaf (CL.filter_ctx_af final C) = AL.filter_ctx_af (trans_ctx αlink C).
Proof.
  induction C; simpl; eauto; intros [IN1 IN2].
  - destruct tx. simpl in *.
    destruct (leb final bf); simpl; eauto.
    rewrite IHC; eauto.
  - destruct tx. simpl in *.
    destruct (leb final bf); simpl; eauto.
    rewrite IHC; eauto.
  - rewrite IHC1; eauto. rewrite IHC2; eauto.
Qed.

Lemma In_linked_ctx_prefix `{Conc.time BCT} `{Conc.time ACT} eqb
  (final : BCT) (init : ACT) :
  forall (Cout C : @dy_ctx (@link BCT _ ACT _))
         (INC : In_linked_ctx final init C),
  In_linked_ctx final init (delete_prefix eqb Cout C).
Proof.
  induction Cout; intros; eauto.
  - destruct C; eauto. simpl.
    destruct (eq_eid x x0) eqn:EQid;
    destruct (eqb tx tx0) eqn:EQt; eauto.
    simpl in *. apply IHCout; apply INC.
  - destruct C; eauto. simpl.
    destruct (eq_eid x x0) eqn:EQid;
    destruct (eqb tx tx0) eqn:EQt; eauto.
    simpl in *. apply IHCout; apply INC.
  - destruct C; eauto. simpl.
    destruct (eq_mid M M0) eqn:EQid;
    destruct (eq_ctx eqb Cout1 C1) eqn:EQC; eauto.
    simpl in *. apply IHCout2; apply INC.
Qed.

Lemma In_linked_ctx_map_aux `{Conc.time BCT} `{Conc.time ACT} eqb
  (final : BCT) (init : ACT) :
  forall n (C Cout : @dy_ctx (@link BCT _ ACT _)) (LE : dy_level C <= n)
         (INC : In_linked_ctx final init C),
  In_linked_ctx final init (delete_map eqb Cout C).
Proof.
  induction n; intros; induction C; try reflexivity; try (inversion LE; fail).
  - rewrite delete_map_red_lam. simpl. simpl in INC.
    split; try apply INC. apply IHC; try apply INC.
    simpl in LE. nia.
  - rewrite delete_map_red_lete. simpl. simpl in INC.
    split; try apply INC. apply IHC; try apply INC.
    simpl in LE. nia.
  - rewrite delete_map_red_letm. simpl. simpl in INC.
    split. apply IHn. simpl in *.
    etransitivity. apply delete_prefix_dec. nia.
    apply In_linked_ctx_prefix. apply INC.
    apply IHC2. simpl in LE. nia. apply INC.
Qed.

Lemma In_linked_ctx_delete `{Conc.time BCT} `{Conc.time ACT} eqb
  (final : BCT) (init : ACT) :
  forall (Cout C : @dy_ctx (@link BCT _ ACT _))
         (INC : In_linked_ctx final init C),
  In_linked_ctx final init (delete_ctx eqb Cout C).
Proof.
  intros. unfold delete_ctx.
  apply In_linked_ctx_map_aux with (n := dy_level C).
  apply delete_prefix_dec. apply In_linked_ctx_prefix. eauto.
Qed.

Lemma trans_ctx_link `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (Cout : @dy_ctx BCT) (BOUND : dy_ctx_bound Cout final)
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall C (INC : In_linked_ctx final init C),
  let αlink := (link_abs final αbf αaf) in
  let eqb' t t' := eqb (αlink t) (αlink t') in
  trans_ctx αaf
    (CL.filter_ctx_af final (delete_ctx eqb' (CL.lift_ctx_bf init Cout) C)) =
  AL.filter_ctx_af
    (delete_ctx eqb (AL.lift_ctx_bf (trans_ctx αbf Cout)) (trans_ctx αlink C)).
Proof.
  intros.
  rewrite <- trans_ctx_lift with (final := final) (init := init) (αaf := αaf); eauto.
  rewrite <- trans_ctx_delete. rewrite trans_ctx_filter with (init := init) (αbf := αbf). eauto.
  apply In_linked_ctx_delete. eauto.
Qed.

Lemma In_map_l {T T'} :
  forall (l : list T) x (f : T -> T'),
    In x (map f l) <-> exists x', x = f x' /\ In x' l.
Proof.
  induction l; simpl; intros.
  - split; intros contra; try contradict.
    destruct contra as [x' contra]. apply contra.
  - split; intros IN.
    + destruct IN as [L | R].
      exists a. split; subst; eauto.
      rewrite IHl in R.
      destruct R as [x' [EQ IN]].
      exists x'. eauto.
    + destruct IN as [x' [EQ [L | R]]].
      left. subst; eauto.
      right. rewrite IHl. exists x'. eauto.
Qed.

Lemma trans_mem_link `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (Cout : @dy_ctx BCT) (BOUND : dy_ctx_bound Cout final)
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) (PRES : preserve_tick αaf) :
  forall mem abs_mem
    (EQ : trans_mem (link_abs final αbf αaf) mem abs_mem)
    (INm : In_linked_mem final init mem),
  let αlink := (link_abs final αbf αaf) in
  trans_mem αaf
  (CL.filter_mem_af final
     (CL.delete_ctx_mem αlink (CL.lift_ctx_bf init Cout) mem))
  (AL.filter_mem_af
     (AL.delete_ctx_mem (AL.lift_ctx_bf (trans_ctx αbf Cout))
        abs_mem)).
Proof.
  intros. subst αlink.
  red. intros.
  unfold AL.delete_ctx_mem. unfold AL.filter_mem_af.
  unfold CL.delete_ctx_mem. unfold CL.filter_mem_af.
  rewrite In_map_l.
  split; intros IN.
  - destruct IN as [v [EQv IN]].
    rewrite In_map_l in IN.
    destruct IN as [v' [EQv' IN]].
    red in EQ. specialize (EQ (AL.AF abs_t) v').
    rewrite EQ in IN.
    destruct IN as [t [v'' [TRANSv [TRANSt ACCESS]]]].
    specialize (INm t). rewrite ACCESS in INm.
    destruct INm as [INt INv].
    destruct t. simpl in INt. simpl in TRANSt.
    destruct (leb final bf); try (inversion TRANSt; fail).
    rewrite eqb_eq in INt. subst.
    exists af. rewrite ACCESS.
    exists (CL.filter_v_af bf
       (delete_ctx_v
          (fun t t' : link =>
           eqb (link_abs bf αbf αaf t)
             (link_abs bf αbf αaf t'))
          (CL.lift_ctx_bf init Cout) v'')).
    repeat split; try (inversion TRANSt; eauto; fail).
    destruct v''. simpl.
    rewrite <- trans_ctx_lift with (final := bf) (init := init) (αaf := αaf); eauto.
    assert (delete_ctx AL.link_eqb
        (trans_ctx (link_abs bf αbf αaf) (lift_ctx_bf init Cout))
        (trans_ctx (link_abs bf αbf αaf) C) =
        trans_ctx (link_abs bf αbf αaf) 
          (delete_ctx (fun t t' => AL.link_eqb ((link_abs bf αbf αaf) t) ((link_abs bf αbf αaf) t'))
            (lift_ctx_bf init Cout) C)) as RR.
    { symmetry. apply (@trans_ctx_delete _ (@AL.link BAT AAT) _ AL.link_eq). }
    rewrite RR. rewrite trans_ctx_filter with (init := init) (αbf := αbf). eauto.
    apply In_linked_ctx_delete. eauto.
  - destruct IN as [af [v [TRANSv [TRANSt SOME]]]].
    destruct (mem (CL.L final af)) eqn:ACCESS; try (inversion SOME; fail).
    subst. red in EQ.
    destruct e. simpl in *.
    inversion SOME. subst.
    exists (Closure x e
      (delete_ctx ALinking.link_eqb
        (AL.lift_ctx_bf (trans_ctx αbf Cout))
        (trans_ctx (link_abs final αbf αaf) C))).
    split. simpl.
    rewrite <- trans_ctx_lift with (final := final) (init := init) (αaf := αaf); eauto.
    assert (delete_ctx AL.link_eqb
        (trans_ctx (link_abs final αbf αaf) (lift_ctx_bf init Cout))
        (trans_ctx (link_abs final αbf αaf) C) =
        trans_ctx (link_abs final αbf αaf) 
          (delete_ctx (fun t t' => AL.link_eqb ((link_abs final αbf αaf) t) ((link_abs final αbf αaf) t'))
            (lift_ctx_bf init Cout) C)) as RR.
    { symmetry. apply (@trans_ctx_delete _ (@AL.link BAT AAT) _ AL.link_eq). }
    rewrite RR. rewrite trans_ctx_filter with (init := init) (αbf := αbf). eauto.
    apply In_linked_ctx_delete. specialize (INm (CL.L final af)). rewrite ACCESS in INm. apply INm.
    rewrite In_map_l.
    exists (Closure x e (trans_ctx (link_abs final αbf αaf) C)).
    split. eauto.
    rewrite EQ.
    exists (CL.L final af).
    exists (Closure x e C).
    split; eauto. split; eauto. simpl. rewrite leb_refl. eauto.
Qed.

Theorem link_abs_pres `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (Cout : @dy_ctx BCT) (BOUND : dy_ctx_bound Cout final)
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) (PRES : preserve_tick αaf) :
  forall (af : ACT) C mem x v abs_mem
    (EQ : trans_mem (link_abs final αbf αaf) mem abs_mem)
    (INm : In_linked_mem final init mem)
    (INC : In_linked_ctx final init C)
    (INv : In_linked_v final init v),
  let αlink := (link_abs final αbf αaf) in
  αlink (CL.link_tick αlink final init Cout C (ST mem (L final af)) x v) =
  AL.link_tick (trans_ctx αbf Cout) (trans_ctx αlink C) (Abs.ST abs_mem (AF (αaf af))) x (trans_v αlink v).
Proof.
  intros. simpl. rewrite leb_refl. simpl. rewrite leb_refl.
  assert (αaf
     (tick
        (CL.filter_ctx_af final
           (delete_ctx (fun t t' : CL.link =>
               ALinking.link_eqb (αlink t) (αlink t'))
               (CL.lift_ctx_bf init Cout) C))
        (ST
           (CL.filter_mem_af final
              (CL.delete_ctx_mem αlink (CL.lift_ctx_bf init Cout) mem)) af) x
        (CL.filter_v_af final
           (delete_ctx_v (fun t t' : CL.link =>
               ALinking.link_eqb (αlink t) (αlink t'))
              (CL.lift_ctx_bf init Cout) v))) =
      Abstract.tick
     (AL.filter_ctx_af
        (delete_ctx AL.link_eqb (AL.lift_ctx_bf (trans_ctx αbf Cout))
           (trans_ctx αlink C)))
     (Abstract.ST
        (AL.filter_mem_af
           (AL.delete_ctx_mem (AL.lift_ctx_bf (trans_ctx αbf Cout))
              abs_mem)) (αaf af)) x
     (AL.filter_v_af
        (delete_ctx_v AL.link_eqb (AL.lift_ctx_bf (trans_ctx αbf Cout))
           (trans_v αlink v)))) as RR.
  { 
    apply PRES. simpl. split. apply trans_ctx_link; eauto.
    split; try reflexivity. apply trans_mem_link; eauto.
    destruct v; simpl in *.
    replace (trans_ctx αaf
      (CL.filter_ctx_af final
        (delete_ctx
           (fun t t' : CL.link =>
            ALinking.link_eqb (αlink t) (αlink t'))
           (CL.lift_ctx_bf init Cout) C0))) with
      (AL.filter_ctx_af
      (delete_ctx AL.link_eqb (AL.lift_ctx_bf (trans_ctx αbf Cout))
        (trans_ctx αlink C0))). eauto.
    symmetry. apply trans_ctx_link; eauto.  
  }
  rewrite RR. eauto.
Qed.

