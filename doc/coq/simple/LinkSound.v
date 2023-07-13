From Simple Require Export ALinking.
From Simple Require Export Linking.

Module AL := ALinking.
Module CL := Linking.

Generalizable Variables BCT BAT ACT AAT.

Definition link_abs `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :=
  fun t : link final init =>
  match t with
  | L _ _ bf af _ =>
    if eqb final bf then AF (αaf af) else BF (αbf bf)
  end.

Lemma trans_ctx_lift `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  let αlink := (link_abs final init αbf αaf) in
  forall C (BOUND : dy_ctx_bound C final),
    trans_ctx αlink (lift_ctx_bf final init C) =
    AL.lift_ctx_bf (trans_ctx αbf C).
Proof.
  induction C; simpl; eauto; intros [BOUND1 BOUND2].
  - replace (eqb final tx) with false. rewrite IHC; eauto.
    symmetry. destruct BOUND1 as [LE NEQ].
    refl_bool. intros contra. rewrite eqb_eq in contra. subst.
    rewrite t_refl in NEQ. inversion NEQ.
  - rewrite IHC1; eauto. rewrite IHC2; eauto.
Qed.

Lemma trans_ctx_filter `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall C,
  let αlink := (link_abs final init αbf αaf) in
  let eqb' t t' := eqb (αlink t) (αlink t') in
  trans_ctx αaf (CL.filter_ctx_af final init C) = AL.filter_ctx_af (trans_ctx αlink C).
Proof.
  induction C; simpl; eauto.
  - destruct tx. simpl in *.
    destruct (eqb final bf); simpl; eauto.
    rewrite IHC; eauto.
  - rewrite IHC1; eauto. rewrite IHC2; eauto.
Qed.

Lemma trans_ctx_link `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (Cout : @dy_ctx BCT) (BOUND : dy_ctx_bound Cout final)
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) :
  forall C,
  let αlink := (link_abs final init αbf αaf) in
  let eqb' t t' := eqb (αlink t) (αlink t') in
  trans_ctx αaf
    (CL.filter_ctx_af final init (delete_ctx eqb' (CL.lift_ctx_bf final init Cout) C)) =
  AL.filter_ctx_af
    (delete_ctx eqb (AL.lift_ctx_bf (trans_ctx αbf Cout)) (trans_ctx αlink C)).
Proof.
  intros.
  rewrite <- trans_ctx_lift with (final := final) (init := init) (αaf := αaf); eauto.
  rewrite <- trans_ctx_delete. rewrite trans_ctx_filter with (init := init) (αbf := αbf). eauto.
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
    (EQ : trans_mem (link_abs final init αbf αaf) mem abs_mem),
  let αlink := (link_abs final init αbf αaf) in
  trans_mem αaf
  (CL.filter_mem_af final init
     (CL.delete_ctx_mem αlink (CL.lift_ctx_bf final init Cout) mem))
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
    destruct t. simpl in TRANSt.
    destruct (eqb final bf) eqn:EQt; try (inversion TRANSt; fail).
    rewrite eqb_eq in EQt. subst.
    exists af. replace (CL.LINK_pf_af bf init af) with LINK; try apply proof_irrelevance.
    rewrite ACCESS.
    exists (CL.filter_v_af bf init
       (delete_ctx_v
          (fun t t' : link bf init =>
           eqb (link_abs bf init αbf αaf t)
             (link_abs bf init αbf αaf t'))
          (CL.lift_ctx_bf bf init Cout) v'')).
    repeat split; try (inversion TRANSt; eauto; fail).
    destruct v''. simpl.
    rewrite <- trans_ctx_lift with (final := bf) (init := init) (αaf := αaf); eauto.
    assert (delete_ctx AL.link_eqb
        (trans_ctx (link_abs bf _ αbf αaf) (lift_ctx_bf _ init Cout))
        (trans_ctx (link_abs bf _ αbf αaf) C) =
        trans_ctx (link_abs bf _ αbf αaf) 
          (delete_ctx (fun t t' => AL.link_eqb ((link_abs bf _ αbf αaf) t) ((link_abs bf _ αbf αaf) t'))
            (lift_ctx_bf _ init Cout) C)) as RR.
    { symmetry. apply (@trans_ctx_delete _ (@AL.link BAT AAT) _ AL.link_eq). }
    rewrite RR. rewrite trans_ctx_filter with (init := init) (αbf := αbf). eauto.
  - destruct IN as [af [v [TRANSv [TRANSt SOME]]]].
    destruct (mem (CL.L _ _ _ af _)) eqn:ACCESS; try (inversion SOME; fail).
    subst. red in EQ.
    destruct e. simpl in *.
    inversion SOME. subst.
    exists (Closure x e
      (delete_ctx ALinking.link_eqb
        (AL.lift_ctx_bf (trans_ctx αbf Cout))
        (trans_ctx (link_abs final init αbf αaf) C))).
    split. simpl.
    rewrite <- trans_ctx_lift with (final := final) (init := init) (αaf := αaf); eauto.
    assert (delete_ctx AL.link_eqb
        (trans_ctx (link_abs final _ αbf αaf) (lift_ctx_bf _ init Cout))
        (trans_ctx (link_abs final _ αbf αaf) C) =
        trans_ctx (link_abs final _ αbf αaf) 
          (delete_ctx (fun t t' => AL.link_eqb ((link_abs final _ αbf αaf) t) ((link_abs final _ αbf αaf) t'))
            (lift_ctx_bf _ init Cout) C)) as RR.
    { symmetry. apply (@trans_ctx_delete _ (@AL.link BAT AAT) _ AL.link_eq). }
    rewrite RR. rewrite trans_ctx_filter with (init := init) (αbf := αbf). eauto.
    rewrite In_map_l.
    exists (Closure x e (trans_ctx (link_abs final _ αbf αaf) C)).
    split. eauto.
    rewrite EQ.
    exists (CL.L _ _ final af (CL.LINK_pf_af final init af)).
    exists (Closure x e C).
    split; eauto. split; eauto. simpl. rewrite t_refl. eauto.
Qed.

Theorem link_abs_pres `{Conc.time BCT} `{Abs.time BAT} `{Conc.time ACT} `{Abs.time AAT}
  (final : BCT) (init : ACT) (Cout : @dy_ctx BCT) (BOUND : dy_ctx_bound Cout final)
  (αbf : BCT -> BAT) (αaf : ACT -> AAT) (PRES : preserve_tick αaf) :
  forall (af : ACT) C mem x v abs_mem
    (EQ : trans_mem (link_abs final init αbf αaf) mem abs_mem),
  let αlink := (link_abs final init αbf αaf) in
  αlink (CL.link_tick final init Cout αlink C (ST mem (L _ _ final af (LINK_pf_af _ _ af))) x v) =
  AL.link_tick (trans_ctx αbf Cout) (trans_ctx αlink C) (Abs.ST abs_mem (AF (αaf af))) x (trans_v αlink v).
Proof.
  intros. simpl. rewrite t_refl. simpl. rewrite t_refl.
  assert (αaf
     (tick
        (CL.filter_ctx_af final _
           (delete_ctx (fun t t' : CL.link final init =>
               ALinking.link_eqb (αlink t) (αlink t'))
               (CL.lift_ctx_bf _ init Cout) C))
        (ST
           (CL.filter_mem_af final _
              (CL.delete_ctx_mem αlink (CL.lift_ctx_bf _ init Cout) mem)) af) x
        (CL.filter_v_af final _
           (delete_ctx_v (fun t t' : CL.link final init =>
               ALinking.link_eqb (αlink t) (αlink t'))
              (CL.lift_ctx_bf _ init Cout) v))) =
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
      (CL.filter_ctx_af final init
        (delete_ctx
           (fun t t' : CL.link final init =>
            ALinking.link_eqb (αlink t) (αlink t'))
           (CL.lift_ctx_bf final init Cout) C0))) with
      (AL.filter_ctx_af
      (delete_ctx AL.link_eqb (AL.lift_ctx_bf (trans_ctx αbf Cout))
        (trans_ctx αlink C0))). eauto.
    symmetry. apply trans_ctx_link; eauto.  
  }
  rewrite RR. eauto.
Qed.

