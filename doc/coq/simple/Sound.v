From Simple Require Export Equiv.

Module Abs := Abstract.
Module Conc := Concrete.

Generalizable Variables CT AT.

Definition preserve_tick `{Conc.time CT} `{Abs.time AT} (α : CT -> AT) :=
  forall C m t x v,
  let abs_C := trans_C α C in
  let abs_m := trans_m α m in
  let abs_t := α t in
  let abs_v := trans_v α v in
  α (Conc.tick C m t x v) = 
    Abs.tick abs_C abs_m abs_t x abs_v.

Lemma sound_eval `{Conc.time CT} `{Abs.time AT} (α : CT -> AT) (PRES : preserve_tick α) :
  forall e C m t ρ (EVAL : {|(Cf e C m t) ~> ρ|})
    (BOUND : time_bound_ρ (Cf e C m t)),
  let abs_C := trans_C α C in
  let abs_m := trans_m α m in
  let abs_t := α t in
  {|(Cf e abs_C abs_m abs_t) ~#> (trans_ρ α ρ)|}.
Proof.
  intros. remember (Cf e C m t) as cf.
  ginduction EVAL; ii;
  repeat match goal with
  | H : {|(Rs _ _ _) ~> _|} |- _ => inversion H
  | x := _ |- _ => subst x
  end; clarify;
  try match goal with
  | ADDR : addr_x ?C ?x = Some ?addr,
    ACCESS : read ?m ?t = Some ?v |- _ =>
    let RR := fresh "RR" in
    pose proof (trans_C_addr α C x) as RR;
    rewrite ADDR in RR;
    assert (In (trans_v α v) (aread (trans_m α m) (α addr)));
    first [rewrite trans_m_aread;
      exists addr; exists v;
      symmetry in ACCESS; eauto|ss; eauto]
  | ACCESS : ctx_M ?C ?M = Some ?CM |- _ =>
    pose proof (trans_C_ctx_M C α M CM ACCESS); ss; eauto
  end;
  repeat match goal with
  | H : {| (Cf ?e ?C ?m ?t) ~> (Rs ?V ?m' ?t') |} |- _ =>
    lazymatch goal with
    | _ : leb t t' = true |- _ => fail
    | _ =>
      let INC := fresh "INC" in
      let BD := fresh "BD" in
      apply time_increase in H as INC;
      apply time_bound in H as BD;
      try solve [ss; eauto]
    end
  end;
  try match goal with
  | |- {| _ ~#> _ |} =>
    try exploit IHEVAL1; eauto;
    try exploit IHEVAL2; eauto;
    try exploit IHEVAL3; eauto;
    ii; ss;
    try rewrite trans_m_update in *;
    try rewrite PRES in *; des; eauto
  end; ss; des;
  try solve [split; eauto using relax_ctx_bound];
  try match goal with
  | |- context [tick _ _ ?t _ _] =>
    split; try (apply time_bound_tick; assumption);
    red; ii; ss; des; clarify;
    try match goal with
    | _ => apply tick_lt
    | H : supp_C ?C_f _, BD : time_bound_C ?C_f _ |- _ =>
      apply BD in H; eapply relax_p_bound;
      first [eassumption | lebt t]
    end
  | _ => split; first [assumption | red; ii; ss; des; clarify]
  end;
  match goal with
  | BD : time_bound_C ?C _, _ : supp_C ?C _ |- _ =>
    solve [apply BD; eauto]
  | BD : time_bound_C ?C _, H : supp_C ?C _ |- _ =>
    apply BD in H;
    solve [eapply relax_p_bound; eassumption]
  | _ => apply time_bound in EVAL2; ss; des;
    try match goal with
    | BD : time_bound_v ?v _, H : supp_v ?v _ |- _ =>
      destruct v; ss; apply BD in H;
      eapply relax_p_bound; first [eassumption | apply tick_lt]
    | BD : time_bound_m ?m _, H : supp_m ?m _ |- _ =>
      apply BD in H;
      eapply relax_p_bound; first [eassumption | apply tick_lt]
    | _ => solve [split; eauto using relax_ctx_bound]
    end
  end.
Qed.
