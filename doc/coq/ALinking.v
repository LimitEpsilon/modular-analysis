From MODULAR Require Export Abstract.
Require Export Coq.Logic.FunctionalExtensionality.

Generalizable Variables T.

Definition inject_ctx_mem `{Eq T} (Cout : @dy_ctx T) (mem : T -> list expr_value) :=
  fun t => map (inject_ctx_v Cout) (mem t).

Definition delete_ctx_mem `{Eq T} (Cout : @dy_ctx T) (mem : T -> list expr_value) :=
  fun t => map (delete_ctx_v Cout) (mem t).

Lemma delete_ctx_mem_eq :
  forall `{Eq T} (Cout : @dy_ctx T) (mem : T -> list expr_value),
         delete_ctx_mem Cout (inject_ctx_mem Cout mem) = mem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold inject_ctx_mem. unfold delete_ctx_mem.
  remember (mem x) as l. clear Heql x mem. revert Cout.
  induction l; try reflexivity. intros.
  destruct a; simpl.
  rewrite delete_inject_eq.
  rewrite IHl. reflexivity.
Qed.

Definition delete_update `{time T} (Cout : @dy_ctx T) :=
  fun C st x v =>
    match st with
    | ST mem t =>
      update (delete_inject Cout C)
             (ST (delete_ctx_mem Cout mem) t)
             x (delete_ctx_v Cout v)
    end.

#[export] Instance delete_time `{time T} (Cout : @dy_ctx T) : time :=
  {
    update := delete_update Cout
  }.

Lemma delete_update_eq `{time T} (Cout : @dy_ctx T) :
  forall C mem t x v,
    delete_update Cout (Cout<|C|>) (ST (inject_ctx_mem Cout mem) t) x (inject_ctx_v Cout v) =
    update C (ST mem t) x v.
Proof.
  intros. destruct v. unfold inject_ctx_v.
  unfold delete_update. simpl.
  rewrite delete_inject_eq. rewrite delete_ctx_mem_eq.
  rewrite delete_inject_eq. reflexivity.
Qed.

Lemma plugin_map_assoc :
  forall `{Eq T} (Cout C C' : @dy_ctx T),
    (map_inject Cout C) [|map_inject Cout C'|] = (map_inject Cout (C [|C'|])).
Proof.
  intros. revert Cout C'. induction C; intros; simpl; eauto; try rewrite IHC; try rewrite IHC2; eauto.
Qed.

Lemma plugin_inject_assoc :
  forall `{Eq T} (Cout C C' : @dy_ctx T),
    (Cout <| C |>)[| map_inject Cout C' |] = (Cout <|C[|C'|]|>).
Proof.
  intros. unfold inject_ctx. rewrite <- c_plugin_assoc.
  rewrite plugin_map_assoc. eauto.
Qed.

Lemma inject_update_m_eq :
  forall `{Eq T} t x e mem (Cout C : @dy_ctx T),
  (t !#-> Closure x e (Cout <| C |>); inject_ctx_mem Cout mem) =
            inject_ctx_mem Cout (t !#-> Closure x e C; mem).
Proof.
  intros. apply functional_extensionality.
  intros. unfold update_m. unfold inject_ctx_mem.
  destruct (eqb x0 t); eauto.
Qed.

Lemma delete_eval_eq {T} `{ET : Eq T} `{TT : @time T ET} (Cout : @dy_ctx T) :
  forall C st e v st'
         (EVAL : @EvalR T ET TT C st e v st'),
    let inject_v :=
      match v with
      | EVal (Closure x_v e_v C_v) => EVal (Closure x_v e_v (Cout<|C_v|>))
      | MVal C_v => MVal (Cout<|C_v|>)
      end in
    let inject_st :=
      match st with
      | ST mem t => ST (inject_ctx_mem Cout mem) t
      end in
    let inject_st' :=
      match st' with
      | ST mem' t' => ST (inject_ctx_mem Cout mem') t'
      end in
    @EvalR T ET (@delete_time T ET TT Cout)
      (Cout<|C|>) inject_st e inject_v inject_st'.
Proof.
  intros. induction EVAL;
  try destruct v; try destruct st; try destruct st'; try destruct st'';
  try (destruct inject_v eqn:INJv; inversion INJv; subst);
  try (destruct inject_st eqn:INJst; inversion INJst; subst);
  try (destruct inject_st' eqn:INJst'; inversion INJst'; subst); eauto.
  - inversion STATE; subst.
    eapply Eval_var_e; eauto.
    pose proof (inject_ctx_addr_x x Cout C) as RR.
    rewrite <- ADDR in RR. symmetry. apply RR.
    unfold inject_ctx_mem. 
    remember (mem0 addr) as l.
    clear Heql C mem0 x addr t0 inject_st' INJst' STATE inject_st INJst ADDR inject_v INJv.
    revert Cout x0 e C0 ACCESS. induction l; simpl; intros; eauto.
    destruct ACCESS as [L | R].
    left. rewrite L. simpl. eauto.
    right. apply IHl. eauto.
  - destruct st_v. destruct arg.
    eapply Eval_app. apply IHEVAL1. apply IHEVAL2.
    pose proof (delete_update_eq Cout C mem t x (Closure x1 e3 C1)) as RR.
    simpl in *. rewrite RR. clear RR.
    rewrite inject_update_m_eq.
    replace (dy_c_lam x t ([||])) with (map_inject Cout (dy_c_lam x t ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. eauto.
  - pose proof (inject_ctx_ctx_M M Cout C) as RR. 
    rewrite <- ACCESS in RR.
    eapply Eval_var_m; eauto.
  - eapply Eval_lete; eauto.
    pose proof (delete_update_eq Cout C mem t x (Closure x0 e0 C0)) as RR.
    simpl in *. rewrite RR. clear RR.
    rewrite inject_update_m_eq.
    replace (dy_c_lete x t ([||])) with (map_inject Cout (dy_c_lete x t ([||]))) by reflexivity.
    rewrite plugin_inject_assoc. eauto.
  - eapply Eval_letm; eauto.
    assert ((Cout <| C |>) [|dy_c_letm M (Cout <| C' |>) ([||])|] =
            (Cout <| (C [|dy_c_letm M C' ([||])|]) |>)) as RR. 
    { rewrite <- plugin_inject_assoc. simpl. eauto. } 
    rewrite RR. clear RR. simpl in *. exact IHEVAL2.
Qed.
