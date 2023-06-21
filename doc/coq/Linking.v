From MODULAR Require Export Sound.
Require Export Coq.Logic.FunctionalExtensionality.

(* before, after *)
Generalizable Variables BT AT.

Inductive link `{Eq BT} `{Eq AT} :=
  | BF (t : BT)
  | AF (t : AT)
.

Definition link_eqb `{EB : Eq BT} `{EA : Eq AT} 
  (t1 : @link BT EB AT EA) (t2 : @link BT EB AT EA) :=
  match t1, t2 with
  | BF t1, BF t2 => eqb t1 t2
  | AF t1, AF t2 => eqb t1 t2
  | _, _ => false  
  end.

Definition link_leb `{EB : Eq BT} `{@OrderT BT EB} `{EA : Eq AT} `{@OrderT AT EA} 
  (t1 : @link BT EB AT EA) (t2 : @link BT EB AT EA) :=
  match t1, t2 with
  | BF t1, BF t2 => leb t1 t2
  | AF t1, AF t2 => leb t1 t2
  | BF t1, AF t2 => true
  | AF t1, BF t2 => false
  end.

Lemma link_leb_refl : 
  forall 
    `{EB : Eq BT} `{EA : Eq AT}
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA} t,
  @link_leb BT EB OB AT EA OA t t = true.
Proof.
  intros. destruct t; apply leb_refl.
Qed.

Lemma link_leb_trans :
  forall 
    `{EB : Eq BT} `{EA : Eq AT}
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
    t t' t''
    (LE : @link_leb BT EB OB AT EA OA t t' = true)
    (LE' : @link_leb BT EB OB AT EA OA t' t'' = true),
  link_leb t t'' = true.
Proof.
  intros.
  destruct t; destruct t'; destruct t'';
  simpl in *;
  try apply leb_trans with (t' := t0);
  try inversion LE;
  try inversion LE';
  eauto.
Qed.

Lemma link_leb_sym :
  forall 
    `{EB : Eq BT} `{EA : Eq AT}
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA} t t'
    (LE : @link_leb BT EB OB AT EA OA t t' = true)
    (LE' : @link_leb BT EB OB AT EA OA t' t = true),
  t = t'.
Proof.
  intros.
  destruct t; destruct t';
  simpl in *;
  try inversion LE;
  try inversion LE';
  assert (t = t0) as RR;
  try apply leb_sym; eauto;
  rewrite RR; eauto.
Qed.

Lemma link_eqb_eq :
  forall `{EB : Eq BT} `{EA : Eq AT} t t',
  @link_eqb BT EB AT EA t t' = true <-> t = t'.
Proof.
  intros.
  destruct t; destruct t';
  simpl in *;
  split; intro EQ;
  try rewrite eqb_eq in *;
  try inversion EQ;
  subst; eauto.
Qed.

Lemma link_eqb_neq :
  forall `{EB : Eq BT} `{EA : Eq AT} t t',
  @link_eqb BT EB AT EA t t' = false <-> t <> t'.
Proof.
  intros.
  destruct t; destruct t';
  simpl in *;
  split; intro NEQ;
  try rewrite eqb_neq in *;
  try inversion NEQ;
  subst; unfold not in *;
  try intros contra;
  try apply NEQ;
  try inversion contra;
  eauto.
Qed.

#[export] Instance LinkEq `{EB : Eq BT} `{EA : Eq AT} :
  Eq (@link BT EB AT EA) :=
{
  eqb := link_eqb;
  eqb_eq := link_eqb_eq;
  eqb_neq := link_eqb_neq
}.

#[export] Instance LinkOrderT `{EB : Eq BT} `{EA : Eq AT} `{OB : @OrderT BT EB} `{OA : @OrderT AT EA} :
  @OrderT (@link BT EB AT EA) LinkEq :=
  {
    leb := link_leb;
    leb_refl := link_leb_refl;
    leb_trans := link_leb_trans;
    leb_sym := link_leb_sym
  }.

Fixpoint filter_ctx_bf
  `{EB : Eq BT} `{EA : Eq AT}
  (C : @dy_ctx (@link BT EB AT EA)) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' =>
    match t with
    | AF t => filter_ctx_bf C'
    | BF t => dy_c_lam x t (filter_ctx_bf C')
    end
  | dy_c_lete x t C' =>
    match t with
    | AF t => filter_ctx_bf C'
    | BF t => dy_c_lete x t (filter_ctx_bf C')
    end
  | dy_c_letm M C' C'' =>
    dy_c_letm M (filter_ctx_bf C') (filter_ctx_bf C'')
  end.

Fixpoint filter_ctx_af
  `{EB : Eq BT} `{EA : Eq AT}
  (C : @dy_ctx (@link BT EB AT EA)) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' =>
    match t with
    | AF t => dy_c_lam x t (filter_ctx_af C')
    | BF t => filter_ctx_af C'
    end
  | dy_c_lete x t C' =>
    match t with
    | AF t => dy_c_lete x t (filter_ctx_af C')
    | BF t => filter_ctx_af C'
    end
  | dy_c_letm M C' C'' =>
    dy_c_letm M (filter_ctx_af C') (filter_ctx_af C'')
  end.

Definition filter_mem_bf
  `{EB : Eq BT} `{EA : Eq AT}
  (mem : (@link BT EB AT EA) -> option (@expr_value (@link BT EB AT EA))) :=
  fun t =>
    match mem (BF t) with
    | Some (Closure x e C) => Some (Closure x e (filter_ctx_bf C))
    | None => None
    end.

Definition filter_mem_af
  `{EB : Eq BT} `{EA : Eq AT}
  (mem : (@link BT EB AT EA) -> option (@expr_value (@link BT EB AT EA))) :=
  fun t =>
    match mem (AF t) with
    | Some (Closure x e C) => Some (Closure x e (filter_ctx_af C))
    | None => None
    end.

Definition filter_v_bf 
  `{EB : Eq BT} `{EA : Eq AT}
  (v : @expr_value (@link BT EB AT EA)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_bf C)
  end.

Definition filter_v_af
  `{EB : Eq BT} `{EA : Eq AT}
  (v : @expr_value (@link BT EB AT EA)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_af C)
  end.

Definition link_update
  `{EB : Eq BT} `{EA : Eq AT} 
  `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
  `{@Conc.time BT EB OB} `{@Conc.time AT EA OA}
  (C : @dy_ctx (@link BT EB AT EA)) (st : state) x v :=
  match st with
  | ST mem (BF t) =>
    BF (update (filter_ctx_bf C) (ST (filter_mem_bf mem) t) x (filter_v_bf v))
  | ST mem (AF t) =>
    AF (update (filter_ctx_af C) (ST (filter_mem_af mem) t) x (filter_v_af v))
  end.

Lemma link_update_lt :
  forall 
    `{EB : Eq BT} `{EA : Eq AT} 
    `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
    `{CB : @Conc.time BT EB OB} `{CA : @Conc.time AT EA OA}
    C mem t x v, 
  let t' := @link_update BT EB AT EA OB OA CB CA C (ST mem t) x v in
  link_leb t t' = true /\ link_eqb t t' = false.
Proof.
  intros. destruct t; simpl in *; try apply update_lt.
Qed.

#[export] Instance link_time 
  `{EB : Eq BT} `{EA : Eq AT} 
  `{OB : @OrderT BT EB} `{OA : @OrderT AT EA}
  `{CB : @Conc.time BT EB OB} `{CA : @Conc.time AT EA OA}
  : (@Conc.time (@link BT EB AT EA) (@LinkEq BT EB AT EA) 
                (@LinkOrderT BT EB AT EA OB OA)) :=
{
  update := link_update;
  update_lt := link_update_lt
}.

Fixpoint lift_ctx_bf `{EB : Eq BT} `{EA : Eq AT} (C : @dy_ctx BT) 
  : @dy_ctx (@link BT EB AT EA) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (BF t) (lift_ctx_bf C')
  | dy_c_lete x t C' => dy_c_lete x (BF t) (lift_ctx_bf C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_bf C') (lift_ctx_bf C'')
  end.

Fixpoint lift_ctx_af `{EB : Eq BT} `{EA : Eq AT} (C : @dy_ctx AT)
  : @dy_ctx (@link BT EB AT EA) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (AF t) (lift_ctx_af C')
  | dy_c_lete x t C' => dy_c_lete x (AF t) (lift_ctx_af C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_af C') (lift_ctx_af C'')
  end.

Fixpoint map_inject {T} (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  match Cin with
  | [||] => [||]
  | dy_c_lam x t C' =>
    dy_c_lam x t (map_inject Cout C')
  | dy_c_lete x t C' =>
    dy_c_lete x t (map_inject Cout C')
  | dy_c_letm M C' C'' =>
    dy_c_letm M (Cout[|map_inject Cout C'|]) (map_inject Cout C'')
  end.

Definition inject_ctx {T} (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  Cout[|map_inject Cout Cin|].

Fixpoint delete_prefix {T} `{Eq T} (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  match Cout, Cin with
  | [||], Cin => Cin
  | dy_c_lam x t Cout', dy_c_lam x' t' Cin'
  | dy_c_lete x t Cout', dy_c_lete x' t' Cin' =>
    if eq_eid x x' && eqb t t' then
      delete_prefix Cout' Cin'
    else Cin
  | dy_c_letm M Cout' Cout'', dy_c_letm M' Cin' Cin'' =>
    if eq_mid M M' && eq_ctx Cout' Cin' then
      delete_prefix Cout'' Cin''
    else Cin
  | _, _ => Cin
  end.

Ltac intro_refl :=
  assert (forall x, eq_eid x x = true) as eid_refl; [intros; apply eq_eid_eq; eauto|idtac];
  assert (forall M, eq_mid M M = true) as mid_refl; [intros; apply eq_mid_eq; eauto|idtac];
  assert (forall {T} `{Eq T} t, eqb t t = true) as t_refl; [intros; apply eqb_eq; eauto|idtac];
  assert (forall {T} `{Eq T} C, eq_ctx C C = true) as ctx_refl; [intros; apply eq_ctx_eq; eauto|idtac].

Lemma delete_prefix_eq :
  forall {T} `{Eq T} (Cout Cin : dy_ctx),
    delete_prefix Cout (Cout[|Cin|]) = Cin.
Proof.
  intro_refl. intros. rename H into ET. revert Cin.
  induction Cout; simpl; eauto;    
    try rewrite eid_refl; try rewrite mid_refl; try rewrite t_refl; try rewrite ctx_refl;
    simpl; eauto.
Qed.

Lemma delete_prefix_dec :
  forall {T} `{Eq T} (Cout Cin : @dy_ctx T),
    dy_level (delete_prefix Cout Cin) <= dy_level Cin.
Proof.
  intros. revert Cout. 
  induction Cin; intros; destruct Cout; simpl; eauto;
  try destruct (eq_eid x0 x); try destruct (eqb tx0 tx);
  try destruct (eq_mid M0 M); try destruct (eq_ctx Cout1 Cin1);
  simpl; try nia.
  etransitivity; try apply IHCin; eauto.
  etransitivity; try apply IHCin; eauto.
  etransitivity; try apply IHCin2; nia.
Qed.

Require Import Program.

Program Fixpoint delete_map 
  {T} `{Eq T} (Cout Cin : dy_ctx) {measure (dy_level Cin)} :=
  match Cin with
  | [||] => [||]
  | dy_c_lam x t C' =>
    dy_c_lam x t (delete_map Cout C')
  | dy_c_lete x t C' =>
    dy_c_lete x t (delete_map Cout C')
  | dy_c_letm M C' C'' =>
    dy_c_letm M (delete_map Cout (delete_prefix Cout C'))
                (delete_map Cout C'')
  end.

Next Obligation.
  simpl.
  pose proof (delete_prefix_dec Cout C').
  nia.
Defined.
Next Obligation.
  simpl.
  pose proof (delete_prefix_dec Cout C'').
  nia.
Defined.

(* reduction lemmas *)
Lemma delete_map_red_lam :
  forall {T} `{Eq T} Cout x t C',
    delete_map Cout (dy_c_lam x t C') =
      dy_c_lam x t (delete_map Cout C').
Proof.
  intros. unfold delete_map. unfold delete_map_func.
  rewrite fix_sub_eq; simpl; try reflexivity.
  intros x' f g Heq.
  specialize (functional_extensionality_dep f g Heq).
  intros RR. rewrite RR. reflexivity.
Qed.

Lemma delete_map_red_lete :
  forall {T} `{Eq T} Cout x t C',
    delete_map Cout (dy_c_lete x t C') =
      dy_c_lete x t (delete_map Cout C').
Proof.
  intros. unfold delete_map. unfold delete_map_func.
  rewrite fix_sub_eq; simpl; try reflexivity.
  intros x' f g Heq.
  specialize (functional_extensionality_dep f g Heq).
  intros RR. rewrite RR. reflexivity.
Qed.

Lemma delete_map_red_letm :
  forall {T} `{Eq T} Cout M C' C'',
    delete_map Cout (dy_c_letm M C' C'') =
      dy_c_letm M (delete_map Cout (delete_prefix Cout C'))
                  (delete_map Cout C'').
Proof.
  intros. unfold delete_map. unfold delete_map_func.
  rewrite fix_sub_eq; simpl; try reflexivity.
  intros x' f g Heq.
  specialize (functional_extensionality_dep f g Heq).
  intros RR. rewrite RR. reflexivity.
Qed.

Ltac simpl_delete :=
  simpl;
  try rewrite delete_map_red_lam;
  try rewrite delete_map_red_lete;
  try rewrite delete_map_red_letm.

Lemma delete_map_eq :
  forall {T} `{Eq T} (Cout Cin : dy_ctx),
    delete_map Cout (map_inject Cout Cin) = Cin.
Proof.
  intros. rename H into ET. revert Cout.
  induction Cin; intros; simpl_delete; 
  try rewrite IHCin; eauto.
  rewrite delete_prefix_eq. 
  rewrite IHCin1. rewrite IHCin2. eauto.
Qed.

Definition delete_inject {T} `{Eq T} (Cout Cin : dy_ctx) :=
  delete_map Cout (delete_prefix Cout Cin).

Lemma delete_inject_eq :
  forall {T} `{Eq T} (Cout Cin : dy_ctx),
    delete_inject Cout (inject_ctx Cout Cin) = Cin.
Proof.
  intros. unfold delete_inject. unfold inject_ctx.
  rewrite delete_prefix_eq.
  rewrite delete_map_eq. eauto.
Qed.
  
Notation "Cout '<|' Cin '|>'" := (inject_ctx Cout Cin)
                              (at level 100, Cin at next level, right associativity).

Definition inject_ctx_mem {T} `{Eq T} (Cout : @dy_ctx T) (mem : T -> option (@expr_value T)) :=
  fun t =>
    match mem t with
    | Some (Closure x t C) => Some (Closure x t (Cout <|C|>))
    | None => None
    end.

Definition delete_ctx_mem {T} `{Eq T} (Cout : @dy_ctx T) (mem : T -> option (@expr_value T)) :=
  fun t =>
    match mem t with
    | Some (Closure x t C) => Some (Closure x t (delete_inject Cout C))
    | None => None
    end.

Lemma delete_ctx_mem_eq :
  forall {T} `{Eq T} (Cout : @dy_ctx T) (mem : T -> option (@expr_value T)),
         delete_ctx_mem Cout (inject_ctx_mem Cout mem) = mem.
Proof.
  intros. apply functional_extensionality.
  intros. unfold inject_ctx_mem. unfold delete_ctx_mem.
  destruct (mem x) eqn:ACCESS; try reflexivity.
  destruct e. rewrite delete_inject_eq. reflexivity.
Qed.

Lemma map_inject_addr_x :
  forall {T} `{Eq T} x (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    addr_x (map_inject Cout Cin) x = addr_x Cin x.
Proof.
  intros. revert Cout. 
  induction Cin; intros; simpl; eauto;
  destruct (addr_x Cin x) eqn:ADDR;
  rewrite IHCin; eauto.
Qed.

Lemma map_inject_ctx_M :
  forall {T} `{Eq T} M (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    ctx_M (map_inject Cout Cin) M =
    match ctx_M Cin M with
    | Some CM => Some (Cout <| CM |>)
    | None => None
    end.
Proof.
  intros. revert Cout.
  induction Cin; intros; simpl; eauto.
  rewrite IHCin2. destruct (ctx_M Cin2 M); eauto.
  destruct (eq_mid M M0); eauto.
Qed.

Lemma plugin_ctx_addr_x :
  forall {T} `{Eq T} x (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match addr_x Cin x with
    | Some t => addr_x (Cout[|Cin|]) x = Some t
    | None => True
    end.
Proof.
  intros. revert Cin.
  induction Cout; intros; 
  destruct (addr_x Cin x) eqn:ADDR; simpl; eauto;
  try (specialize (IHCout Cin); rewrite ADDR in IHCout;
      rewrite IHCout; eauto).
  specialize (IHCout2 Cin); rewrite ADDR in IHCout2; rewrite IHCout2; eauto.
Qed.

Lemma plugin_ctx_ctx_M :
  forall {T} `{Eq T} M (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match ctx_M Cin M with
    | Some CM => ctx_M (Cout[|Cin|]) M = Some CM
    | None => True
    end.
Proof.
  intros. revert Cin.
  induction Cout; intros;
  destruct (ctx_M Cin M) eqn:CTX; simpl; eauto;
  try (specialize (IHCout Cin); rewrite CTX in IHCout;
      rewrite IHCout; eauto).
  specialize (IHCout2 Cin); rewrite CTX in IHCout2; rewrite IHCout2; eauto.
Qed.

Lemma inject_ctx_addr_x :
  forall {T} `{Eq T} x (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match addr_x Cin x with
    | Some t => addr_x (Cout<|Cin|>) x = Some t
    | None => True
    end.
Proof.
  intros. destruct (addr_x Cin x) eqn:ADDR; eauto.
  rewrite <- map_inject_addr_x with (Cout := Cout) in ADDR.
  rewrite <- ADDR. 
  pose proof plugin_ctx_addr_x.
  specialize (H0 x Cout (map_inject Cout Cin)).
  rewrite ADDR in H0. rewrite <- H0 in ADDR.
  eauto.
Qed.

Lemma inject_ctx_ctx_M :
  forall {T} `{Eq T} M (Cout : @dy_ctx T) (Cin : @dy_ctx T),
    match ctx_M Cin M with
    | Some CM => ctx_M (Cout<|Cin|>) M = Some (Cout <|CM|>)
    | None => True
    end.
Proof.
  intros. destruct (ctx_M Cin M) eqn:CTX; eauto.
  pose proof (map_inject_ctx_M M Cout Cin).
  rewrite CTX in H0.
  pose proof (plugin_ctx_ctx_M M Cout (map_inject Cout Cin)).
  rewrite H0 in H1. eauto.
Qed.

Definition delete_update {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) :=
  fun C st x v =>
    let delete_C := delete_inject Cout C in
    let delete_st :=
      match st with
      | ST mem t => ST (delete_ctx_mem Cout mem) t
      end in
    let delete_v := 
      match v with
      | Closure x_v e_v C_v =>
        Closure x_v e_v (delete_inject Cout C_v)
      end in
    update delete_C delete_st x delete_v.

Lemma delete_update_lt {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) :
  forall C mem t x v, let t' := delete_update Cout C (ST mem t) x v in
                                leb t t' = true /\ eqb t t' = false.
Proof.
  intros. unfold delete_update in t'. apply update_lt.
Qed.

#[export] Instance delete_time {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) : @time T ET OT :=
  {
    update := delete_update Cout;
    update_lt := delete_update_lt Cout
  }.

Lemma delete_update_eq {T} `{ET : Eq T} `{OT : @OrderT T ET} `{@time T ET OT} (Cout : @dy_ctx T) :
  forall C mem t x v,
    let inject_v :=
      match v with
      | Closure x_v e_v C_v => Closure x_v e_v (Cout<|C_v|>)
      end in
    delete_update Cout (Cout<|C|>) (ST (inject_ctx_mem Cout mem) t) x inject_v =
    update C (ST mem t) x v.
Proof.
  intros. destruct v. destruct inject_v eqn:INJ. inversion INJ. subst.
  unfold delete_update. rewrite delete_inject_eq. rewrite delete_ctx_mem_eq.
  rewrite delete_inject_eq. reflexivity.
Qed.

Lemma plugin_map_assoc :
  forall {T} `{Eq T} (Cout C C' : @dy_ctx T),
    (map_inject Cout C) [|map_inject Cout C'|] = (map_inject Cout (C [|C'|])).
Proof.
  intros. revert Cout C'. induction C; intros; simpl; eauto; try rewrite IHC; try rewrite IHC2; eauto.
Qed.

Lemma plugin_inject_assoc :
  forall {T} `{Eq T} (Cout C C' : @dy_ctx T),
    (Cout <| C |>)[| map_inject Cout C' |] = (Cout <|C[|C'|]|>).
Proof.
  intros. unfold inject_ctx. rewrite <- c_plugin_assoc.
  rewrite plugin_map_assoc. eauto.
Qed.

Lemma inject_update_m_eq :
  forall {T} `{Eq T} t x e mem (Cout C : @dy_ctx T),
  (t !-> Closure x e (Cout <| C |>); inject_ctx_mem Cout mem) =
            inject_ctx_mem Cout (t !-> Closure x e C; mem).
Proof.
  intros. apply functional_extensionality.
  intros. unfold update_m. unfold inject_ctx_mem.
  destruct (eqb x0 t); eauto.
Qed.

Lemma delete_eval_eq {T} `{ET : Eq T} `{OT : @OrderT T ET} `{TT : @time T ET OT} (Cout : @dy_ctx T) :
  forall C st e v st'
         (EVAL : @EvalR T ET OT TT C st e v st'),
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
    @EvalR T ET OT (@delete_time T ET OT TT Cout)
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
    unfold inject_ctx_mem. rewrite <- ACCESS. eauto.
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

Fixpoint lift_state_bf `{OrderT BT} (st : @state BT) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (BF t) (lift_ctx_bf C')
  | dy_c_lete x t C' => dy_c_lete x (BF t) (lift_ctx_bf C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_bf C') (lift_ctx_bf C'')
  end.

Fixpoint lift_state_af `{OrderT AT} (st : @state AT) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (AF t) (lift_ctx_af C')
  | dy_c_lete x t C' => dy_c_lete x (AF t) (lift_ctx_af C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_af C') (lift_ctx_af C'')
  end.

Definition inject_state {T} (st_out : @Conc.state T)

Lemma link_eval `{Conc.time BT} `{Conc.time AT} :
  forall (Cout : @dy_ctx BT) (Cin : @dy_ctx AT) st e e' st'
         (EVAL : EvalR C st e e' st')
