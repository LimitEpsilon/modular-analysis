From MODULAR Require Export Sound.
Require Export Coq.Logic.FunctionalExtensionality.

(* before, after *)
Generalizable Variables BT AT.

Inductive link `{OrderT BT} `{OrderT AT} :=
  | BF (t : BT)
  | AF (t : AT)
.

Definition link_leb `{OrderT BT} `{OrderT AT} (t1 : link) (t2 : link) :=
  match t1, t2 with
  | BF t1, BF t2 => leb t1 t2
  | AF t1, AF t2 => leb t1 t2
  | BF t1, AF t2 => true
  | AF t1, BF t2 => false
  end.

Definition link_eqb `{OrderT BT} `{OrderT AT} (t1 : link) (t2 : link) :=
  match t1, t2 with
  | BF t1, BF t2 => eqb t1 t2
  | AF t1, AF t2 => eqb t1 t2
  | _, _ => false  
  end.

Lemma link_leb_refl : 
  forall `{OrderT BT} `{OrderT AT} t,
  link_leb t t = true.
Proof.
  intros. destruct t; apply leb_refl.
Qed.

Lemma link_leb_trans :
  forall `{OrderT BT} `{OrderT AT} t t' t''
         (LE : link_leb t t' = true)
         (LE' : link_leb t' t'' = true),
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
  forall `{OrderT BT} `{OrderT AT} t t'
         (LE : link_leb t t' = true)
         (LE' : link_leb t' t = true),
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
  forall `{OrderT BT} `{OrderT AT} t t',
  link_eqb t t' = true <-> t = t'.
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
  forall `{OrderT BT} `{OrderT AT} t t',
  link_eqb t t' = false <-> t <> t'.
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

#[export] Instance LinkOrderT `{OrderT BT} `{OrderT AT} : OrderT link:=
  {
    leb := link_leb;
    leb_refl := link_leb_refl;
    leb_trans := link_leb_trans;
    leb_sym := link_leb_sym;
    eqb := link_eqb;
    eqb_eq := link_eqb_eq;
    eqb_neq := link_eqb_neq
  }.

Fixpoint filter_ctx_bf
  `{BO : OrderT BT} `{AO : OrderT AT}
  (C : @dy_ctx (@link BT BO AT AO)) :=
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
  `{BO : OrderT BT} `{AO : OrderT AT}
  (C : @dy_ctx (@link BT BO AT AO)) :=
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
  `{BO : OrderT BT} `{AO : OrderT AT}
  (mem : (@link BT BO AT AO) -> option (@expr_value (@link BT BO AT AO))) :=
  fun t =>
    match mem (BF t) with
    | Some (Closure x e C) => Some (Closure x e (filter_ctx_bf C))
    | None => None
    end.

Definition filter_mem_af
  `{BO : OrderT BT} `{AO : OrderT AT}
  (mem : (@link BT BO AT AO) -> option (@expr_value (@link BT BO AT AO))) :=
  fun t =>
    match mem (AF t) with
    | Some (Closure x e C) => Some (Closure x e (filter_ctx_af C))
    | None => None
    end.

Definition filter_v_bf 
  `{BO : OrderT BT} `{AO : OrderT AT}
  (v : @expr_value (@link BT BO AT AO)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_bf C)
  end.

Definition filter_v_af
  `{BO : OrderT BT} `{AO : OrderT AT}
  (v : @expr_value (@link BT BO AT AO)) :=
  match v with
  | Closure x e C => Closure x e (filter_ctx_af C)
  end.

Definition link_update
  `{Conc.time BT} `{Conc.time AT}
  (C : @dy_ctx link) (st : @state link) x v :=
  match st with
  | ST mem (BF t) =>
    BF (update (filter_ctx_bf C) (ST (filter_mem_bf mem) t) x (filter_v_bf v))
  | ST mem (AF t) =>
    AF (update (filter_ctx_af C) (ST (filter_mem_af mem) t) x (filter_v_af v))
  end.

Lemma link_update_lt :
  forall `{Conc.time BT} `{Conc.time AT}
         C mem t x v, 
  let t' := link_update C (ST mem t) x v in
  link_leb t t' = true /\ link_eqb t t' = false.
Proof.
  intros. destruct t; simpl in *; try apply update_lt.
Qed.

#[export] Instance link_time `{Conc.time BT} `{Conc.time AT} : (@Conc.time link LinkOrderT) :=
{
  update := link_update;
  update_lt := link_update_lt
}.

Fixpoint lift_ctx_bf `{OrderT BT} (C : @dy_ctx BT) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (BF t) (lift_ctx_bf C')
  | dy_c_lete x t C' => dy_c_lete x (BF t) (lift_ctx_bf C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_bf C') (lift_ctx_bf C'')
  end.

Fixpoint lift_ctx_af `{OrderT AT} (C : @dy_ctx AT) :=
  match C with
  | ([||]) => ([||])
  | dy_c_lam x t C' => dy_c_lam x (AF t) (lift_ctx_af C')
  | dy_c_lete x t C' => dy_c_lete x (AF t) (lift_ctx_af C')
  | dy_c_letm M C' C'' => dy_c_letm M (lift_ctx_af C') (lift_ctx_af C'')
  end.

Fixpoint inject_ctx {T} (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  match Cin with
  | ([||]) => Cout
  | dy_c_lam x t C' =>
    inject_ctx (Cout [|dy_c_lam x t ([||])|]) C'
  | dy_c_lete x t C' =>
    inject_ctx (Cout [|dy_c_lete x t ([||])|]) C'
  | dy_c_letm M C' C'' => 
    inject_ctx (Cout [|dy_c_letm M (inject_ctx Cout C') ([||])|]) C''
  end.

Notation "Cout '<|' Cin '|>'" := (inject_ctx Cout Cin)
                              (at level 100, Cin at next level, right associativity).

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
