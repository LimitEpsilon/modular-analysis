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
