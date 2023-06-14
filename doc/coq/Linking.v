From MODULAR Require Export Sound.

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

Definition filter_mem 
  `{BO : OrderT BT} `{AO : OrderT AT} `{OrderT (@link )}
  (mem : BT -> option (@expr_value BT)) := 1.

Fixpoint inject_ctx `{OrderT T1}Cout Cin :=
  match Cin with
  | ([||]) => Cout
  | dy_c_lam x t C' =>
    inject_ctx (Cout [|dy_c_lam x t ([||])|]) C'
  | dy_c_lete x t C' =>
    inject_ctx (Cout [|dy_c_lete x t ([||])|]) C'
  | dy_c_letm M CM C' => 
    inject_ctx (Cout [|dy_c_letm M (inject_ctx Cout CM) ([||])|]) C'
  end.