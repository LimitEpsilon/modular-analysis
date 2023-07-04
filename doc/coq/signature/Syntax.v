From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Coq Require Export Strings.String.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Inductive expr_id :=
  | eid (x : nat)
.

Inductive mod_id :=
  | mid (M : nat)
.

Definition eq_eid id1 id2 :=
  match id1, id2 with
  | eid x1, eid x2 => x1 =? x2
  end.

Definition eq_mid id1 id2 :=
  match id1, id2 with
  | mid M1, mid M2 => M1 =? M2
  end.

Lemma eq_eid_eq : forall x x',
  eq_eid x x' = true <-> x = x'.
Proof.
  intros. destruct x. destruct x'.
  simpl. split; intros. 
  rewrite Nat.eqb_eq in H.
  rewrite H. eauto.
  inversion H; subst. rewrite Nat.eqb_eq. eauto.
Qed.

Lemma eq_eid_neq : forall x x',
  eq_eid x x' = false <-> x <> x'.
Proof.
  intros. destruct x. destruct x'.
  simpl. split; intros.
  unfold not. intros.
  rewrite Nat.eqb_neq in H. apply H. inversion H0. eauto.
  rewrite Nat.eqb_neq. unfold not. intros. apply H. subst; eauto.
Qed.

Lemma eq_mid_eq : forall M M',
  eq_mid M M' = true <-> M = M'.
Proof.
  intros. destruct M. destruct M'.
  simpl. split; intros. 
  rewrite Nat.eqb_eq in H.
  rewrite H. eauto.
  inversion H; subst. rewrite Nat.eqb_eq. eauto.
Qed.

Lemma eq_mid_neq : forall M M',
  eq_eid M M' = false <-> M <> M'.
Proof.
  intros. destruct M. destruct M'.
  simpl. split; intros.
  unfold not. intros.
  rewrite Nat.eqb_neq in H. apply H. inversion H0. eauto.
  rewrite Nat.eqb_neq. unfold not. intros. apply H. subst; eauto.
Qed.

Inductive st_ctx :=
  | st_hole
  | st_binde (x : expr_id) (C : st_ctx)
  | st_bindm (M : mod_id) (CM : st_ctx) (C : st_ctx)
.

Inductive tm :=
  | e_var (x : expr_id)
  | e_lam (x : expr_id) (e : tm)
  | e_app (e1 : tm) (e2 : tm)
  | e_link (m : tm) (e : tm)
  | m_empty
  | m_var (M : mod_id)
  | m_lam (M : mod_id) (s : st_ctx) (e : tm)
  | m_app (e1 : tm) (e2 : tm) (s : st_ctx)
.

Inductive value : tm -> Prop :=
  | v_fn x e : value (e_lam x e)
  | v_ft M s e : value (m_lam M s e)
.

Fixpoint st_ctx_M (C : st_ctx) (M : mod_id) :=
  match C with
  | st_hole => None
  | st_binde _ C' => st_ctx_M C' M
  | st_bindm M' CM' C' =>
    match st_ctx_M C' M with
    | Some CM => Some CM
    | None => if eq_mid M M' then Some CM' else None
    end
  end.

Fixpoint st_plugin (Cout : st_ctx) (Cin : st_ctx) :=
  match Cout with
  | st_hole => Cin
  | st_binde x C' => st_binde x (st_plugin C' Cin)
  | st_bindm M' CM' C' => st_bindm M' CM' (st_plugin C' Cin)
  end.

Lemma st_plugin_assoc : forall C1 C2 C3,
  st_plugin (st_plugin C1 C2) C3 =
  st_plugin C1 (st_plugin C2 C3). 
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
  rewrite IHC1_2. eauto.
Qed.

Notation "Cout '[[|' Cin '|]]'" := (st_plugin Cout Cin)
                              (at level 100, Cin at next level, right associativity).

Notation "'[[||]]'" := (st_hole) (at level 100).

(* collect all static contexts reachable from the current configuration *)
Fixpoint collect_ctx C e :=
  match e with
  | e_var x => (None, [C])
  | e_lam x e' => 
    let ctx_body := snd (collect_ctx (C [[|st_binde x ([[||]])|]]) e') in
    (None, C :: ctx_body)
  | e_app e1 e2 =>
    let ctxs1 := snd (collect_ctx C e1) in
    let ctxs2 := snd (collect_ctx C e2) in
    (None, ctxs1 ++ ctxs2)
  | e_link m e' =>
    match collect_ctx C m with
    | (Some C_m, ctxs_m) => 
      let (ctx_o, ctxs_e) := collect_ctx C_m e' in
      (ctx_o, ctxs_m ++ ctxs_e)
    | (None, ctxs_m) => (None, ctxs_m)
    end
  | m_empty => (Some C, [C])
  | m_var M =>
    match st_ctx_M C M with
    | Some C_M => (Some (C[[|C_M|]]), [C])
    | None => (None, [C])
    end
  | m_lam M s e =>
    let ctx_body := snd (collect_ctx (C [[|st_bindm M s ([[||]])|]]) e) in
    (None, C :: ctx_body)
  | m_app e1 e2 s =>
    let ctxs1 := snd (collect_ctx C e1) in
    let ctxs2 := snd (collect_ctx C e2) in
    (Some (st_plugin C s), ctxs1 ++ ctxs2)
  end.

Lemma st_ctx_M_plugin :
  forall Cout Cin M,
    st_ctx_M (st_plugin Cout Cin) M =
      match st_ctx_M Cin M with
      | Some CM => Some CM
      | None =>
        match st_ctx_M Cout M with
        | Some CM => Some CM
        | None => None
        end
      end.
Proof.
  induction Cout; intros; simpl; eauto.
  - destruct (st_ctx_M Cin M); eauto.
  - specialize (IHCout2 Cin M0). 
    destruct (st_ctx_M Cin M0). 
    rewrite IHCout2. eauto. 
    rewrite IHCout2.
    destruct (st_ctx_M Cout2 M0). eauto.
    assert (RR : forall Cout0 Cin0, 
    st_ctx_M (st_plugin Cout0 Cin0) M0 = None -> st_ctx_M Cin0 M0 = None).
    { induction Cout0; intros; simpl; eauto. 
      simpl in H. apply IHCout0_2.
      destruct (st_ctx_M (st_plugin Cout0_2 Cin0) M0).
      inversion H. eauto. }
    specialize (IHCout1 Cin M0).
    rewrite (RR Cout2 Cin IHCout2) in IHCout1.
    destruct (eq_mid M0 M).
    eauto. eauto.
Qed.

Lemma collect_ctx_refl : forall e C, In C (snd (collect_ctx C e)).
Proof.
  induction e; intros; simpl; eauto.
  - apply in_app_iff. left. eauto.
  - remember (collect_ctx C e1) as ol. destruct ol as [o l].
    specialize (IHe1 C). rewrite <- Heqol in IHe1.
    destruct o; eauto. simpl in *.
    destruct (collect_ctx C e2); simpl in *.
    destruct (collect_ctx s e2); simpl in *. 
    apply in_app_iff. left. eauto.
  - destruct (st_ctx_M C M); simpl; left; eauto.
  - apply in_app_iff. eauto.
Qed.

(* dynamic context *)
Inductive dy_ctx {time : Type} :=
  | dy_hole
  | dy_binde (x: expr_id) (tx : time) (C : dy_ctx)
  | dy_bindm (M : mod_id) (CM : dy_ctx) (C : dy_ctx)
.

Fixpoint dy_plugin {time : Type} (Cout : @dy_ctx time) (Cin : @dy_ctx time) :=
  match Cout with
  | dy_hole => Cin
  | dy_binde x tx C' => dy_binde x tx (dy_plugin C' Cin)
  | dy_bindm M CM C' => dy_bindm M CM (dy_plugin C' Cin)
  end.

Fixpoint addr_x {time : Type} (C : @dy_ctx time) (x : expr_id) :=
  match C with
  | dy_hole => None
  | dy_binde x' tx' C' =>
    match addr_x C' x with
    | None => if eq_eid x x' then (Some tx') else None
    | addr => addr
    end
  | dy_bindm _ _ C' => addr_x C' x
  end.

Fixpoint ctx_M {time : Type} (C : @dy_ctx time) (M : mod_id) :=
  match C with
  | dy_hole => None
  | dy_binde _ _ C' => ctx_M C' M
  | dy_bindm M' CM' C' =>
    match ctx_M C' M with
    | Some CM => Some CM
    | None => if eq_mid M M' then Some CM' else None
    end
  end.

(* a term, a context *)
Inductive expr_value {time : Type} :=
  | Fun (x : expr_id) (e : tm) (C : @dy_ctx time)
  | Func (M : mod_id) (s : st_ctx) (e : tm) (C : @dy_ctx time)
.

Inductive dy_value {time : Type} :=
  | EVal (ev : @expr_value time)
  | MVal (mv : @dy_ctx time)
.

Notation "Cout '[|' Cin '|]'" := (dy_plugin Cout Cin)
                              (at level 100, Cin at next level, right associativity).
Notation "'[||]'" := (dy_hole) (at level 100).

Fixpoint In_ctx {T} (t : T) (C : @dy_ctx T) :=
  match C with
  | [||] => False
  | dy_binde _ t' C' => t = t' \/ In_ctx t C'
  | dy_bindm _ C' C'' => In_ctx t C' \/ In_ctx t C''
  end.

Lemma dy_plugin_assoc : forall {T} (C1 : @dy_ctx T) C2 C3, C1[| C2[| C3 |] |] = ((C1[|C2|])[|C3|]).
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
  rewrite IHC1_2. eauto.
Qed.

Fixpoint dy_to_st {T} (C : @dy_ctx T) :=
  match C with
  | ([||]) => st_hole
  | dy_binde x _ C' => st_binde x (dy_to_st C')
  | dy_bindm M CM C' => st_bindm M (dy_to_st CM) (dy_to_st C')
  end.

Lemma in_plugin_iff :
  forall {T} (t : T) (Cout Cin : @dy_ctx T),
    In_ctx t (Cout[|Cin|]) <-> (In_ctx t Cout \/ In_ctx t Cin).
Proof.
  intros. revert Cin.
  induction Cout; intros; split; simpl; intros H; 
  try rewrite IHCout in H;
  try rewrite IHCout2 in H;
  try rewrite IHCout;
  try rewrite IHCout2;
  try destruct H as [? | [? | ?]];
  try destruct H as [[? | ?] | ?];
  eauto.
  destruct H; try assumption; inversion H.
Qed.

Lemma dy_to_st_plugin :
  forall {T} (Cout : @dy_ctx T) Cin,
    dy_to_st (Cout[|Cin|]) = st_plugin (dy_to_st Cout) (dy_to_st Cin).
Proof.
  induction Cout; intros; simpl; try rewrite IHCout; eauto.
  rewrite IHCout2. eauto.
Qed. 

Lemma mod_is_static_none : forall {T} (dC : @dy_ctx T) (M : mod_id),
  (ctx_M dC M = None <-> st_ctx_M (dy_to_st dC) M = None).
Proof. 
  intros. repeat split. 
  - induction dC; simpl; eauto.
    destruct (ctx_M dC2 M). intros H; inversion H.
    specialize (IHdC2 eq_refl). rewrite IHdC2.
    destruct (eq_mid M M0). intros H; inversion H. eauto.
  - induction dC; simpl; eauto.
    destruct (st_ctx_M (dy_to_st dC2) M). intros H; inversion H.
    specialize (IHdC2 eq_refl). rewrite IHdC2.
    destruct (eq_mid M M0). intros H; inversion H. eauto.
Qed.

Lemma mod_is_static_some : forall {T} (dC : @dy_ctx T) (M : mod_id),
  (forall v, ctx_M dC M = Some v -> st_ctx_M (dy_to_st dC) M = Some (dy_to_st v)) /\
  (forall v, st_ctx_M (dy_to_st dC) M = Some v -> exists dv, dy_to_st dv = v /\ ctx_M dC M = Some dv).
Proof.
  intros; split. 
  - induction dC; simpl; intros; eauto.
    + inversion H.
    + remember (ctx_M dC2 M) as v2. destruct v2.
      specialize (IHdC2 v H). rewrite IHdC2. eauto.
      symmetry in Heqv2. rewrite mod_is_static_none in Heqv2.
      rewrite Heqv2. destruct (eq_mid M M0); inversion H; eauto.
  - induction dC; simpl; intros; eauto.
    + inversion H.
    + remember (st_ctx_M (dy_to_st dC2) M) as v2. destruct v2.
      specialize (IHdC2 v H). inversion IHdC2. exists x.
      destruct H0. split. assumption. rewrite H1. eauto.
      remember (ctx_M dC2 M) as v2. destruct v2;
      symmetry in Heqv2; rewrite <- mod_is_static_none in Heqv2.
      rewrite Heqv2 in Heqv0. inversion Heqv0.
      destruct (eq_mid M M0). inversion H.
      exists dC1. eauto. inversion H.
Qed.

Class Eq T : Type :=
{
  eqb : T -> T -> bool;
  eqb_eq : forall (t t' : T), eqb t t' = true <-> t = t';
  eqb_neq : forall (t t' : T), eqb t t' = false <-> t <> t'
}.

Fixpoint eq_ctx {T} `{Eq T} (C1 : @dy_ctx T) (C2 : @dy_ctx T) :=
  match C1, C2 with
  | [||], [||] => true
  | dy_binde x1 t1 C1', dy_binde x2 t2 C2' =>
    eq_eid x1 x2 && eqb t1 t2 && eq_ctx C1' C2'
  | dy_bindm M1 C1' C1'', dy_bindm M2 C2' C2'' =>
    eq_mid M1 M2 && eq_ctx C1' C2' && eq_ctx C1'' C2''
  | _, _ => false
  end.

Lemma eq_ctx_eq : forall {T} `{Eq T} (C C' : dy_ctx),
  eq_ctx C C' = true <-> C = C'.
Proof.
  intros. rename H into ET. revert C'.
  induction C; destruct C'; split; intros H; inversion H; try reflexivity;
  try (assert (x = x0);
    [rewrite <- eq_eid_eq | idtac];
    destruct (eq_eid x x0); inversion H1; eauto;
    assert (tx = tx0);
    [rewrite <- eqb_eq | idtac];
    destruct (eqb tx tx0); inversion H1; eauto;
    assert (C = C');
    [rewrite <- IHC | idtac]; eauto; subst; reflexivity);
  try (subst; simpl;
    assert (eq_eid x0 x0 = true);
    [rewrite eq_eid_eq; reflexivity | idtac];
    assert (eqb tx0 tx0 = true);
    [rewrite eqb_eq; reflexivity | idtac];
    assert (eq_ctx C' C' = true);
    [rewrite IHC; reflexivity | idtac];
    rewrite H0; rewrite H1; rewrite H2; eauto).
  assert (M = M0);
  [rewrite <- eq_mid_eq; destruct (eq_mid M M0); inversion H1; eauto | idtac];
  assert (C1 = C'1);
  [rewrite <- IHC1; destruct (eq_mid M M0);
   destruct (eq_ctx C1 C'1); inversion H1; eauto | idtac].
  assert (C2 = C'2);
  [rewrite <- IHC2; destruct (eq_mid M M0);
   destruct (eq_ctx C1 C'1); destruct (eq_ctx C2 C'2); inversion H1; eauto | idtac];
  subst; eauto.
  subst; simpl.
  assert (eq_mid M0 M0 = true);
  [rewrite eq_mid_eq; reflexivity | idtac];
  assert (eq_ctx C'1 C'1 = true);
  [rewrite IHC1; reflexivity | idtac];
  assert (eq_ctx C'2 C'2 = true);
  [rewrite IHC2; reflexivity | idtac];
  rewrite H0; rewrite H1; rewrite H2; eauto.
Qed.

Lemma eq_ctx_neq : forall {T} `{Eq T} (C C' : dy_ctx),
  eq_ctx C C' = false <-> C <> C'.
Proof.
  intros; split; intros.
  - red; intros contra. rewrite <- eq_ctx_eq in contra.
    rewrite contra in H0. inversion H0.
  - destruct (eq_ctx C C') eqn:EQ; try reflexivity.
    rewrite eq_ctx_eq in EQ. apply H0 in EQ. inversion EQ.
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

(* projection *)

Fixpoint project {T} (d : @dy_ctx T) (s : st_ctx) :=
  match s with
  | [[||]] => Some ([||])
  | st_binde x C =>
    match addr_x d x with
    | Some t =>
      match project d C with
      | Some C' => Some (dy_binde x t C')
      | None => None
      end
    | None => None
    end
  | st_bindm M CM C =>
    match ctx_M d M with
    | Some CM' =>
      match project CM' CM with
      | Some C' =>
        match project d C with
        | Some C'' => Some (dy_bindm M C' C'')
        | None => None
        end
      | None => None
      end
    | None => None
    end
  end.

Lemma plugin_project_eq {T} {ET : Eq T} 
  (Cout Cin p : @dy_ctx T) (s : st_ctx)
  (PROJECT : project Cin s = Some p) : project (Cout[|Cin|]) s = Some p.
Proof.
  revert Cout Cin p PROJECT.
  induction s; simpl; eauto.
  - intros.
    destruct (addr_x Cin x) eqn:ACCESS; try (inversion PROJECT; fail).
    pose proof (plugin_ctx_addr_x x Cout Cin) as ADDR.
    rewrite ACCESS in ADDR. rewrite ADDR.
    destruct (project Cin s) eqn:PROJ; try (inversion PROJECT; fail).
    erewrite IHs; eauto.
  - intros.
    destruct (ctx_M Cin M) eqn:ACCESS; try (inversion PROJECT; fail).
    pose proof (plugin_ctx_ctx_M M Cout Cin) as CTX.
    rewrite ACCESS in CTX. rewrite CTX.
    destruct (project d s1) eqn:PROJ1; try (inversion PROJECT; fail).
    destruct (project Cin s2) eqn:PROJ2; try (inversion PROJECT; fail).
    erewrite IHs2; eauto.
Qed.

Lemma project_st_eq {T} {ET : Eq T}
  (d ds : @dy_ctx T) (s : st_ctx)
  (PROJECT : project d s = Some ds) : dy_to_st ds = s.
Proof.
  revert d ds PROJECT.
  induction s; intros; simpl in *.
  - inversion PROJECT; subst; eauto.
  - destruct (addr_x d x); inversion PROJECT.
    destruct (project d s) eqn:PROJ; inversion PROJECT.
    specialize (IHs d d0 PROJ).
    simpl in *. rewrite IHs. eauto.
  - destruct (ctx_M d M); inversion PROJECT.
    destruct (project d0 s1) eqn:PROJ1; inversion PROJECT.
    specialize (IHs1 d0 d1 PROJ1).
    destruct (project d s2) eqn:PROJ2; inversion PROJECT.
    specialize (IHs2 d d2 PROJ2).
    simpl. rewrite IHs1. rewrite IHs2. eauto.
Qed.

(* injection, deletion *)

Fixpoint delete {T} `{Eq T} (Cout : @dy_ctx T) (Cin : @dy_ctx T) :=
  match Cout, Cin with
  | [||], Cin => Cin
  | dy_binde x t Cout', dy_binde x' t' Cin' =>
    if eq_eid x x' && eqb t t' then
      delete Cout' Cin'
    else Cin
  | dy_bindm M Cout' Cout'', dy_bindm M' Cin' Cin'' =>
    if eq_mid M M' && eq_ctx Cout' Cin' then
      delete Cout'' Cin''
    else Cin
  | _, _ => Cin
  end.

Ltac intro_refl :=
  assert (forall x, eq_eid x x = true) as eid_refl; [intros; apply eq_eid_eq; eauto|idtac];
  assert (forall M, eq_mid M M = true) as mid_refl; [intros; apply eq_mid_eq; eauto|idtac];
  assert (forall {T} `{Eq T} t, eqb t t = true) as t_refl; [intros; apply eqb_eq; eauto|idtac];
  assert (forall {T} `{Eq T} C, eq_ctx C C = true) as ctx_refl; [intros; apply eq_ctx_eq; eauto|idtac].

Lemma delete_eq :
  forall {T} `{Eq T} (Cout Cin : dy_ctx),
    delete Cout (Cout[|Cin|]) = Cin.
Proof.
  intro_refl. intros. rename H into ET. revert Cin.
  induction Cout; simpl; eauto;    
    try rewrite eid_refl; try rewrite mid_refl; try rewrite t_refl; try rewrite ctx_refl;
    simpl; eauto.
Qed.

Definition plugin_ctx_v {T} `{Eq T} (Cout : @dy_ctx T) (v : @expr_value T) :=
  match v with
  | Fun x e C => Fun x e (Cout[|C|])
  | Func M e s C => Func M e s (Cout[|C|])
  end.

Definition delete_ctx_v {T} `{Eq T} (Cout : @dy_ctx T) (v : @expr_value T) :=
  match v with
  | Fun x e C => Fun x e (delete Cout C)
  | Func M e s C => Func M e s (delete Cout C)
  end.

(* Typeclass for concrete times *)
Class OrderT (T : Type) `{Eq T} : Type :=
{
  leb : T -> T -> bool;
  leb_refl : forall t, leb t t = true;
  leb_trans : forall t t' t'' (LE : leb t t' = true) (LE' : leb t' t'' = true), leb t t'' = true;
  leb_sym : forall t t' (LE : leb t t' = true) (LE' : leb t' t = true), t = t'
}.

Definition lt {T} `{OrderT T} (t1 t2 : T) :=
  leb t1 t2 = true /\ eqb t1 t2 = false.

Notation "t1 '<' t2" := (lt t1 t2).

Ltac contradict :=
  let contra := fresh "contra" in
  assert False as contra; eauto 3; inversion contra.

Lemma __R__ : forall b, b = false <-> ~ b = true.
Proof. 
  intros; destruct b; unfold "<>"; split; 
  intros; try inversion H; try inversion H0; try contradict; eauto.
Qed.

Ltac refl_bool :=
  match goal with
  | |- _ = false => rewrite __R__; unfold "<>"
  | |- _ <> true => rewrite <- __R__
  | _ => idtac
  end.
