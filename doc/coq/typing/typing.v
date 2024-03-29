Require Import Basics.
Require Import String.
From Equations Require Export Equations.

Inductive tm :=
  | Var (x : string)
  | Lam (x : string) (e : tm)
  | App (e1 : tm) (e2 : tm)
  | Link (e1 : tm) (e2 : tm)
  | Empty
  | Val (x : string) (e1 : tm) (e2 : tm)
.

Inductive env :=
  | Mt
  | VBind (x : string) (v : value) (σ : env)

with value :=
  | Ctx (σ : env)
  | Closure (x : string) (e : tm) (σ : env)
.

Scheme env_ind_mut := Induction for env Sort Prop
with value_ind_mut := Induction for value Sort Prop.

Combined Scheme ctx_ind from env_ind_mut, value_ind_mut.

Inductive tyenv :=
  | Nil
  | TBind (x : string) (A : ty) (Γ : tyenv)

with ty :=
  | Env (Γ : tyenv)
  | Fun (A : ty) (B : ty)
.

Scheme tyenv_ind_mut := Induction for tyenv Sort Prop
with ty_ind_mut := Induction for ty Sort Prop.

Combined Scheme type_ind from tyenv_ind_mut, ty_ind_mut.

Fixpoint tyenv_size Γ :=
  match Γ with
  | Nil => 1
  | TBind _ A Γ' => ty_size A + tyenv_size Γ'
  end

with ty_size A :=
  match A with
  | Env Γ => tyenv_size Γ
  | Fun A B => 1 + ty_size A + ty_size B
  end.

Lemma size_positive :
  (forall Γ, tyenv_size Γ > 0) /\
  (forall A, ty_size A > 0).
Proof.
  apply type_ind; intros; simpl in *; nia.
Qed.

Lemma tyenv_size_positive Γ : tyenv_size Γ > 0.
Proof. apply size_positive. Qed.

Lemma ty_size_positive A : ty_size A > 0.
Proof. apply size_positive. Qed.

Fixpoint read (Γ : tyenv) (x : string) :=
  match Γ with
  | Nil => None
  | TBind x' τ Γ' =>
    if String.eqb x x' then Some τ else read Γ' x
  end.

Fixpoint remove (Γ : tyenv) (x : string) :=
  match Γ with
  | Nil => Nil
  | TBind x' τ Γ' =>
    let Γ' := remove Γ' x in
    if String.eqb x x' then Γ' else TBind x' τ Γ'
  end.

Lemma read_size_dec Γ :
  forall x A (READ : read Γ x = Some A),
    ty_size A < tyenv_size Γ.
Proof.
  induction Γ; intros; simpl in *; repeat des_hyp;
  inversion READ; subst.
  - specialize (tyenv_size_positive Γ). nia.
  - specialize (IHΓ _ _ READ). nia.
Qed.

Lemma remove_size Γ x :
  match read Γ x with
  | None => remove Γ x = Γ
  | Some _ => tyenv_size (remove Γ x) < tyenv_size Γ
  end.
Proof.
  induction Γ; ii; ss; des_ifs; ss.
  all:first [nia | repeat rw; try reflexivity].
  specialize (ty_size_positive t). nia.
Qed.

Lemma remove_size_dec Γ x :
  tyenv_size (remove Γ x) <= tyenv_size Γ.
Proof.
  specialize (remove_size Γ x).
  des_ifs; ii; repeat rw; nia.
Qed.

(* subtype A B = A ≥ B *)
Equations subtype (A B : ty) : Prop by wf (ty_size A + ty_size B) :=
  subtype (Env Nil) (Env Nil) := True;
  subtype (Env Γ) (Env (TBind x' A' Γ')) :=
    subtype (Env (remove Γ x')) (Env Γ') /\
    match read Γ x' as r return read Γ x' = r -> Prop with 
    | None => fun _ => True
    | Some A => fun _ => subtype A A'
    end eq_refl;
  subtype (Fun A A') (Fun B B') := subtype B A /\ subtype A' B';
  subtype _ _ := False
.

Ltac step :=
  match goal with
  | _ => nia
  | _ => progress ss
  | |- _ -> _ => intros
  | _ => des_goal
  | _ => des_hyp
  | H : Some _ = None |- _ => inversion H
  | H : None = Some _ |- _ => inversion H
  | H : Some ?A = Some ?B |- _ =>
    lazymatch A with
    | B => fail
    | _ => inversion H; subst
    end
  | H : read ?Γ ?x = Some ?A |- _ =>
    lazymatch goal with
    | _ : ty_size A < tyenv_size Γ |- _ => fail
    | _ => specialize (read_size_dec Γ x A H)
    end
  | |- context [remove ?Γ ?x] =>
    lazymatch goal with
    | _ : tyenv_size (remove Γ x) <= tyenv_size Γ |- _ => fail
    | _ => specialize (remove_size_dec Γ x)
    end
  | |- ?L < ?R =>
    match R with
    | context [ty_size ?A] =>
      lazymatch L with
      | context [ty_size A] => fail
      | _ => 
        lazymatch goal with
        | _ : ty_size A > 0 |- _ => fail
        | _ => specialize (ty_size_positive A)
        end
      end
    | context [tyenv_size ?Γ] =>
      lazymatch L with
      | context [tyenv_size Γ] => fail
      | _ =>
        lazymatch goal with
        | _ : tyenv_size Γ > 0 |- _ => fail
        | _ => specialize (tyenv_size_positive Γ)
        end
      end
    end
  end.

Ltac t := repeat step.

Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.

Lemma simp_subtype_env Γ x' A' Γ' :
  subtype (Env Γ) (Env (TBind x' A' Γ')) =
  (subtype (Env (remove Γ x')) (Env Γ') /\
  match read Γ x' with 
  | None => True
  | Some A => subtype A A'
  end).
Proof. destruct Γ; simp subtype; repeat des_goal; ss. Qed.

Lemma simp_subtype_fun A A' B B' :
  subtype (Fun A A') (Fun B B') =
  (subtype B A /\ subtype A' B').
Proof. simp subtype. eauto. Qed.

Inductive type_case : Set :=
  | expr_case | val_case.

Fixpoint fetch (σ : env) x :=
  match σ with
  | Mt => None
  | VBind x' v σ' =>
    if String.eqb x x' then Some v else fetch σ' x
  end.

Inductive eval : tm * env -> value -> Prop :=
  | EVar x σ v (FETCH : fetch σ x = Some v)
  : eval (Var x, σ) v

  | ELam x e σ
  : eval (Lam x e, σ) (Closure x e σ)

  | EApp e1 e2 σ x e σ' v v'
  (FN : eval (e1, σ) (Closure x e σ'))
  (ARG : eval (e2, σ) v)
  (BODY : eval (e, VBind x v σ') v')
  : eval (App e1 e2, σ) v'

  | ELink e1 e2 σ σ' v
  (MOD : eval (e1, σ) (Ctx σ'))
  (EXPR : eval (e2, σ') v)
  : eval (Link e1 e2, σ) v

  | EEmpty σ
  : eval (Empty, σ) (Ctx Mt)

  | EVal x e1 e2 σ v σ'
  (VAL : eval (e1, σ) v)
  (MOD : eval (e2, VBind x v σ) (Ctx σ'))
  : eval (Val x e1 e2, σ) (Ctx (VBind x v σ'))
.

#[local] Hint Constructors eval : core.

Inductive typing (Γ : tyenv) : tm -> ty -> Prop :=
  | TVar x A (READ : read Γ x = Some A)
  : typing Γ (Var x) A

  | TLam x e A B
  (FN : typing (TBind x A Γ) e B)
  : typing Γ (Lam x e) (Fun A B)

  | TApp e1 e2 A B C
  (FN : typing Γ e1 (Fun A C))
  (ARG : typing Γ e2 B)
  (SUB : subtype A B)
  : typing Γ (App e1 e2) C

  | TLink e1 e2 Γ' A
  (MOD : typing Γ e1 (Env Γ'))
  (EXPR : typing Γ' e2 A)
  : typing Γ (Link e1 e2) A

  | TEmpty
  : typing Γ Empty (Env Nil)

  | TVal x e1 e2 A Γ'
  (VAL : typing Γ e1 A)
  (MOD : typing (TBind x A Γ) e2 (Env Γ'))
  : typing Γ (Val x e1 e2) (Env (TBind x A Γ'))
.

#[local] Hint Constructors typing : core.

Definition mut_measure (c : type_case) (A : ty) : nat :=
  match c with
  | expr_case => 1 + ty_size A
  | val_case => ty_size A
  end.

Equations type_interp (c : type_case) (t : ty) (v : match c with val_case => value | expr_case => tm * env end) : Prop by wf (mut_measure c t) := {
  type_interp val_case (Env Nil) v :=
    match v with | Ctx _ => True | _ => False end;
  type_interp val_case (Env (TBind x A Γ)) v :=
    match v with
    | Ctx σ =>
      match fetch σ x with
      | None => False
      | Some v' => type_interp val_case A v'
      end /\ type_interp val_case (Env (remove Γ x)) v
    | _ => False
    end;
  type_interp val_case (Fun A B) v :=
    match v with
    | Closure x e σ =>
      forall v' (GOOD : type_interp val_case A v'),
        type_interp expr_case B (e, VBind x v' σ)
    | _ => False
    end;
  type_interp expr_case A (e, σ) :=
    exists v, type_interp val_case A v /\ eval (e, σ) v
}.

Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.

Lemma simp_interp_env Γ v :
  type_interp val_case (Env Γ) v =
  match v with
  | Ctx σ => type_interp val_case (Env Γ) v
  | _ => False
  end. 
Proof. destruct Γ; ii; simp type_interp; repeat des_goal; eauto. Qed.

Lemma remove_read Γ x x' :
  read (remove Γ x) x' =
    match String.eqb x' x with
    | true => None
    | false => read Γ x'
    end.
Proof.
  ginduction Γ; ii; ss; repeat des_goal;
  repeat rewrite eqb_eq in *; 
  repeat rewrite eqb_neq in *;
  clarify;
  solve [rw; rewrite eqb_refl; ss
    | rewrite <- eqb_neq in *; repeat rw; ss].
Qed.

Lemma remove_comm Γ x x' :
  remove (remove Γ x) x' = remove (remove Γ x') x.
Proof.
  induction Γ; ss; repeat des_goal; ss; rw; eauto.
Qed.

Lemma env_extend_aux Γ σ σ'
  (READ : forall x (DOM : read Γ x <> None),
    fetch σ' x = fetch σ x)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ))
  n (IND : tyenv_size Γ <= n) :
  type_interp val_case (Env Γ) (Ctx σ').
Proof.
  ginduction n; ii; ss.
  pose proof (tyenv_size_positive Γ); nia.
  destruct Γ; ss.
  simp type_interp in *.
  des_hyp; des; clarify.
  repeat rw. split. eauto.
  apply (IHn (remove Γ x) σ σ'); eauto.
  - ii. rewrite remove_read in DOM. apply READ.
    des_hyp; eauto.
  - pose proof (ty_size_positive A).
    pose proof (remove_size_dec Γ x). nia.
  - rewrite eqb_refl. ii. clarify.
Qed.

Lemma env_extend Γ σ σ'
  (READ : forall x (DOM : read Γ x <> None),
    fetch σ' x = fetch σ x)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ)) :
  type_interp val_case (Env Γ) (Ctx σ').
Proof. eapply env_extend_aux; eauto. Qed.

Lemma sep_env_aux Γ σ x n (IND : tyenv_size Γ <= n) :
  match read Γ x, fetch σ x with
  | Some _, None => False
  | Some A, Some v => type_interp val_case A v
  | _, _ => True
  end /\ type_interp val_case (Env (remove Γ x)) (Ctx σ) ->
  type_interp val_case (Env Γ) (Ctx σ).
Proof.
  ginduction n; ii;
  destruct Γ; ss; repeat des_hyp; des; 
  pose proof (tyenv_size_positive Γ); try nia;
  clarify.
  - rewrite eqb_eq in *; clarify.
    simp type_interp in *. rw. eauto.
  - simp type_interp in *.
    des_goal; des; clarify.
    split; eauto.
    apply (IHn _ _ x).
    pose proof (ty_size_positive A).
    pose proof (remove_size_dec Γ x0). nia.
    rewrite remove_read. rewrite remove_comm.
    repeat rw. eauto.
  - simp type_interp in *.
    des_goal; des; clarify.
    split; eauto.
    apply (IHn _ _ x).
    pose proof (ty_size_positive A).
    pose proof (remove_size_dec Γ x0). nia.
    rewrite remove_read. rewrite remove_comm.
    repeat rw. eauto.
Qed.

Lemma sep_env Γ σ x :
  match read Γ x, fetch σ x with
  | Some _, None => False
  | Some A, Some v => type_interp val_case A v
  | _, _ => True
  end /\ type_interp val_case (Env (remove Γ x)) (Ctx σ) ->
  type_interp val_case (Env Γ) (Ctx σ).
Proof. eapply sep_env_aux. eauto. Qed.

Lemma env_sep_aux Γ σ x n (IND : tyenv_size Γ <= n) :
  type_interp val_case (Env Γ) (Ctx σ) ->
  type_interp val_case (Env (remove Γ x)) (Ctx σ).
Proof.
  ginduction n; ii; ss. pose proof (tyenv_size_positive Γ). nia.
  destruct Γ; ss. pose proof (ty_size_positive A).
  des_goal.
  - rewrite eqb_eq in *. clarify.
    simp type_interp in H. apply H.
  - simp type_interp in *.
    des_hyp; des; clarify.
    split; eauto.
    rewrite remove_comm. apply IHn; eauto.
    pose proof (remove_size_dec Γ x0). nia.
Qed.

Lemma env_sep Γ σ x :
  type_interp val_case (Env Γ) (Ctx σ) ->
  type_interp val_case (Env (remove Γ x)) (Ctx σ).
Proof. eapply env_sep_aux; eauto. Qed.

Lemma read_subtype Γ Γ'
  (READ : forall x A, read Γ x = Some A ->
    exists A', read Γ' x = Some A' /\ subtype A A') :
  subtype (Env Γ) (Env Γ').
Proof.
  ginduction Γ'.
  - ii; ss. destruct Γ; ss.
    specialize (READ x A).
    rewrite eqb_refl in *.
    exploit READ; eauto.
    ii; des; clarify.
  - ii. rewrite simp_subtype_env. split.
    + apply IHΓ'. ii.
      rewrite remove_read in *. des_hyp.
      exploit READ; eauto.
      ii; des; ss. des_hyp; clarify. eauto.
    + des_goal; eauto.
      exploit READ; eauto.
      ii; des; ss. rewrite eqb_refl in *.
      clarify.
Qed.

Lemma subtype_read Γ Γ'
  (SUB : subtype (Env Γ) (Env Γ')) :
  forall x A, read Γ x = Some A ->
    exists A', read Γ' x = Some A' /\ subtype A A'.
Proof.
  ginduction Γ'; ii; ss.
  - destruct Γ; ss.
  - rewrite simp_subtype_env in SUB.
    des_goal. rewrite eqb_eq in *. clarify.
    exists A. rewrite H in *. des; eauto.
    eapply IHΓ'. des; eauto.
    rewrite remove_read. rw. eauto.
Qed.

Lemma subtype_remove Γ Γ' x (SUB : subtype (Env Γ) (Env Γ')) :
  subtype (Env (remove Γ x)) (Env (remove Γ' x)).
Proof.
  apply read_subtype. ii.
  specialize (subtype_read Γ Γ' SUB x0 A).
  rewrite remove_read in *. des_hyp.
  eauto.
Qed.

Lemma subtype_refl_aux A n (IND : ty_size A <= n) :
  subtype A A.
Proof.
  ginduction n; ii. pose proof (ty_size_positive A). nia.
  destruct A; ss.
  - apply read_subtype. intros x A READ.
    exists A. split; eauto.
    apply IHn.
    specialize (read_size_dec Γ x A READ). nia.
  - simp subtype. split; apply IHn; nia.
Qed.

Theorem subtype_refl A : subtype A A.
Proof. eapply subtype_refl_aux; eauto. Qed.

Lemma subtype_trans_aux A B C
  (SUBa : subtype A B)
  (SUBb : subtype B C) 
  n (IND : ty_size A + ty_size B + ty_size C <= n) :
  subtype A C.
Proof.
  ginduction n; ii. pose proof (ty_size_positive B). nia.
  destruct B; destruct A;
  try solve [destruct Γ; ss].
  - destruct C; try solve [destruct Γ; ss].
    apply read_subtype.
    ii. exploit (subtype_read Γ0); eauto.
    intros (A' & READ & SUB).
    pose proof (subtype_read Γ Γ1 SUBb x A' READ) as (A'' & READ' & SUB').
    exists A''.
    split; eauto.
    apply (IHn A A' A''); eauto.
    specialize (read_size_dec Γ0 x A H).
    specialize (read_size_dec Γ x A' READ).
    specialize (read_size_dec Γ1 x A'' READ').
    ss. nia.
  - destruct C; try solve [destruct Γ; ss].
    rewrite simp_subtype_fun in *.
    ss; des; split; eapply IHn; eauto; nia.
Qed.

Theorem subtype_trans A B C :
  subtype A B -> subtype B C -> subtype A C.
Proof. ii. eapply subtype_trans_aux; eauto. Qed.

(* A ≥ B => V[A] ⊇ V[B] *)
Lemma subtype_subset_aux A B (SUB : subtype A B)
  n (IND : ty_size A + ty_size B <= n) :
  forall v (GOOD : type_interp val_case B v),
    type_interp val_case A v.
Proof.
  ginduction n; ii; ss.
  pose proof (ty_size_positive A). nia.
  destruct B; destruct A; try destruct Γ; ss.
  - destruct Γ0; ss.
  - rewrite simp_subtype_env in SUB.
    simp type_interp in *; repeat des_hyp; des; clarify.
    + apply (sep_env _ _ x). repeat rw.
      split. eapply IHn; eauto.
      exploit (read_size_dec _ x t); eauto.
      specialize (tyenv_size_positive Γ). nia.
      specialize (remove_size_dec Γ x).
      specialize (remove_size Γ0 x). rw.
      specialize (ty_size_positive A). ii.
      eapply (IHn _ (Env (remove Γ x))); eauto.
      pose proof (remove_size (remove Γ0 x) x) as RR.
      rewrite remove_read in *. rewrite eqb_refl in *.
      rewrite <- RR.
      apply subtype_remove. eauto.
      s. nia.
    + apply (sep_env _ _ x). repeat rw.
      split; eauto.
      specialize (remove_size Γ0 x). rw. intros RR.
      rewrite RR in *.
      eapply (IHn _ (Env (remove Γ x))); eauto.
      rewrite <- RR. apply subtype_remove. eauto.
      pose proof (ty_size_positive A).
      pose proof (remove_size_dec Γ x). s. nia.
  - simp subtype in SUB. simp type_interp in *.
    des_hyp; clarify. ii.
    exploit (GOOD v').
    eapply IHn; eauto. apply SUB.
    pose proof (ty_size_positive A2). nia.
    ii. simp type_interp in *. des.
    exists v. split; eauto.
    eapply IHn; eauto.
    pose proof (ty_size_positive A1). nia.
Qed.

Lemma subtype_subset A B (SUB : subtype A B) :
  forall v (GOOD : type_interp val_case B v),
    type_interp val_case A v.
Proof. eapply subtype_subset_aux; eauto. Qed.

Lemma var_compatible_aux Γ x A σ n
  (IND : tyenv_size Γ <= n)
  (READ : read Γ x = Some A)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ)) :
  exists v, type_interp val_case A v /\ fetch σ x = Some v.
Proof.
  ginduction n; intros; destruct Γ; ss.
  - specialize (tyenv_size_positive Γ). nia.
  - simp type_interp in GOOD.
    repeat des_hyp; des; clarify.
    rewrite eqb_eq in *. clarify. exists v. eauto.
    match goal with
    | _ : context [remove ?Γ ?x] |- _ =>
      eapply (IHn (remove Γ x))
    end; eauto.
    t. pose proof (ty_size_positive A0). nia.
    rewrite remove_read. repeat rw. eauto.
Qed.

Lemma var_compatible Γ x A σ
  (READ : read Γ x = Some A)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ)) :
  exists v, type_interp val_case A v /\ fetch σ x = Some v.
Proof. eapply var_compatible_aux; eauto. Qed.

Lemma env_bind_compatible Γ A x v σ
  (Genv : type_interp val_case (Env Γ) (Ctx σ))
  (Gval : type_interp val_case A v) :
  type_interp val_case (Env (TBind x A Γ)) (Ctx (VBind x v σ)).
Proof.
  simp type_interp.
  s. rewrite eqb_refl. split; eauto.
  eapply (env_extend (remove Γ x) σ).
  ii. rewrite remove_read in DOM.
  s. des_hyp; clarify.
  apply env_sep. eauto.
Qed.

Theorem type_safety Γ e A (TYPE : typing Γ e A) :
  forall σ (GOOD : type_interp val_case (Env Γ) (Ctx σ)),
    type_interp expr_case A (e, σ).
Proof.
  induction TYPE; ii; simp type_interp in *.
  - exploit var_compatible; eauto. ii; des.
    eexists; split; eauto.
  - eexists; split; eauto.
    simp type_interp. ii.
    apply IHTYPE.
    apply env_bind_compatible; eauto.
  - exploit IHTYPE1; eauto. intros SEMTY1.
    simp type_interp in SEMTY1.
    destruct SEMTY1 as (v & SEMTY1 & EVAL1).
    simp type_interp in SEMTY1. des_hyp; clarify.
    exploit IHTYPE2; eauto. intros SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v & SEMTY2 & EVAL2).
    eapply subtype_subset in SEMTY2; eauto.
    eapply SEMTY1 in SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v' & SEMTY2 & EVAL3).
    exists v'. eauto.
  - exploit IHTYPE1; eauto. intros SEMTY1.
    simp type_interp in SEMTY1.
    destruct SEMTY1 as (v & SEMTY1 & EVAL1).
    rewrite simp_interp_env in SEMTY1. des_hyp; clarify.
    exploit IHTYPE2; eauto. intros SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v & SEMTY2 & EVAL2).
    exists v. eauto.
  - eexists; split; eauto. simp type_interp. eauto.
  - exploit IHTYPE1; eauto. intros SEMTY1.
    simp type_interp in SEMTY1.
    destruct SEMTY1 as (v & SEMTY1 & EVAL1).
    exploit (IHTYPE2 (VBind x v σ)).
    apply env_bind_compatible; eauto.
    intros SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v' & SEMTY2 & EVAL2).
    rewrite simp_interp_env in SEMTY2. des_ifs.
    eexists; split; eauto using env_bind_compatible.
Qed.

Corollary termination e A (TYPE : typing Nil e A) :
  forall σ, exists v, eval (e, σ) v.
Proof.
  ii. exploit (type_safety _ _ _ _ σ); ii; eauto.
  all:simp type_interp in *; des; eauto.
Qed.
