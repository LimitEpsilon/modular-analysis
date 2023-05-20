Require Export Coq.Init.Nat. 
Require Export Lia.

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

Inductive mod_tm :=
  | m_empty
  | m_var (M : mod_id)
  | m_lete (x : expr_id) (e : expr_tm) (m : mod_tm)
  | m_letm (M : mod_id) (m1 : mod_tm) (m2 : mod_tm)

with expr_tm :=
  | e_var (x : expr_id)
  | e_lam (x : expr_id) (e : expr_tm)
  | e_app (e1 : expr_tm) (e2 : expr_tm)
  | e_link (m : mod_tm) (e : expr_tm)
.

Inductive value : expr_tm -> Prop :=
  | v_fn (x : expr_id) (e : expr_tm) : value (e_lam x e)
.

Scheme expr_ind_mut := Induction for expr_tm Sort Prop
with mod_ind_mut := Induction for mod_tm Sort Prop.

Inductive ctx :=
  | c_hole
  | c_lam (x: expr_id) (C : ctx)
  | c_lete (x : expr_id) (C : ctx)
  | c_letm (M : mod_id) (C : ctx)
.

Fixpoint plugin_c Cout Cin :=
  match Cout with
  | c_hole => Cin
  | c_lam x C' => c_lam x (plugin_c C' Cin)
  | c_lete x C' => c_lete x (plugin_c C' Cin)
  | c_letm M C' => c_letm M (plugin_c C' Cin)
  end.

Definition time := nat.

Definition path := list time.

Definition update_t (t : time) := S t.

Definition eq_t (t1 t2 : time) := t1 =? t2.

Fixpoint eq_p (p1 p2 : path) :=
  match p1, p2 with
  | [], [] => true
  | hd1 :: tl1, [] => false
  | [], hd2 :: tl2 => false
  | hd1 :: tl1, hd2 :: tl2 =>
    if eq_t hd1 hd2 then eq_p tl1 tl2
                    else false
  end.

Definition len_p (p : path) := List.length p.

Definition eq_eid id1 id2 :=
  match id1, id2 with
  | eid x1, eid x2 => x1 =? x2
  end.

Definition eq_mid id1 id2 :=
  match id1, id2 with
  | mid M1, mid M2 => M1 =? M2
  end.

Fixpoint level (C : ctx) :=
  match C with
  | c_hole => 0
  | c_lam _ C'
  | c_lete _  C' 
  | c_letm _  C' => S (level C')
  end.

Fixpoint index_expr (C : ctx) (x : expr_id) :=
  match C with
  | c_hole => None
  | c_lam x' C' 
  | c_lete x' C' =>
    match index_expr C' x with
    | None => if eq_eid x x' then Some (level C') else None
    | Some i => Some i
    end
  | c_letm _ C' => index_expr C' x
  end.

Fixpoint index_expr_aux (C : ctx) (x : expr_id) (o : option nat) :=
  match C with
  | c_hole => o
  | c_lam x' C' 
  | c_lete x' C' => 
    if eq_eid x x' then (
      index_expr_aux C' x (Some 0)
    ) else (
      match o with
      | Some i => index_expr_aux C' x (Some (S i))
      | None => index_expr_aux C' x None
      end
    )
  | c_letm _ C' =>
    match o with
    | Some i => index_expr_aux C' x (Some (S i))
    | None => index_expr_aux C' x None
    end
  end.

Lemma index_expr_util1 :
  (forall C x x', index_expr (c_lam x' C) x = None ->
                  index_expr C x = None) /\
  (forall C x x', index_expr (c_lete x' C) x = None ->
                  index_expr C x = None) /\
  (forall C x M, index_expr (c_letm M C) x = None ->
                 index_expr C x = None) /\
  (forall C x m n, index_expr_aux C x None = Some n ->
                   index_expr_aux C x (Some m) = Some n).
Proof.
  repeat split; try (intros; simpl in *; destruct (index_expr C x); eauto; fail);
                induction C; eauto using ctx; intros; try (inversion H; fail);
                try (simpl in *; destruct (eq_eid x0 x); eauto; fail).
Qed.

Lemma index_expr_util2 : forall C n x (NOx : index_expr C x = None),
                        index_expr_aux C x (Some n) = Some (n + level C).
Proof.
  pose proof index_expr_util1 as H; destruct H as [LAM [LETe [LETm IRREL]]].
  induction C; eauto using ctx;
  induction n; intros; simpl; eauto; try (
  try (intros; simpl; fail);
  remember (eq_eid x0 x) as eid_sub; destruct eid_sub;
  try (simpl in NOx; rewrite <- Heqeid_sub in NOx;
  destruct (index_expr C x0); simpl in NOx; inversion NOx; fail));
  try (replace (S (n + S (level C))) with (S (S n) + level C) by eauto); eauto.
Qed.

Ltac index_expr_util :=
  pose proof index_expr_util1 as H; destruct H as [LAM [LETe [LETm IRREL]]];
  pose proof index_expr_util2 as LEVEL.

Lemma index_expr_eqv_None : forall C x (NOx : index_expr C x = None),
                        index_expr_aux C x None = None.
Proof.
  induction C; eauto using ctx; intros; simpl in NOx;
  remember (eq_eid x0 x) as eid_sub; destruct eid_sub;
  try (simpl; destruct (index_expr C x0) in NOx; inversion NOx; fail); 
  try (
    remember (index_expr C x0) as i_sub; destruct i_sub; inversion NOx;
    simpl; rewrite <- Heqeid_sub; apply IHC; eauto; fail).
Qed.

Lemma index_expr_eqv_Some : forall C x n (SOMEx : index_expr C x = Some n),
                               index_expr_aux C x None = Some n.
Proof.
  index_expr_util. induction C; eauto using ctx; intros.
  - simpl in SOMEx. remember (index_expr C x0) as i_sub. destruct i_sub.
    + rewrite SOMEx in *; clear SOMEx.
      simpl. remember (eq_eid x0 x) as eid_sub. destruct eid_sub;
      try apply IRREL; apply IHC; eauto.
    + remember (eq_eid x0 x) as eid_sub. destruct eid_sub.
      * rewrite <- SOMEx in *. simpl. rewrite <- Heqeid_sub. eauto.
      * inversion SOMEx.
  - simpl in SOMEx. remember (index_expr C x0) as i_sub. destruct i_sub.
    + rewrite SOMEx in *; clear SOMEx.
      simpl. remember (eq_eid x0 x) as eid_sub. destruct eid_sub;
      try apply IRREL; apply IHC; eauto.
    + remember (eq_eid x0 x) as eid_sub. destruct eid_sub.
      * rewrite <- SOMEx in *. simpl. rewrite <- Heqeid_sub. eauto.
      * inversion SOMEx.
Qed.

Theorem index_expr_eqv : forall C x, index_expr C x = index_expr_aux C x None.
Proof.
  intros. remember (index_expr C x) as i. destruct i.
  - symmetry. apply index_expr_eqv_Some; eauto.
  - symmetry. apply index_expr_eqv_None; eauto.
Qed.

Fixpoint index_mod (C : ctx) (M : mod_id) :=
  match C with
  | c_hole => None
  | c_lam _ C' 
  | c_lete _ C' => index_mod C' M
  | c_letm M' C' => 
    match index_mod C' M with
    | None => if eq_mid M M' then Some (level C') else None
    | Some i => Some i
    end
  end.

Fixpoint index_mod_aux (C : ctx) (M : mod_id) (o : option nat) :=
  match C with
  | c_hole => o
  | c_lam _ C'
  | c_lete _ C' =>
    match o with
    | Some i => index_mod_aux C' M (Some (S i))
    | None => index_mod_aux C' M None
    end
  | c_letm M' C' =>
    if eq_mid M M' then
      index_mod_aux C' M (Some 0)
    else match o with
      | Some i => index_mod_aux C' M (Some (S i))
      | None => index_mod_aux C' M None
    end
  end.

Fixpoint pop (p : path) (i : nat) := 
  match i with
  | 0 => Some p
  | S i' =>
    match p with
    | [] => None
    | _ :: tl => pop tl i'
    end
  end.

Inductive mod_value :=
  | Mod (p : path) (C : ctx)
.

(* a term, a proof, a path, a context *)
Inductive expr_value :=
  | Val (e : expr_tm) (v : value e) (p : path) (C : ctx)
.

Inductive state :=
  | ST (e_mem : path -> option expr_value)
       (m_mem : path -> option mod_value)
       (t : time)
.

Definition update_m {X} mem (p : path) (x : X) :=
  fun p1 => if eq_p p1 p then Some x else mem p1.

Definition empty_mem {X} (p : path) : option X := None.

Notation "p '!->' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Notation "Cout '[|' Cin '|]'" := (plugin_c Cout Cin)
                              (at level 100, Cin at next level, right associativity).

Inductive EevalR (p : path) (C : ctx) (st : state)
    : expr_tm -> expr_value -> state -> Prop :=
  | Eeval_var x i p_x v e_mem m_mem t
             (STATE : ST e_mem m_mem t = st)
             (INDEX : Some i = index_expr C x)
             (POP : Some p_x = pop p i)
             (ACCESS : Some v = e_mem p_x)
    : EevalR p C st (e_var x) v st
  | Eeval_lam x e
    : EevalR p C st (e_lam x e) 
            (Val (e_lam x e) (v_fn x e) p C) st
  | Eeval_app e1 e2 
              x e p_lam C_lam st_lam
              arg e_mem m_mem t
              v st_v
              (FN : EevalR p C st e1
                           (Val (e_lam x e) (v_fn x e) p_lam C_lam) st_lam)
              (ARG : EevalR p C st_lam e2
                            arg (ST e_mem m_mem t))
              (BODY : EevalR (t :: p_lam) (C_lam [|c_lam x c_hole|])
                             (ST ((t :: p_lam) !-> arg ; e_mem) m_mem (update_t t))
                              e v st_v)
    : EevalR p C st (e_app e1 e2) v st_v
  | Eeval_link m e p_m C_m st_m v st_v
               (MOD : MevalR p C st m (Mod p_m C_m) st_m)
               (LINK : EevalR p_m C_m st_m e v st_v)
    : EevalR p C st (e_link m e) v st_v

with MevalR (p : path) (C : ctx) (st : state)
    : mod_tm -> mod_value -> state -> Prop :=
  | Meval_empty
    : MevalR p C st m_empty (Mod p C) st
  | Meval_var M i p_M v e_mem m_mem t
              (STATE : ST e_mem m_mem t = st)
              (INDEX : Some i = index_mod C M)
              (POP : Some p_M = pop p i)
              (ACCESS : Some v = m_mem p_M)
    : MevalR p C st (m_var M) v st
  | Meval_lete x e v_e e_mem m_mem t
               m v_m st_m
               (EVALe : EevalR p C st e v_e (ST e_mem m_mem t))
               (EVALm : MevalR (t :: p) (C [|c_lete x c_hole|]) 
                        (ST ((t :: p) !-> v_e ; e_mem) m_mem (update_t t))
                        m v_m st_m)
    : MevalR p C st (m_lete x e m) v_m st_m
  | Meval_letm M m1 v_m1 e_mem m_mem t
               m2 v_m2 st_m2
               (EVALm1 : MevalR p C st m1 v_m1 (ST e_mem m_mem t))
               (EVALm2 : MevalR (t :: p) (C [|c_letm M c_hole|])
                         (ST e_mem ((t :: p) !-> v_m1 ; m_mem) (update_t t))
                         m2 v_m2 st_m2)
    : MevalR p C st (m_letm M m1 m2) v_m2 st_m2
.

Scheme EevalR_ind_mut := Induction for EevalR Sort Prop
with MevalR_ind_mut := Induction for MevalR Sort Prop.

Definition Reach (tm1 tm2 : Type) := tm1 -> path -> ctx -> state -> tm2 -> Prop.

(* Reachability relation *)
Inductive EreachE (p : path) (C : ctx) (st : state)
    : Reach expr_tm expr_tm :=
  | ere_refl e
    : EreachE p C st e 
              p C st e
  | ere_var x i e_mem m_mem t p_x e' pf p' C'
            (STATE : st = ST e_mem m_mem t)
            (INDEX : Some i = index_expr C x)
            (POP : Some p_x = pop p i)
            (ACCESS : Some (Val e' pf p' C') = e_mem p_x)
    : EreachE p C st (e_var x)
              p' C' st e'
  | ere_app_left e1 e2 p' C' st' e'
                 (REACHl : EreachE p C st e1
                                   p' C' st' e')
    : EreachE p C st (e_app e1 e2) 
              p' C' st' e'
  | ere_app_right e1 e2 p1 C1 st1 v1 p' C' st' e'
                  (FN : EreachE p C st e1
                                p1 C1 st1 v1)
                  (FNV : value v1)
                  (REACHr : EreachE p C st1 e2
                                    p' C' st' e')
    : EreachE p C st (e_app e1 e2)
              p' C' st' e'
  | ere_app_body e1 e2 x e p_lam C_lam st_lam
                 p_arg C_arg arg e_mem m_mem t
                 p' C' st' e'
                 (FN : EreachE p C st e1 
                               p_lam C_lam st_lam (e_lam x e))
                 (ARG : EreachE p C st_lam e2
                                p_arg C_arg (ST e_mem m_mem t) arg)
                 (ARGV : value arg)
                 (REACHb : EreachE (t :: p_lam) (C_lam[|c_lam x c_hole|]) 
                                   (ST ((t :: p_lam) !-> (Val arg ARGV p_arg C_arg) ; e_mem) m_mem (update_t t)) e
                                    p' C' st' e')
    : EreachE p C st (e_app e1 e2)
              p' C' st' e'
  | ere_link_m m e p' C' st' e'
               (REACHm : MreachE p C st m
                                 p' C' st' e')
    : EreachE p C st (e_link m e)
              p' C' st' e'
  | ere_link_e m e p_m C_m st_m p' C' st' e'
               (MOD : MreachM p C st m 
                              p_m C_m st_m m_empty)
               (REACHe : EreachE p_m C_m st_m e
                                 p' C' st' e')
    : EreachE p C st (e_link m e)
              p' C' st' e'

with MreachE (p : path) (C : ctx) (st : state)
    : Reach mod_tm expr_tm :=
  | mre_lete_e x e m p' C' st' e'
               (REACHe : EreachE p C st e
                                 p' C' st' e')
    : MreachE p C st (m_lete x e m)
              p' C' st' e'
  | mre_lete_m x e m p1 C1 v e_mem m_mem t
             p' C' st' e'
             (EVALx : EreachE p C st e
                              p1 C1 (ST e_mem m_mem t) v)
             (xV : value v)
             (REACHm : MreachE (t :: p) (C[|c_lete x c_hole|])
                               (ST ((t :: p) !-> (Val v xV p1 C1) ; e_mem) m_mem (update_t t)) m
                                p' C' st' e')
    : MreachE p C st (m_lete x e m)
              p' C' st' e'
  | mre_letm_m1 M m1 m2 p' C' st' e'
               (REACHm : MreachE p C st m1
                                 p' C' st' e')
    : MreachE p C st (m_letm M m1 m2)
              p' C' st' e'
  | mre_letm_m2 M m1 m2 p1 C1 e_mem m_mem t
             p' C' st' e'
             (EVALM : MreachM p C st m1
                              p1 C1 (ST e_mem m_mem t) m_empty)
             (REACHm : MreachE (t :: p) (C[|c_letm M c_hole|]) 
                               (ST e_mem ((t :: p) !-> (Mod p1 C1) ; m_mem) (update_t t)) m2
                                p' C' st' e')
    : MreachE p C st (m_letm M m1 m2)
              p' C' st' e'

with MreachM (p : path) (C : ctx) (st : state)
    : Reach mod_tm mod_tm :=
  | mrm_refl m
    : MreachM p C st m
              p C st m
  | mrm_var M i e_mem m_mem t p_M p' C'
            (STATE : st = ST e_mem m_mem t)
            (INDEX : Some i = index_mod C M)
            (POP : Some p_M = pop p i)
            (ACCESS : Some (Mod p' C') = m_mem p_M)
    : MreachM p C st (m_var M)
              p' C' st m_empty
  | mrm_lete_e x e m p' C' st' m'
               (REACHe : EreachM p C st e
                                 p' C' st' m')
    : MreachM p C st (m_lete x e m)
              p' C' st' m'
  | mrm_lete_m x e m p1 C1 v e_mem m_mem t
             p' C' st' m'
             (EVALx : EreachE p C st e 
                              p1 C1 (ST e_mem m_mem t) v)
             (xV : value v)
             (REACHm : MreachM (t :: p) (C[|c_lete x c_hole|]) 
                               (ST ((t :: p) !-> (Val v xV p1 C1) ; e_mem) m_mem (update_t t)) m
                                p' C' st' m')
    : MreachM p C st (m_lete x e m)
              p' C' st' m'
  | mrm_letm_m1 M m1 m2 p' C' st' m'
               (REACHm : MreachM p C st m1
                                 p' C' st' m')
    : MreachM p C st (m_letm M m1 m2)
              p' C' st' m'
  | mrm_letm_m2 M m1 m2 p1 C1 e_mem m_mem t
             p' C' st' m'
             (EVALM : MreachM p C st m1 
                              p1 C1 (ST e_mem m_mem t) m_empty)
             (REACHm : MreachM (t :: p) (C[|c_letm M c_hole|]) 
                               (ST e_mem ((t :: p) !-> (Mod p1 C1) ; m_mem) (update_t t)) m2
                                p' C' st' m')
    : MreachM p C st (m_letm M m1 m2)
              p' C' st' m'

with EreachM (p : path) (C : ctx) (st : state)
    : Reach expr_tm mod_tm :=
  | erm_app_left e1 e2 p' C' st' m'
                 (REACHl : EreachM p C st e1
                                   p' C' st' m')
    : EreachM p C st (e_app e1 e2) 
              p' C' st' m'
  | erm_app_right e1 e2 p1 C1 v1 st1 p' C' st' m'
                  (FN : EreachE p C st e1 
                                p1 C1 st1 v1)
                  (FNV : value v1)
                  (REACHr : EreachM p C st1 e2
                                    p' C' st' m')
    : EreachM p C st (e_app e1 e2)
              p' C' st' m'
  | erm_app_body e1 e2 x e p_lam C_lam st_lam
                 p_arg C_arg arg e_mem m_mem t
                 p' C' st' m'
                 (FN : EreachE p C st e1 
                               p_lam C_lam st_lam (e_lam x e))
                 (ARG : EreachE p C st_lam e2
                                p_arg C_arg (ST e_mem m_mem t) arg)
                 (ARGV : value arg)
                 (REACHb : EreachM (t :: p_lam) (C_lam[|c_lam x c_hole|]) 
                                   (ST ((t :: p_lam) !-> (Val arg ARGV p_arg C_arg) ; e_mem) m_mem (update_t t)) e
                                    p' C' st' m')
    : EreachM p C st (e_app e1 e2)
              p' C' st' m'
  | erm_link_m m e p' C' st' m'
               (REACHm : MreachM p C st m
                                 p' C' st' m')
    : EreachM p C st (e_link m e)
              p' C' st' m'
  | erm_link_e m e p_m C_m st_m p' C' st' m'
               (MOD : MreachM p C st m p_m C_m st_m m_empty)
               (REACHe : EreachM p_m C_m st_m e
                                 p' C' st' m')
    : EreachM p C st (e_link m e)
              p' C' st' m'
.

Scheme EreachE_ind_mut := Induction for EreachE Sort Prop
with EreachM_ind_mut := Induction for EreachM Sort Prop
with MreachE_ind_mut := Induction for MreachE Sort Prop
with MreachM_ind_mut := Induction for MreachM Sort Prop.

Notation "'<e|' p1 C1 st1 tm1 '~>' p2 C2 st2 tm2 '|e>'" := (EreachE p1 C1 st1 tm1 p2 C2 st2 tm2) 
                                               (at level 10, 
                                                p1 at next level, C1 at next level, st1 at next level, tm1 at next level,
                                                p2 at next level, C2 at next level, st2 at next level, tm2 at next level).

Notation "'<m|' p1 C1 st1 tm1 '~>' p2 C2 st2 tm2 '|e>'" := (MreachE p1 C1 st1 tm1 p2 C2 st2 tm2) 
                                               (at level 10, 
                                                p1 at next level, C1 at next level, st1 at next level, tm1 at next level,
                                                p2 at next level, C2 at next level, st2 at next level, tm2 at next level).

Notation "'<m|' p1 C1 st1 tm1 '~>' p2 C2 st2 tm2 '|m>'" := (MreachM p1 C1 st1 tm1 p2 C2 st2 tm2) 
                                               (at level 10, 
                                                p1 at next level, C1 at next level, st1 at next level, tm1 at next level,
                                                p2 at next level, C2 at next level, st2 at next level, tm2 at next level).

Notation "'<e|' p1 C1 st1 tm1 '~>' p2 C2 st2 tm2 '|m>'" := (EreachM p1 C1 st1 tm1 p2 C2 st2 tm2) 
                                               (at level 10, 
                                                p1 at next level, C1 at next level, st1 at next level, tm1 at next level,
                                                p2 at next level, C2 at next level, st2 at next level, tm2 at next level).

Check EreachE_ind_mut.

(* sanity check *)
Lemma ere_trans : forall p1 C1 st1 e1
                         p2 C2 st2 e2
                         p3 C3 st3 e3
                         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)
                         (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 e3 |e>),
                         <e| p1 C1 st1 e1 ~> p3 C3 st3 e3 |e>.
Proof.
  intros. generalize dependent e3.
  revert p3 C3 st3.
  apply (EreachE_ind_mut
    (fun p1 C1 st1 e1 
         p2 C2 st2 e2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)=> 
         forall p3 C3 st3 e3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 e3 |e>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 e3 |e>)
    (fun p1 C1 st1 e1 
         p2 C2 st2 m2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 e3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 e3 |e>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 e3 |e>)
    (fun p1 C1 st1 m1
         p2 C2 st2 e2
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>) =>
         forall p3 C3 st3 e3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 e3 |e>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 e3 |e>)
    (fun p1 C1 st1 m1 
         p2 C2 st2 m2 
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 e3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 e3 |e>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 e3 |e>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma mrm_trans : forall p1 C1 st1 m1
                         p2 C2 st2 m2
                         p3 C3 st3 m3
                         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>)
                         (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 m3 |m>),
                         <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>.
Proof.
  intros. generalize dependent m3.
  revert p3 C3 st3.
  apply (MreachM_ind_mut
    (fun p1 C1 st1 e1 
         p2 C2 st2 e2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)=> 
         forall p3 C3 st3 m3
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 m3 |m>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 e1 
         p2 C2 st2 m2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 m3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 m3 |m>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 m1
         p2 C2 st2 e2
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>) =>
         forall p3 C3 st3 m3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 m3 |m>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 m1 
         p2 C2 st2 m2 
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 m3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 m3 |m>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma ermre_trans : forall p1 C1 st1 e1
                           p2 C2 st2 m2
                           p3 C3 st3 e3
                           (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>)
                           (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 e3 |e>),
                           <e| p1 C1 st1 e1 ~> p3 C3 st3 e3 |e>. 
Proof.
  intros. generalize dependent e3.
  revert p3 C3 st3.
  apply (EreachM_ind_mut
    (fun p1 C1 st1 e1 
         p2 C2 st2 e2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)=> 
         forall p3 C3 st3 e3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 e3 |e>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 e3 |e>)
    (fun p1 C1 st1 e1 
         p2 C2 st2 m2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 e3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 e3 |e>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 e3 |e>)
    (fun p1 C1 st1 m1
         p2 C2 st2 e2
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>) =>
         forall p3 C3 st3 e3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 e3 |e>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 e3 |e>)
    (fun p1 C1 st1 m1 
         p2 C2 st2 m2 
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 e3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 e3 |e>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 e3 |e>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma mrerm_trans : forall p1 C1 st1 m1
                           p2 C2 st2 e2
                           p3 C3 st3 m3
                           (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>)
                           (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 m3 |m>),
                           <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>. 
Proof.
  intros. generalize dependent m3.
  revert p3 C3 st3.
  apply (MreachE_ind_mut
    (fun p1 C1 st1 e1 
         p2 C2 st2 e2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)=> 
         forall p3 C3 st3 m3
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 m3 |m>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 e1 
         p2 C2 st2 m2 
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 m3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 m3 |m>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 m1
         p2 C2 st2 e2
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>) =>
         forall p3 C3 st3 m3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 m3 |m>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 m1 
         p2 C2 st2 m2 
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 m3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 m3 |m>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma c_plugin_assoc : forall C1 C2 C3, C1[| C2[| C3 |] |] = ((C1[|C2|])[|C3|]).
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
Qed.

Lemma c_plugin_adds_level : forall C1 C2, level(C1[|C2|]) = level C1 + level C2.
Proof.
  induction C1; eauto;
  intros; simpl; try rewrite IHC1; eauto.
Qed.

Definition st_len e_mem m_mem p C :=
        (forall (addr : path) v pf p' C', 
                e_mem addr = Some (Val v pf p' C') ->
                len_p p + level C' = len_p p' + level C) /\
        (forall (addr : path) p' C',
                m_mem addr = Some (Mod p' C') ->
                len_p p + level C' = len_p p' + level C).

Lemma ere_p_is_level : 
    forall p1 C1 st1 e1
           p2 C2 st2 e2
          (REACH : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)
           e_mem1 m_mem1 t1 e_mem2 m_mem2 t2
          (STATE1 : st1 = ST e_mem1 m_mem1 t1)
          (STATE2 : st2 = ST e_mem2 m_mem2 t2)
          (INIT : st_len e_mem1 m_mem1 p1 C1),
        st_len e_mem2 m_mem2 p1 C1 /\
        len_p p1 + level C2 = len_p p2 + level C1.
Proof. 
  apply (EreachE_ind_mut
    (fun p1 C1 st1 e1 
         p2 C2 st2 e2 
         (REACH : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>) =>
         forall e_mem1 m_mem1 t1 e_mem2 m_mem2 t2
            (STATE1 : st1 = ST e_mem1 m_mem1 t1)
            (STATE2 : st2 = ST e_mem2 m_mem2 t2)
            (INIT : st_len e_mem1 m_mem1 p1 C1),
            st_len e_mem2 m_mem2 p1 C1 /\
            len_p p1 + level C2 = len_p p2 + level C1)
    (fun p1 C1 st1 e1 
         p2 C2 st2 m2 
         (REACH : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>) =>
         forall e_mem1 m_mem1 t1 e_mem2 m_mem2 t2
            (STATE1 : st1 = ST e_mem1 m_mem1 t1)
            (STATE2 : st2 = ST e_mem2 m_mem2 t2)
            (INIT : st_len e_mem1 m_mem1 p1 C1),
            st_len e_mem2 m_mem2 p1 C1 /\
            len_p p1 + level C2 = len_p p2 + level C1)
    (fun p1 C1 st1 m1 
         p2 C2 st2 e2
         (REACH : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>) =>
         forall e_mem1 m_mem1 t1 e_mem2 m_mem2 t2
            (STATE1 : st1 = ST e_mem1 m_mem1 t1)
            (STATE2 : st2 = ST e_mem2 m_mem2 t2)
            (INIT : st_len e_mem1 m_mem1 p1 C1),
            st_len e_mem2 m_mem2 p1 C1 /\
            len_p p1 + level C2 = len_p p2 + level C1)
    (fun p1 C1 st1 m1 
         p2 C2 st2 m2 
         (REACH : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>) =>
         forall e_mem1 m_mem1 t1 e_mem2 m_mem2 t2
            (STATE1 : st1 = ST e_mem1 m_mem1 t1)
            (STATE2 : st2 = ST e_mem2 m_mem2 t2)
            (INIT : st_len e_mem1 m_mem1 p1 C1),
            st_len e_mem2 m_mem2 p1 C1 /\
            len_p p1 + level C2 = len_p p2 + level C1));
   unfold st_len in *; repeat split; simpl in *;
   try inversion INIT as [INITe INITm]; eauto;
   try rewrite STATE1 in *; inversion STATE2; subst; eauto;
   try (inversion STATE; subst; eauto; fail);
   try (eapply (H e_mem1 m_mem1 t1 e_mem2 m_mem2 t2); eauto; fail);
   try (destruct st1 as [e_mem3 m_mem3 t3]; subst;
        eapply (H0 e_mem3 m_mem3 t3 e_mem2 m_mem2 t2); eauto;
        eapply (H e_mem1 m_mem1 t1 e_mem3 m_mem3 t3); eauto; fail);
   intros; 
   try destruct st_lam as [e_mem3 m_mem3 t3]; subst;
   try destruct st_m as [e_mem3 m_mem3 t3]; subst;
   try specialize (H e_mem1 m_mem1 t1 e_mem3 m_mem3 t3 eq_refl eq_refl);
   try specialize (H0 e_mem3 m_mem3 t3 e_mem m_mem t eq_refl eq_refl);
   try specialize (H1 (t :: p_lam !-> Val arg ARGV p_arg C_arg; e_mem) m_mem (update_t t)
                   e_mem2 m_mem2 t2 eq_refl eq_refl);
   try apply H in INIT; destruct INIT as [INIT' EQ'];
   try apply H0 in INIT'; try destruct INIT' as [INIT'' EQ''];
   try destruct INIT'' as [INITe' INITm'];
   try (specialize (H0 e_mem3 m_mem3 t3 e_mem2 m_mem2 t2 eq_refl eq_refl);
       destruct H as [A B]; eauto;
       destruct A as [INITe' INITm']).
   - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            (t :: p_lam !-> Val arg ARGV p_arg C_arg; e_mem) addr =
            Some (Val v pf p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|]))).
    {
        split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p_lam));
        rewrite c_plugin_adds_level; simpl; 
        replace (level C_lam + 1) with (S (level C_lam)) by nia;
        try inversion H4; subst;
        assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
     }
     apply H1 in H4. destruct H4 as [INIT''' EQ'''].
     rewrite c_plugin_adds_level in *. simpl in *.
     replace (level C_lam + 1) with (S (level C_lam)) in * by nia.
     destruct INIT''' as [INITe'' INITm''].
     assert (S (len_p p_lam + level C'0) = len_p p'0 + S (level C_lam)). eauto.
     nia.
   - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
        (p' : path) (C' : ctx),
        (t :: p_lam !-> Val arg ARGV p_arg C_arg; e_mem) addr =
        Some (Val v pf p' C') ->
        S (len_p p_lam + level C') =
        len_p p' + level (C_lam [|c_lam x c_hole|])) /\
        (forall (addr p' : path) (C' : ctx),
        m_mem addr = Some (Mod p' C') ->
        S (len_p p_lam + level C') =
        len_p p' + level (C_lam [|c_lam x c_hole|]))).
    {
        split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p_lam));
        rewrite c_plugin_adds_level; simpl; 
        replace (level C_lam + 1) with (S (level C_lam)) by nia;
        try inversion H4; subst;
        assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
     }
     apply H1 in H4. destruct H4 as [INIT''' EQ'''];
     rewrite c_plugin_adds_level in *. simpl in *.
     replace (level C_lam + 1) with (S (level C_lam)) in * by nia.
     destruct INIT''' as [INITe'' INITm''].
     assert (S (len_p p_lam + level C'0) = len_p p'0 + S (level C_lam)). eauto.
     nia.
   - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
        (p' : path) (C' : ctx),
        (t :: p_lam !-> Val arg ARGV p_arg C_arg; e_mem) addr =
        Some (Val v pf p' C') ->
        S (len_p p_lam + level C') =
        len_p p' + level (C_lam [|c_lam x c_hole|])) /\
        (forall (addr p' : path) (C' : ctx),
        m_mem addr = Some (Mod p' C') ->
        S (len_p p_lam + level C') =
        len_p p' + level (C_lam [|c_lam x c_hole|]))).
    {
        split; intros; unfold update_m in *; destruct (eq_p addr (t :: p_lam));
        rewrite c_plugin_adds_level; simpl; 
        replace (level C_lam + 1) with (S (level C_lam)) by nia;
        try inversion H3; subst;
        assert (len_p p + level C'0 = len_p p'0 + level C); eauto; try nia.
     }
     apply H1 in H3. destruct H3 as [INIT''' EQ'''];
     rewrite c_plugin_adds_level in *. simpl in *.
     replace (level C_lam + 1) with (S (level C_lam)) in * by nia.
     destruct INIT''' as [INITe'' INITm''].
     assert (S (len_p p_lam + level C') = len_p p' + S (level C_lam)). eauto.
     nia.
   - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem3 addr = Some (Val v pf p' C') ->
            len_p p_m + level C' = len_p p' + level C_m) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem3 addr = Some (Mod p' C') ->
            len_p p_m + level C' = len_p p' + level C_m)).
    {
        split; intros;
        assert (len_p p + level C'1 = len_p p'1 + level C); eauto; nia.
    }
    apply H0 in H. 
    destruct H as [[INITe'' INITm''] EQ'''].
    assert (len_p p_m + level C'0 = len_p p'0 + level C_m); eauto. nia.
  - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem3 addr = Some (Val v pf p' C') ->
            len_p p_m + level C' = len_p p' + level C_m) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem3 addr = Some (Mod p' C') ->
            len_p p_m + level C' = len_p p' + level C_m)).
    {
        split; intros;
        assert (len_p p + level C'1 = len_p p'1 + level C); eauto; nia.
    }
    apply H0 in H. 
    destruct H as [[INITe'' INITm''] EQ'''].
    assert (len_p p_m + level C'0 = len_p p'0 + level C_m); eauto. nia.
 - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem3 addr = Some (Val v pf p' C') ->
            len_p p_m + level C' = len_p p' + level C_m) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem3 addr = Some (Mod p' C') ->
            len_p p_m + level C' = len_p p' + level C_m)).
    {
        split; intros;
        assert (len_p p + level C'0 = len_p p'0 + level C); eauto; nia.
    }
    apply H0 in H. 
    destruct H as [[INITe'' INITm''] EQ'''].
    assert (len_p p_m + level C' = len_p p' + level C_m); eauto. nia.
  - assert (H1' : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            (t :: p_lam !-> Val arg ARGV p_arg C_arg; e_mem) addr =
            Some (Val v pf p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p_lam));
      rewrite c_plugin_adds_level; simpl; 
      replace (level C_lam + 1) with (S (level C_lam)) by nia;
      try inversion H4; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H1 in H1'; clear H1. destruct H1' as [INIT'' EQ].
    destruct INIT'' as [INITe'' INITm''].
    assert (H3' : S (len_p p_lam + level C'0) =
                len_p p'0 + level (C_lam [|c_lam x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - assert (H1' : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            (t :: p_lam !-> Val arg ARGV p_arg C_arg; e_mem) addr =
            Some (Val v pf p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p_lam));
      rewrite c_plugin_adds_level; simpl; 
      replace (level C_lam + 1) with (S (level C_lam)) by nia;
      try inversion H4; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H1 in H1'; clear H1. destruct H1' as [INIT'' EQ].
    destruct INIT'' as [INITe'' INITm''].
    assert (H3' : S (len_p p_lam + level C'0) =
                len_p p'0 + level (C_lam [|c_lam x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - assert (H1' : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            (t :: p_lam !-> Val arg ARGV p_arg C_arg; e_mem) addr =
            Some (Val v pf p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p_lam + level C') =
            len_p p' + level (C_lam [|c_lam x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr (t :: p_lam));
      rewrite c_plugin_adds_level; simpl; 
      replace (level C_lam + 1) with (S (level C_lam)) by nia;
      try inversion H3; subst;
      assert (len_p p + level C'0 = len_p p'0 + level C); eauto; try nia.
    }
    apply H1 in H1'; clear H1. destruct H1' as [INIT'' EQ].
    destruct INIT'' as [INITe'' INITm''].
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem3 addr = Some (Val v pf p' C') ->
            len_p p_m + level C' = len_p p' + level C_m) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem3 addr = Some (Mod p' C') ->
            len_p p_m + level C' = len_p p' + level C_m)).
    {
        split; intros;
        assert (len_p p + level C'1 = len_p p'1 + level C); eauto; nia.
    }
    apply H0 in H. 
    destruct H as [[INITe'' INITm''] EQ'''].
    assert (len_p p_m + level C'0 = len_p p'0 + level C_m); eauto. nia.
  - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem3 addr = Some (Val v pf p' C') ->
            len_p p_m + level C' = len_p p' + level C_m) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem3 addr = Some (Mod p' C') ->
            len_p p_m + level C' = len_p p' + level C_m)).
    {
        split; intros;
        assert (len_p p + level C'1 = len_p p'1 + level C); eauto; nia.
    }
    apply H0 in H. 
    destruct H as [[INITe'' INITm''] EQ'''].
    assert (len_p p_m + level C'0 = len_p p'0 + level C_m); eauto. nia.
  - assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem3 addr = Some (Val v pf p' C') ->
            len_p p_m + level C' = len_p p' + level C_m) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem3 addr = Some (Mod p' C') ->
            len_p p_m + level C' = len_p p' + level C_m)).
    {
        split; intros;
        assert (len_p p + level C'0 = len_p p'0 + level C); eauto; nia.
    }
    apply H0 in H. 
    destruct H as [[INITe'' INITm''] EQ'''].
    assert (len_p p_m + level C' = len_p p' + level C_m); eauto. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 (t :: p !-> Val v xV p1 C1; e_mem) m_mem (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v0 : expr_tm) (pf : value v0) 
            (p' : path) (C' : ctx),
            (t :: p !-> Val v xV p1 C1; e_mem) addr = Some (Val v0 pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_lete x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 (t :: p !-> Val v xV p1 C1; e_mem) m_mem (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v0 : expr_tm) (pf : value v0) 
            (p' : path) (C' : ctx),
            (t :: p !-> Val v xV p1 C1; e_mem) addr = Some (Val v0 pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_lete x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 (t :: p !-> Val v xV p1 C1; e_mem) m_mem (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v0 : expr_tm) (pf : value v0) 
            (p' : path) (C' : ctx),
            (t :: p !-> Val v xV p1 C1; e_mem) addr = Some (Val v0 pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'0 = len_p p'0 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C') =
                len_p p' + level (C [|c_lete x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 e_mem (t :: p !-> Mod p1 C1; m_mem) (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem addr = Some (Val v pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            (t :: p !-> Mod p1 C1; m_mem) addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_letm M c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 e_mem (t :: p !-> Mod p1 C1; m_mem) (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem addr = Some (Val v pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            (t :: p !-> Mod p1 C1; m_mem) addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_letm M c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 e_mem (t :: p !-> Mod p1 C1; m_mem) (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem addr = Some (Val v pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            (t :: p !-> Mod p1 C1; m_mem) addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'0 = len_p p'0 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C') =
                len_p p' + level (C [|c_letm M c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 (t :: p !-> Val v xV p1 C1; e_mem) m_mem (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v0 : expr_tm) (pf : value v0) 
            (p' : path) (C' : ctx),
            (t :: p !-> Val v xV p1 C1; e_mem) addr = Some (Val v0 pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_lete x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 (t :: p !-> Val v xV p1 C1; e_mem) m_mem (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v0 : expr_tm) (pf : value v0) 
            (p' : path) (C' : ctx),
            (t :: p !-> Val v xV p1 C1; e_mem) addr = Some (Val v0 pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_lete x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 (t :: p !-> Val v xV p1 C1; e_mem) m_mem (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v0 : expr_tm) (pf : value v0) 
            (p' : path) (C' : ctx),
            (t :: p !-> Val v xV p1 C1; e_mem) addr = Some (Val v0 pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_lete x c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'0 = len_p p'0 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C') =
                len_p p' + level (C [|c_lete x c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 e_mem (t :: p !-> Mod p1 C1; m_mem) (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem addr = Some (Val v pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            (t :: p !-> Mod p1 C1; m_mem) addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_letm M c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 e_mem (t :: p !-> Mod p1 C1; m_mem) (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem addr = Some (Val v pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            (t :: p !-> Mod p1 C1; m_mem) addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr0 (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'1 = len_p p'1 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C'0) =
                len_p p'0 + level (C [|c_letm M c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
  - specialize (H e_mem1 m_mem1 t1 e_mem m_mem t eq_refl eq_refl).
    specialize (H0 e_mem (t :: p !-> Mod p1 C1; m_mem) (update_t t)
                    e_mem2 m_mem2 t2 eq_refl eq_refl).
    assert (RR : (forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem1 addr = Some (Val v pf p' C') ->
            len_p p + level C' = len_p p' + level C) /\
            (forall (addr p' : path) (C' : ctx),
            m_mem1 addr = Some (Mod p' C') ->
            len_p p + level C' = len_p p' + level C)). 
    { split; eauto. }
    apply H in RR; clear H; destruct RR as [[INITe' INITm'] EQ].
    assert ((forall (addr : path) (v : expr_tm) (pf : value v) 
            (p' : path) (C' : ctx),
            e_mem addr = Some (Val v pf p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|])) /\
            (forall (addr p' : path) (C' : ctx),
            (t :: p !-> Mod p1 C1; m_mem) addr = Some (Mod p' C') ->
            S (len_p p + level C') = len_p p' + level (C [|c_letm M c_hole|]))).
    {
      split; intros; unfold update_m in *; destruct (eq_p addr (t :: p));
      rewrite c_plugin_adds_level; simpl;
      replace (level C + 1) with (S (level C)) by nia;
      try inversion H; subst;
      assert (len_p p + level C'0 = len_p p'0 + level C); eauto; try nia.
    }
    apply H0 in H; clear H0; destruct H as [[INITe'' INITm''] EQ''].
    assert (H3' : S (len_p p + level C') =
                len_p p' + level (C [|c_letm M c_hole|])); eauto.
    rewrite c_plugin_adds_level in *; simpl in *. nia.
Qed.

Theorem p_len_eq_level : forall st e p' C' st' e' e_mem m_mem t
        (REACH : <e| [] c_hole st e ~> p' C' st' e' |e>)
        (STATE1 : st = ST empty_mem empty_mem 0)
        (STATE2 : st' = ST e_mem m_mem t),
        st_len e_mem m_mem [] c_hole /\
        len_p p' = level C'.
Proof.
  intros.
  assert (INIT : st_len empty_mem empty_mem [] c_hole).
  { split; intros; inversion H. }
  specialize (ere_p_is_level [] c_hole st e
                             p' C' st' e'
                             REACH empty_mem empty_mem 0 e_mem m_mem t
                             STATE1 STATE2 INIT) as [FST SND].
  simpl in *. split; eauto; try nia.
Qed.

Theorem eval_then_reach : forall p1 C1 st1 e1 v st2
                                 (EVAL : EevalR p1 C1 st1 e1 v st2)
                                 e2 pf p2 C2
                                 (VAL : v = Val e2 pf p2 C2),
                                 <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>.
Proof.
  apply (EevalR_ind_mut 
            (fun p1 C1 st1 e1 v st2
                 (EVAL : EevalR p1 C1 st1 e1 v st2) =>
                 forall e2 pf p2 C2
                        (VAL : v = Val e2 pf p2 C2),
                        <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)
            (fun p1 C1 st1 m1 v st2
                 (EVAL : MevalR p1 C1 st1 m1 v st2) =>
                 forall p2 C2 (VAL : v = Mod p2 C2),
                        <m| p1 C1 st1 m1 ~> p2 C2 st2 m_empty |m>));
  intros;
  try rewrite VAL in *; try destruct arg; inversion VAL;
  eauto using EreachE, EreachM, MreachE, MreachM, MevalR, EevalR.
  - apply mrm_trans with (p2 := t :: p) (C2 := C [|c_lete x c_hole|])
                         (st2 := ST ((t :: p) !-> v_e; e_mem) m_mem (update_t t)) (m2 := m);
    destruct v_e; eauto using MreachM.
  - apply mrm_trans with (p2 := t :: p) (C2 := C [|c_letm M c_hole|])
                         (st2 := ST e_mem ((t :: p) !-> v_m1; m_mem) (update_t t)) (m2 := m2);
    destruct v_m1; eauto using MreachM.
Qed.