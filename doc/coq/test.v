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

(* Reachability relation, sensible version *)
Inductive _EreachE (p : path) (C : ctx) (st : state)
    : Reach expr_tm expr_tm :=
  | _ere_refl e
    : _EreachE p C st e 
               p C st e
  | _ere_var x i p_x e_mem m_mem t v pf p_v C_v
            (STATE : ST e_mem m_mem t = st)
            (INDEX : Some i = index_expr C x)
            (POP : Some p_x = pop p i)
            (ACCESS : Some (Val v pf p_v C_v) = e_mem p_x)
    : _EreachE p C st (e_var x) 
               p_v C_v st v
  | _ere_app_left e1 e2 p' C' st' e'
                 (REACHl : _EreachE p C st e1
                                    p' C' st' e')
    : _EreachE p C st (e_app e1 e2) 
               p' C' st' e'
  | _ere_app_right e1 e2 st1 v p' C' st' e'
                  (FN : EevalR p C st e1 v st1)
                  (REACHr : _EreachE p C st1 e2
                                     p' C' st' e')
    : _EreachE p C st (e_app e1 e2)
               p' C' st' e'
  | _ere_app_body e1 e2 x e p_lam C_lam st_lam
                 arg e_mem m_mem t
                 p' C' st' e'
                 (FN : EevalR p C st e1 
                             (Val (e_lam x e) (v_fn x e) p_lam C_lam) st_lam)
                 (ARG : EevalR p C st_lam e2
                               arg (ST e_mem m_mem t))
                 (REACHb : _EreachE (t :: p_lam) (C_lam[|c_lam x c_hole|]) 
                                    (ST ((t :: p_lam) !-> arg ; e_mem) m_mem (update_t t)) e
                                     p' C' st' e')
    : _EreachE p C st (e_app e1 e2)
               p' C' st' e'
  | _ere_link_m m e p' C' st' e'
               (REACHm : _MreachE p C st m
                                  p' C' st' e')
    : _EreachE p C st (e_link m e)
               p' C' st' e'
  | _ere_link_e m e p_m C_m st_m p' C' st' e'
               (MOD : MevalR p C st m (Mod p_m C_m) st_m)
               (REACHe : _EreachE p_m C_m st_m e
                                  p' C' st' e')
    : _EreachE p C st (e_link m e)
               p' C' st' e'

with _MreachE (p : path) (C : ctx) (st : state)
    : Reach mod_tm expr_tm :=
  | _mre_lete_e x e m p' C' st' e'
               (REACHe : _EreachE p C st e
                                  p' C' st' e')
    : _MreachE p C st (m_lete x e m)
               p' C' st' e'
  | _mre_lete_m x e m v e_mem m_mem t
             p' C' st' e'
             (EVALx : EevalR p C st e v (ST e_mem m_mem t))
             (REACHm : _MreachE (t :: p) (C[|c_lete x c_hole|])
                                (ST ((t :: p) !-> v ; e_mem) m_mem (update_t t)) m
                                 p' C' st' e')
    : _MreachE p C st (m_lete x e m)
               p' C' st' e'
  | _mre_letm_m1 M m1 m2 p' C' st' e'
               (REACHm : _MreachE p C st m1
                                  p' C' st' e')
    : _MreachE p C st (m_letm M m1 m2)
              p' C' st' e'
  | _mre_letm_m2 M m1 m2 v e_mem m_mem t
             p' C' st' e'
             (EVALM : MevalR p C st m1 v (ST e_mem m_mem t))
             (REACHm : _MreachE (t :: p) (C[|c_letm M c_hole|]) 
                                (ST e_mem ((t :: p) !-> v ; m_mem) (update_t t)) m2
                                 p' C' st' e')
    : _MreachE p C st (m_letm M m1 m2)
               p' C' st' e'.

Scheme __EreachE_ind_mut := Induction for _EreachE Sort Prop
with __MreachE_ind_mut := Induction for _MreachE Sort Prop.

Inductive _MreachM (p : path) (C : ctx) (st : state)
    : Reach mod_tm mod_tm :=
  | _mrm_refl m
    : _MreachM p C st m
               p C st m
  | _mrm_var M i p_M e_mem m_mem t p_v C_v
            (STATE : ST e_mem m_mem t = st)
            (INDEX : Some i = index_mod C M)
            (POP : Some p_M = pop p i)
            (ACCESS : Some (Mod p_v C_v) = m_mem p_M)
    : _MreachM p C st (m_var M)
               p_v C_v st m_empty
  | _mrm_lete_e x e m p' C' st' m'
               (REACHe : _EreachM p C st e
                                  p' C' st' m')
    : _MreachM p C st (m_lete x e m)
               p' C' st' m'
  | _mrm_lete_m x e m v e_mem m_mem t
             p' C' st' m'
             (EVALx : EevalR p C st e v (ST e_mem m_mem t))
             (REACHm : _MreachM (t :: p) (C[|c_lete x c_hole|]) 
                                (ST ((t :: p) !-> v ; e_mem) m_mem (update_t t)) m
                                 p' C' st' m')
    : _MreachM p C st (m_lete x e m)
               p' C' st' m'
  | _mrm_letm_m1 M m1 m2 p' C' st' m'
               (REACHm : _MreachM p C st m1
                                  p' C' st' m')
    : _MreachM p C st (m_letm M m1 m2)
               p' C' st' m'
  | _mrm_letm_m2 M m1 m2 v e_mem m_mem t
             p' C' st' m'
             (EVALM : MevalR p C st m1 v (ST e_mem m_mem t))
             (REACHm : _MreachM (t :: p) (C[|c_letm M c_hole|]) 
                                (ST e_mem ((t :: p) !-> v ; m_mem) (update_t t)) m2
                                 p' C' st' m')
    : _MreachM p C st (m_letm M m1 m2)
               p' C' st' m'

with _EreachM (p : path) (C : ctx) (st : state)
    : Reach expr_tm mod_tm :=
  | _erm_app_left e1 e2 p' C' st' m'
                 (REACHl : _EreachM p C st e1
                                    p' C' st' m')
    : _EreachM p C st (e_app e1 e2) 
               p' C' st' m'
  | _erm_app_right e1 e2 v1 st1 p' C' st' m'
                  (FN : EevalR p C st e1 v1 st1)
                  (REACHr : _EreachM p C st1 e2
                                     p' C' st' m')
    : _EreachM p C st (e_app e1 e2)
               p' C' st' m'
  | _erm_app_body e1 e2 x e p_lam C_lam st_lam
                 arg e_mem m_mem t
                 p' C' st' m'
                 (FN : EevalR p C st e1 
                              (Val (e_lam x e) (v_fn x e) p_lam C_lam) st_lam)
                 (ARG : EevalR p C st_lam e2 arg (ST e_mem m_mem t))
                 (REACHb : _EreachM (t :: p_lam) (C_lam[|c_lam x c_hole|]) 
                                    (ST ((t :: p_lam) !-> arg ; e_mem) m_mem (update_t t)) e
                                     p' C' st' m')
    : _EreachM p C st (e_app e1 e2)
               p' C' st' m'
  | _erm_link_m m e p' C' st' m'
               (REACHm : _MreachM p C st m
                                  p' C' st' m')
    : _EreachM p C st (e_link m e)
               p' C' st' m'
  | _erm_link_e m e p_m C_m st_m p' C' st' m'
               (MOD : MevalR p C st m (Mod p_m C_m) st_m)
               (REACHe : _EreachM p_m C_m st_m e
                                  p' C' st' m')
    : _EreachM p C st (e_link m e)
               p' C' st' m'
.

Scheme __EreachM_ind_mut := Induction for _EreachM Sort Prop
with __MreachM_ind_mut := Induction for _MreachM Sort Prop.

(* for proofs *)
Inductive EreachE (p : path) (C : ctx) (st : state)
    : Reach expr_tm expr_tm :=
  | ere_refl e
    : EreachE p C st e 
              p C st e
  | ere_var x i p_x e_mem m_mem t v pf p_v C_v
            (STATE : ST e_mem m_mem t = st)
            (INDEX : Some i = index_expr C x)
            (POP : Some p_x = pop p i)
            (ACCESS : Some (Val v pf p_v C_v) = e_mem p_x)
    : EreachE p C st (e_var x) 
              p_v C_v st v
  | ere_app_left e1 e2 p' C' st' e'
                 (REACHl : EreachE p C st e1
                                   p' C' st' e')
    : EreachE p C st (e_app e1 e2) 
              p' C' st' e'
  | ere_app_right e1 e2 st1 v pf p1 C1 p' C' st' e'
                  (FN : EevalR p C st e1 (Val v pf p1 C1) st1)
                  (FNr : EreachE p C st e1 p1 C1 st1 v)
                  (REACHr : EreachE p C st1 e2
                                    p' C' st' e')
    : EreachE p C st (e_app e1 e2)
              p' C' st' e'
  | ere_app_body e1 e2 x e p_lam C_lam st_lam
                 arg pf p_arg C_arg e_mem m_mem t
                 p' C' st' e'
                 (FN : EevalR p C st e1 
                             (Val (e_lam x e) (v_fn x e) p_lam C_lam) st_lam)
                 (FNr : EreachE p C st e1 p_lam C_lam st_lam (e_lam x e))
                 (ARG : EevalR p C st_lam e2
                               (Val arg pf p_arg C_arg) (ST e_mem m_mem t))
                 (ARGr : EreachE p C st_lam e2 p_arg C_arg (ST e_mem m_mem t) arg)
                 (REACHb : EreachE (t :: p_lam) (C_lam[|c_lam x c_hole|]) 
                                   (ST ((t :: p_lam) !-> (Val arg pf p_arg C_arg) ; e_mem) m_mem (update_t t)) e
                                    p' C' st' e')
    : EreachE p C st (e_app e1 e2)
              p' C' st' e'
  | ere_link_m m e p' C' st' e'
               (REACHm : MreachE p C st m
                                 p' C' st' e')
    : EreachE p C st (e_link m e)
              p' C' st' e'
  | ere_link_e m e p_m C_m st_m p' C' st' e'
               (MOD : MevalR p C st m (Mod p_m C_m) st_m)
               (MODr : MreachM p C st m p_m C_m st_m m_empty)
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
  | mre_lete_m x e m v pf p1 C1 e_mem m_mem t
             p' C' st' e'
             (EVALx : EevalR p C st e (Val v pf p1 C1) (ST e_mem m_mem t))
             (EVALxr : EreachE p C st e p1 C1 (ST e_mem m_mem t) v)
             (REACHm : MreachE (t :: p) (C[|c_lete x c_hole|])
                               (ST ((t :: p) !-> (Val v pf p1 C1) ; e_mem) m_mem (update_t t)) m
                                p' C' st' e')
    : MreachE p C st (m_lete x e m)
              p' C' st' e'
  | mre_letm_m1 M m1 m2 p' C' st' e'
               (REACHm : MreachE p C st m1
                                 p' C' st' e')
    : MreachE p C st (m_letm M m1 m2)
              p' C' st' e'
  | mre_letm_m2 M m1 m2 p_m C_m e_mem m_mem t
             p' C' st' e'
             (EVALM : MevalR p C st m1 (Mod p_m C_m) (ST e_mem m_mem t))
             (EVALMr : MreachM p C st m1 p_m C_m (ST e_mem m_mem t) m_empty)
             (REACHm : MreachE (t :: p) (C[|c_letm M c_hole|]) 
                               (ST e_mem ((t :: p) !-> (Mod p_m C_m) ; m_mem) (update_t t)) m2
                                p' C' st' e')
    : MreachE p C st (m_letm M m1 m2)
              p' C' st' e'

with MreachM (p : path) (C : ctx) (st : state)
    : Reach mod_tm mod_tm :=
  | mrm_refl m
    : MreachM p C st m
              p C st m
  | mrm_var M i p_M e_mem m_mem t p_v C_v
            (STATE : ST e_mem m_mem t = st)
            (INDEX : Some i = index_mod C M)
            (POP : Some p_M = pop p i)
            (ACCESS : Some (Mod p_v C_v) = m_mem p_M)
    : MreachM p C st (m_var M)
              p_v C_v st m_empty
  | mrm_lete_e x e m p' C' st' m'
               (REACHe : EreachM p C st e
                                 p' C' st' m')
    : MreachM p C st (m_lete x e m)
              p' C' st' m'
  | mrm_lete_m x e m v pf p1 C1 e_mem m_mem t
             p' C' st' m'
             (EVALx : EevalR p C st e (Val v pf p1 C1) (ST e_mem m_mem t))
             (EVALxr : EreachE p C st e p1 C1 (ST e_mem m_mem t) v)
             (REACHm : MreachM (t :: p) (C[|c_lete x c_hole|])
                               (ST ((t :: p) !-> (Val v pf p1 C1) ; e_mem) m_mem (update_t t)) m
                                p' C' st' m')
    : MreachM p C st (m_lete x e m)
              p' C' st' m'
  | mrm_letm_m1 M m1 m2 p' C' st' m'
               (REACHm : MreachM p C st m1
                                 p' C' st' m')
    : MreachM p C st (m_letm M m1 m2)
              p' C' st' m'
  | mrm_letm_m2 M m1 m2 p_m C_m e_mem m_mem t
             p' C' st' m'
             (EVALM : MevalR p C st m1 (Mod p_m C_m) (ST e_mem m_mem t))
             (EVALMr : MreachM p C st m1 p_m C_m (ST e_mem m_mem t) m_empty)
             (REACHm : MreachM (t :: p) (C[|c_letm M c_hole|]) 
                               (ST e_mem ((t :: p) !-> (Mod p_m C_m) ; m_mem) (update_t t)) m2
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
  | erm_app_right e1 e2 st1 v pf p1 C1 p' C' st' m'
                  (FN : EevalR p C st e1 (Val v pf p1 C1) st1)
                  (FNr : EreachE p C st e1 p1 C1 st1 v)
                  (REACHr : EreachM p C st1 e2
                                    p' C' st' m')
    : EreachM p C st (e_app e1 e2)
              p' C' st' m'
  | erm_app_body e1 e2 x e p_lam C_lam st_lam
                 arg pf p_arg C_arg e_mem m_mem t
                 p' C' st' m'
                 (FN : EevalR p C st e1 
                             (Val (e_lam x e) (v_fn x e) p_lam C_lam) st_lam)
                 (FNr : EreachE p C st e1 p_lam C_lam st_lam (e_lam x e))
                 (ARG : EevalR p C st_lam e2
                               (Val arg pf p_arg C_arg) (ST e_mem m_mem t))
                 (ARGr : EreachE p C st_lam e2 p_arg C_arg (ST e_mem m_mem t) arg)
                 (REACHb : EreachM (t :: p_lam) (C_lam[|c_lam x c_hole|]) 
                                   (ST ((t :: p_lam) !-> (Val arg pf p_arg C_arg) ; e_mem) m_mem (update_t t)) e
                                    p' C' st' m')
    : EreachM p C st (e_app e1 e2)
              p' C' st' m'
  | erm_link_m m e p' C' st' m'
               (REACHm : MreachM p C st m
                                 p' C' st' m')
    : EreachM p C st (e_link m e)
              p' C' st' m'
  | erm_link_e m e p_m C_m st_m p' C' st' m'
               (MOD : MevalR p C st m (Mod p_m C_m) st_m)
               (MODr : MreachM p C st m p_m C_m st_m m_empty)
               (REACHe : EreachM p_m C_m st_m e
                                 p' C' st' m')
    : EreachM p C st (e_link m e)
              p' C' st' m'
.

Scheme _EreachE_ind_mut := Induction for EreachE Sort Prop
with _EreachM_ind_mut := Induction for EreachM Sort Prop
with _MreachE_ind_mut := Induction for MreachE Sort Prop
with _MreachM_ind_mut := Induction for MreachM Sort Prop.

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
  apply (_EreachE_ind_mut
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
  apply (_MreachM_ind_mut
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
  apply (_EreachM_ind_mut
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
  apply (_MreachE_ind_mut
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

(* equivalence between reachability relations *)
Lemma Eeval_then_reach :
    forall pi Ci sti ei v stv
           (EVAL : EevalR pi Ci sti ei v stv)
           ev pf pv Cv e_mem m_mem t
           (VAL : v = Val ev pf pv Cv)
           (STATE : stv = ST e_mem m_mem t),
          <e| pi Ci sti ei ~> pv Cv stv ev |e>.
Proof.
  apply (EevalR_ind_mut
    (fun pi Ci sti ei v stv
        (EVAL : EevalR pi Ci sti ei v stv) =>
        forall ev pf pv Cv e_mem m_mem t
              (VAL : v = Val ev pf pv Cv)
              (STATE : stv = ST e_mem m_mem t),
        <e| pi Ci sti ei ~> pv Cv stv ev |e>)
    (fun pi Ci sti mi v stv
        (EVAL : MevalR pi Ci sti mi v stv) =>
        forall pv Cv e_mem m_mem t
              (VAL : v = Mod pv Cv)
              (STATE : stv = ST e_mem m_mem t),
        <m| pi Ci sti mi ~> pv Cv stv m_empty |m>));
  intros; try inversion STATE0; try inversion STATE;
          try inversion VAL; try destruct st_lam;
          try destruct st_m; try destruct v_e;
          try destruct v_m1; try destruct arg; subst; 
          eauto using EreachE, EreachM, MreachE, MreachM.
  - inversion STATE; subst. destruct st; subst.
    eapply mrm_lete_m. eapply EVALe.
    eapply H. eauto. eauto. eapply H0. eauto. eauto.
Qed.

Lemma Meval_then_reach :
    forall pi Ci sti mi v stv
           (EVAL : MevalR pi Ci sti mi v stv)
           pv Cv e_mem m_mem t
           (VAL : v = Mod pv Cv)
           (STATE : stv = ST e_mem m_mem t),
           <m| pi Ci sti mi ~> pv Cv stv m_empty |m>.
Proof.
  apply (MevalR_ind_mut
    (fun pi Ci sti ei v stv
        (EVAL : EevalR pi Ci sti ei v stv) =>
        forall ev pf pv Cv e_mem m_mem t
              (VAL : v = Val ev pf pv Cv)
              (STATE : stv = ST e_mem m_mem t),
        <e| pi Ci sti ei ~> pv Cv stv ev |e>)
    (fun pi Ci sti mi v stv
        (EVAL : MevalR pi Ci sti mi v stv) =>
        forall pv Cv e_mem m_mem t
              (VAL : v = Mod pv Cv)
              (STATE : stv = ST e_mem m_mem t),
        <m| pi Ci sti mi ~> pv Cv stv m_empty |m>));
  intros; try inversion STATE0; try inversion STATE;
          try inversion VAL; try destruct st_lam;
          try destruct st_m; try destruct v_e;
          try destruct v_m1; try destruct arg; subst; 
          eauto using EreachE, EreachM, MreachE, MreachM.
  - inversion STATE; subst. destruct st; subst.
    eapply mrm_lete_m. eapply EVALe.
    eapply H. eauto. eauto. eapply H0. eauto. eauto.
Qed.

Lemma EreachE_equiv_left :
    forall p1 C1 st1 e1 p2 C2 st2 e2,
          <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e> ->
          _EreachE p1 C1 st1 e1 p2 C2 st2 e2.
Proof.
  apply (_EreachE_ind_mut 
    (fun p1 C1 st1 e1 p2 C2 st2 e2
        (REACH : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>) =>
        _EreachE p1 C1 st1 e1 p2 C2 st2 e2)
    (fun p1 C1 st1 e1 p2 C2 st2 m2
        (REACH : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>) =>
        _EreachM p1 C1 st1 e1 p2 C2 st2 m2)
    (fun p1 C1 st1 m1 p2 C2 st2 e2
        (REACH : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>) =>
        _MreachE p1 C1 st1 m1 p2 C2 st2 e2)
    (fun p1 C1 st1 m1 p2 C2 st2 m2
        (REACH : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>) =>
        _MreachM p1 C1 st1 m1 p2 C2 st2 m2));
  intros; eauto using EreachE, EreachM, MreachE, MreachM, _EreachE, _MreachE, _EreachM, _MreachM.
Qed.

Lemma EreachE_equiv_right :
    forall p1 C1 st1 e1 p2 C2 st2 e2,
          _EreachE p1 C1 st1 e1 p2 C2 st2 e2 ->
          <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>.
Proof.
  apply (__EreachE_ind_mut 
    (fun p1 C1 st1 e1 p2 C2 st2 e2
        (REACH : _EreachE p1 C1 st1 e1 p2 C2 st2 e2) =>
        <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>)
    (fun p1 C1 st1 m1 p2 C2 st2 e2
        (REACH : _MreachE p1 C1 st1 m1 p2 C2 st2 e2) =>
        <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>));
  intros; try destruct v; try destruct st; try destruct st1; try destruct st_lam;
  try destruct arg; try destruct st_m; try destruct st';
  eauto using EreachE, EreachM, MreachE, MreachM, _EreachE, _MreachE, _EreachM, _MreachM.
  - eapply Eeval_then_reach in FN as FNr; eauto using EreachE.
  - eapply Eeval_then_reach in FN as FNr; eauto using EreachE.
    eapply Eeval_then_reach in ARG as ARGr; eauto using EreachE.
  - eapply Meval_then_reach in MOD as MODr; eauto using EreachE.
  - eapply Eeval_then_reach in EVALx as EVALxr; eauto using MreachE.
  - eapply Meval_then_reach in EVALM as EVALMr; eauto using MreachE.
Qed.

Theorem EreachE_equiv : 
  forall p1 C1 st1 e1 p2 C2 st2 e2,
          _EreachE p1 C1 st1 e1 p2 C2 st2 e2 <->
          <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>.
Proof. 
  intros; split; try apply EreachE_equiv_left; try apply EreachE_equiv_right. 
Qed.

(* Induction principle: preserves a predicate on p, C, st *)
Lemma EreachE_ind_mut : 
  forall (P : forall (p : path) (C : ctx) (st : state), Prop),
    (forall p C st, (P p C st) -> 
        (match st with
        | ST e_mem m_mem _ =>
            forall addr,
            match e_mem addr with
              | None => True
              | Some (Val _ _ p' C') => P p' C' st
            end /\
            match m_mem addr with
              | None => True
              | Some (Mod p' C') => P p' C' st
            end
        end)) ->
    (forall p C st p' C' st'
            (INIT : P p C st)
            (REACH : P p' C' st'),
            P p C st') ->
    (forall p C st 
            x p_lam C_lam st_lam 
            v pf p_arg C_arg e_mem m_mem t
            (INIT : P p C st)
            (FN: P p_lam C_lam st_lam)
            (ARG : P p_arg C_arg (ST e_mem m_mem t)),
            P (t :: p_lam) (C_lam[|c_lam x c_hole|])
              (ST ((t :: p_lam) !-> (Val v pf p_arg C_arg); e_mem) m_mem (update_t t))) ->
    (forall p C st x
            v (pf : value v) p_x C_x e_mem m_mem t
            (INIT : P p C st)
            (EVx : P p_x C_x (ST e_mem m_mem t)),
            P (t :: p) (C[|c_lete x c_hole|])
              (ST ((t :: p) !-> (Val v pf p_x C_x); e_mem) m_mem (update_t t))) ->
    (forall p C st M
            p_M C_M e_mem m_mem t
            (INIT : P p C st)
            (EVM : P p_M C_M (ST e_mem m_mem t)),
            P (t :: p) (C[|c_letm M c_hole|])
              (ST e_mem ((t :: p) !-> (Mod p_M C_M); m_mem) (update_t t))) ->
    (forall p C st e p' C' st' e'
            (INIT : P p C st)
            (REACH : <e| p C st e ~> p' C' st' e' |e>),
            P p' C' st').
Proof. 
(* intros just before our goal, then fix 10, on REACH, 
   with mutual induction on EreachM, MreachE, MreachM *)
  intros P condP transP LAM LETe LETm.
  fix IHere 10 with 
    (IHerm p C st e p' C' st' m'
          (INIT : P p C st)
          (REACH : <e| p C st e ~> p' C' st' m' |m>)
          { struct REACH }
          : P p' C' st')
    (IHmre p C st m p' C' st' e'
          (INIT : P p C st)
          (REACH : <m| p C st m ~> p' C' st' e' |e>)
          { struct REACH }
          : P p' C' st')
    (IHmrm p C st m p' C' st' m'
          (INIT : P p C st)
          (REACH : <m| p C st m ~> p' C' st' m' |m>)
          { struct REACH }
          : P p' C' st').
  - intros. destruct REACH.
    + exact INIT.
    + specialize (condP p C st INIT).
      rewrite <- STATE in *. destruct (condP p_x) as [valcase modcase].
      rewrite <- ACCESS in *. exact valcase.
    + apply (IHere p C st e1 p' C' st' e'). exact INIT. exact REACH.
    + apply (IHere p C st1 e2 p' C' st' e').
      assert (P p1 C1 st1) as trans.
      apply (IHere p C st e1 p1 C1 st1 v).
      exact INIT. exact REACH1. eapply transP.
      exact INIT. exact trans. exact REACH2.
    + apply (IHere (t :: p_lam) (C_lam [|c_lam x c_hole|])
            (ST (t :: p_lam !-> (Val arg pf p_arg C_arg); e_mem) m_mem (update_t t)) e
            p' C' st' e').
      assert (P p_lam C_lam st_lam) as trans.
      apply (IHere p C st e1 p_lam C_lam st_lam (e_lam x e)).
      exact INIT. exact REACH1.
      apply LAM with (p := p) (C := C) (st := st) (st_lam := st_lam).
      exact INIT. exact trans. apply (IHere p C st_lam e2 p_arg C_arg (ST e_mem m_mem t) arg).
      eapply transP. eapply INIT. eapply trans. apply REACH2. exact REACH3.
    + apply (IHmre p C st m p' C' st' e'). exact INIT. exact REACHm.
    + apply (IHere p_m C_m st_m e p' C' st' e').
      apply (IHmrm p C st m p_m C_m st_m m_empty).
      exact INIT. exact MODr. exact REACH.
  - intros. destruct REACH.
    + apply (IHerm p C st e1 p' C' st' m'). exact INIT. exact REACH.
    + apply (IHerm p C st1 e2 p' C' st' m').
      assert (P p1 C1 st1) as trans.
      apply (IHere p C st e1 p1 C1 st1 v).
      exact INIT. exact FNr. eapply transP.
      exact INIT. exact trans. exact REACH.
    + apply (IHerm (t :: p_lam) (C_lam [|c_lam x c_hole|])
            (ST (t :: p_lam !-> Val arg pf p_arg C_arg; e_mem) m_mem (update_t t)) e
            p' C' st' m').
      assert (P p_lam C_lam st_lam) as trans.
      apply (IHere p C st e1 p_lam C_lam st_lam (e_lam x e)).
      exact INIT. exact FNr.
      apply LAM with (p := p) (C := C) (st := st) (st_lam := st_lam).
      exact INIT. exact trans. apply (IHere p C st_lam e2 p_arg C_arg (ST e_mem m_mem t) arg).
      eapply transP. eapply INIT. eapply trans. apply ARGr. exact REACH.
    + apply (IHmrm p C st m p' C' st' m'). exact INIT. exact REACHm.
    + apply (IHerm p_m C_m st_m e p' C' st' m').
      apply (IHmrm p C st m p_m C_m st_m m_empty).
      exact INIT. exact MODr. exact REACH.
  - intros. destruct REACH.
    + apply (IHere p C st e p' C' st' e'). exact INIT. exact REACHe.
    + apply (IHmre (t :: p) (C [|c_lete x c_hole|])
        (ST (t :: p !-> Val v pf p1 C1; e_mem) m_mem (update_t t)) m
        p' C' st' e').
      eapply LETe. exact INIT. apply (IHere p C st e p1 C1 (ST e_mem m_mem t) v).
      exact INIT. exact EVALxr. exact REACH.
    + apply (IHmre p C st m1 p' C' st' e'). exact INIT. exact REACH.
    + apply (IHmre (t :: p) (C [|c_letm M c_hole|])
        (ST e_mem (t :: p !-> Mod p_m C_m; m_mem) (update_t t)) m2 p'
        C' st' e' ).
      eapply LETm. exact INIT. apply (IHmrm p C st m1 p_m C_m (ST e_mem m_mem t) m_empty).
      exact INIT. exact EVALMr. exact REACH.
  - intros. destruct REACH.
    + exact INIT.
    + specialize (condP p C st INIT).
      rewrite <- STATE in *. destruct (condP p_M) as [valcase modcase].
      rewrite <- ACCESS in *. exact modcase.
    + apply (IHerm p C st e p' C' st' m'). exact INIT. exact REACHe.
    + apply (IHmrm (t :: p) (C [|c_lete x c_hole|])
        (ST (t :: p !-> Val v pf p1 C1; e_mem) m_mem (update_t t)) m
        p' C' st' m').
      eapply LETe. exact INIT. apply (IHere p C st e p1 C1 (ST e_mem m_mem t) v).
      exact INIT. exact EVALxr. exact REACH.
    + apply (IHmrm p C st m1 p' C' st' m'). exact INIT. exact REACH.
    + apply (IHmrm (t :: p) (C [|c_letm M c_hole|])
        (ST e_mem (t :: p !-> Mod p_m C_m; m_mem) (update_t t)) m2 p'
        C' st' m' ).
      eapply LETm. exact INIT. apply (IHmrm p C st m1 p_m C_m (ST e_mem m_mem t) m_empty).
      exact INIT. exact REACH1. exact REACH2.
Qed.

Definition st_len m n p C st :=
    match st with
    | ST e_mem m_mem t =>
        (forall (addr : path) v pf p' C',
                e_mem addr = Some (Val v pf p' C') ->
                len_p p' + m = level C' + n) /\
        (forall (addr : path) p' C',
                m_mem addr = Some (Mod p' C') ->
                len_p p' + m = level C' + n) /\
        len_p p + m = level C + n
    end.

Lemma ere_p_is_level : 
    forall m n
           pi Ci sti ei
           pr Cr str er
          (INIT : st_len m n pi Ci sti)
          (REACH : <e| pi Ci sti ei ~> pr Cr str er |e>),
          st_len m n pr Cr str.
Proof. 
  intros m n.
  apply EreachE_ind_mut with (P := st_len m n).
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