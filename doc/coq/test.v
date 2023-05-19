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

Scheme expr_ind_mut := Induction for expr_tm Sort Prop
with mod_ind_mut := Induction for mod_tm Sort Prop.

Inductive ctx :=
  | c_hole
  | c_lam (x: expr_id) (C : ctx)
  | c_app_left (C : ctx) (e : expr_tm)
  | c_app_right (e : expr_tm) (C : ctx)
  | c_lete (x : expr_id) (e : expr_tm) (C : ctx)
  | c_letm (M : mod_id) (m : mod_tm) (C : ctx)
.

Fixpoint plugin_c Cout Cin :=
  match Cout with
  | c_hole => Cin
  | c_lam x C' => c_lam x (plugin_c C' Cin)
  | c_app_left C' e => c_app_left (plugin_c C' Cin) e
  | c_app_right e C' => c_app_right e (plugin_c C' Cin)
  | c_lete x e C' => c_lete x e (plugin_c C' Cin)
  | c_letm M m C' => c_letm M m (plugin_c C' Cin)
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
  | c_app_left C' _
  | c_app_right _ C' => level C'
  | c_lam _ C'
  | c_lete _ _ C' 
  | c_letm _ _ C' => S (level C')
  end.

Fixpoint index_expr_aux (C : ctx) (x : expr_id) (o : option nat) :=
  match C with
  | c_hole => o
  | c_app_left C' _
  | c_app_right _ C' => index_expr_aux C' x o
  | c_lam x' C' 
  | c_lete x' _ C' => 
    if eq_eid x x' then (
      index_expr_aux C' x (Some 0)
    ) else (
      match o with
      | Some i => index_expr_aux C' x (Some (S i))
      | None => index_expr_aux C' x None
      end
    )
  | c_letm M _ C' =>
    match o with
    | Some i => index_expr_aux C' x (Some (S i))
    | None => index_expr_aux C' x None
    end
  end.

Definition index_expr C x := index_expr_aux C x None.

Fixpoint index_mod_aux (C : ctx) (M : mod_id) (o : option nat) :=
  match C with
  | c_hole => o
  | c_app_left C' _
  | c_app_right _ C' => index_mod_aux C' M o
  | c_lam _ C'
  | c_lete _ _ C' =>
    match o with
    | Some i => index_mod_aux C' M (Some (S i))
    | None => index_mod_aux C' M None
    end
  | c_letm M' _ C' =>
    if eq_mid M M' then (
      index_mod_aux C' M (Some 0)
    ) else (
      match o with
      | Some i => index_mod_aux C' M (Some (S i))
      | None => index_mod_aux C' M None
      end
    )
  end.

Definition index_mod C M := index_mod_aux C M None.

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

Inductive expr_value :=
  | Closure (x : expr_id) (e : expr_tm) (p : path) (C : ctx)
.

Inductive state :=
  | ST (e_mem : path -> option expr_value)
       (m_mem : path -> option mod_value)
       (t : nat)
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
    : EevalR p C st (e_lam x e) (Closure x e p C) st
  | Eeval_app e1 e2 
              x e_lam p_lam C_lam st_lam
              arg e_mem m_mem t
              v st_v
              (FN : EevalR p (C [|c_app_left c_hole e2|]) st
                           e1 (Closure x e_lam p_lam C_lam) st_lam)
              (ARG : EevalR p (C [|c_app_right e1 c_hole|]) st_lam
                            e2 arg (ST e_mem m_mem t))
              (BODY : EevalR (t :: p_lam) (C_lam [|c_lam x c_hole|])
                             (ST ((t :: p_lam) !-> arg ; e_mem) m_mem (update_t t))
                              e_lam v st_v)
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
               (EVALm : MevalR (t :: p) (C [|c_lete x e c_hole|]) 
                        (ST ((t :: p) !-> v_e ; e_mem) m_mem (update_t t))
                        m v_m st_m)
    : MevalR p C st (m_lete x e m) v_m st_m
  | Meval_letm M m1 v_m1 e_mem m_mem t
               m2 v_m2 st_m2
               (EVALm1 : MevalR p C st m1 v_m1 (ST e_mem m_mem t))
               (EVALm2 : MevalR (t :: p) (C [|c_letm M m1 c_hole|])
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
  | ere_app_left e1 e2 p' C' st' e'
                 (REACHl : EreachE p (C [|c_app_left c_hole e2|]) st e1
                                   p' C' st' e')
    : EreachE p C st (e_app e1 e2) 
              p' C' st' e'
  | ere_app_right e1 e2 v1 st1 p' C' st' e'
                  (FN : EevalR p (C [|c_app_left c_hole e2|]) st e1 v1 st1)
                  (REACHr : EreachE p (C[|c_app_right e1 c_hole|]) st1 e2
                                    p' C' st' e')
    : EreachE p C st (e_app e1 e2)
              p' C' st' e'
  | ere_app_body e1 e2 x e_lam p_lam C_lam st_lam
                 arg e_mem m_mem t_a
                 p' C' st' e'
                 (FN : EevalR p (C [|c_app_left c_hole e2|]) st e1 
                             (Closure x e_lam p_lam C_lam) st_lam)
                 (ARG : EevalR p (C [|c_app_right e1 c_hole|]) st_lam e2
                               arg (ST e_mem m_mem t_a))
                 (REACHb : EreachE (t_a :: p_lam) (C_lam[|c_lam x c_hole|]) 
                                   (ST ((t_a :: p_lam) !-> arg ; e_mem) m_mem (update_t t_a)) e_lam
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
  | mre_lete_m x e m v e_mem m_mem t_e
             p' C' st' e'
             (EVALx : EevalR p C st e v (ST e_mem m_mem t_e))
             (REACHm : MreachE (t_e :: p) (C[|c_lete x e c_hole|]) (ST ((t_e :: p) !-> v ; e_mem) m_mem (update_t t_e)) m
                                p' C' st' e')
    : MreachE p C st (m_lete x e m)
              p' C' st' e'
  | mre_letm_m1 M m1 m2 p' C' st' e'
               (REACHm : MreachE p C st m1
                                 p' C' st' e')
    : MreachE p C st (m_letm M m1 m2)
              p' C' st' e'
  | mre_letm_m2 M m1 m2 v e_mem m_mem t_m
             p' C' st' e'
             (EVALM : MevalR p C st m1 v (ST e_mem m_mem t_m))
             (REACHm : MreachE (t_m :: p) (C[|c_letm M m1 c_hole|]) (ST e_mem ((t_m :: p) !-> v ; m_mem) (update_t t_m)) m2
                                p' C' st' e')
    : MreachE p C st (m_letm M m1 m2)
              p' C' st' e'
.

Scheme EreachE_ind_mut := Induction for EreachE Sort Prop
with MreachE_ind_mut := Induction for MreachE Sort Prop.

Inductive MreachM (p : path) (C : ctx) (st : state)
    : Reach mod_tm mod_tm :=
  | mrm_refl m
    : MreachM p C st m
              p C st m
  | mrm_lete_e x e m p' C' st' m'
               (REACHe : EreachM p C st e
                                 p' C' st' m')
    : MreachM p C st (m_lete x e m)
              p' C' st' m'
  | mrm_lete_m x e m v e_mem m_mem t_e
             p' C' st' m'
             (EVALx : EevalR p C st e v (ST e_mem m_mem t_e))
             (REACHm : MreachM (t_e :: p) (C[|c_lete x e c_hole|]) (ST ((t_e :: p) !-> v ; e_mem) m_mem (update_t t_e)) m
                                p' C' st' m')
    : MreachM p C st (m_lete x e m)
              p' C' st' m'
  | mrm_letm_m1 M m1 m2 p' C' st' m'
               (REACHm : MreachM p C st m1
                                 p' C' st' m')
    : MreachM p C st (m_letm M m1 m2)
              p' C' st' m'
  | mrm_letm_m2 M m1 m2 v e_mem m_mem t_m
             p' C' st' m'
             (EVALM : MevalR p C st m1 v (ST e_mem m_mem t_m))
             (REACHm : MreachM (t_m :: p) (C[|c_letm M m1 c_hole|]) (ST e_mem ((t_m :: p) !-> v ; m_mem) (update_t t_m)) m2
                                p' C' st' m')
    : MreachM p C st (m_letm M m1 m2)
              p' C' st' m'

with EreachM (p : path) (C : ctx) (st : state)
    : Reach expr_tm mod_tm :=
  | erm_app_left e1 e2 p' C' st' m'
                 (REACHl : EreachM p (C [|c_app_left c_hole e2|]) st e1
                                   p' C' st' m')
    : EreachM p C st (e_app e1 e2) 
              p' C' st' m'
  | erm_app_right e1 e2 v1 st1 p' C' st' m'
                  (FN : EevalR p (C [|c_app_left c_hole e2|]) st e1 v1 st1)
                  (REACHr : EreachM p (C[|c_app_right e1 c_hole|]) st1 e2
                                    p' C' st' m')
    : EreachM p C st (e_app e1 e2)
              p' C' st' m'
  | erm_app_body e1 e2 x e_lam p_lam C_lam st_lam
                 arg e_mem m_mem t_a
                 p' C' st' m'
                 (FN : EevalR p (C [|c_app_left c_hole e2|]) st e1 
                             (Closure x e_lam p_lam C_lam) st_lam)
                 (ARG : EevalR p (C [|c_app_right e1 c_hole|]) st_lam e2
                               arg (ST e_mem m_mem t_a))
                 (REACHb : EreachM (t_a :: p_lam) (C_lam[|c_lam x c_hole|]) (ST ((t_a :: p_lam) !-> arg ; e_mem) m_mem (update_t t_a)) e_lam
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
               (REACHe : EreachM p_m C_m st_m e
                                 p' C' st' m')
    : EreachM p C st (e_link m e)
              p' C' st' m'
.

Scheme MreachM_ind_mut := Induction for MreachM Sort Prop
with EreachM_ind_mut := Induction for EreachM Sort Prop.

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
    (fun p1 C1 st1 m1
         p2 C2 st2 e2
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>) =>
         forall p3 C3 st3 e3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 e3 |e>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 e3 |e>));
   eauto using EreachE, MreachE.
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
    (fun p1 C1 st1 m1 
         p2 C2 st2 m2 
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>)=> 
         forall p3 C3 st3 m3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 m3 |m>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 e1
         p2 C2 st2 m2
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>) =>
         forall p3 C3 st3 m3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 m3 |m>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 m3 |m>));
   eauto using MreachM, EreachM.
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
    (fun p1 C1 st1 m1
         p2 C2 st2 m2
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 m2 |m>)=>
         forall p3 C3 st3 e3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 e3 |e>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 e3 |e>)
    (fun p1 C1 st1 e1
         p2 C2 st2 m2
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 m2 |m>)=>
         forall p3 C3 st3 e3 
                (REACH2 : <m| p2 C2 st2 m2 ~> p3 C3 st3 e3 |e>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 e3 |e>));
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
         (REACH1 : <e| p1 C1 st1 e1 ~> p2 C2 st2 e2 |e>) =>
         forall p3 C3 st3 m3 
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 m3 |m>),
                <e| p1 C1 st1 e1 ~> p3 C3 st3 m3 |m>)
    (fun p1 C1 st1 m1
         p2 C2 st2 e2
         (REACH1 : <m| p1 C1 st1 m1 ~> p2 C2 st2 e2 |e>)=>
         forall p3 C3 st3 m3
                (REACH2 : <e| p2 C2 st2 e2 ~> p3 C3 st3 m3 |m>),
                <m| p1 C1 st1 m1 ~> p3 C3 st3 m3 |m>));
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

(* Want to show this *)
Lemma ere_len_p_is_level : 
    forall e st p C st' e' (REACH : EreachE [] c_hole st e 
                                            p C st' e'),
            len_p p = level C.
Proof. Admitted.