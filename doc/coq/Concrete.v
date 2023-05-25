From MODULAR Require Export Syntax.

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

Inductive dy_ctx :=
  | dy_c_hole
  | dy_c_lam (x: expr_id) (tx : time) (C : dy_ctx)
  | dy_c_lete (x : expr_id) (tx : time) (C : dy_ctx)
  | dy_c_letm (M : mod_id) (CM : dy_ctx) (C : dy_ctx)
.

Fixpoint dy_plugin_c Cout Cin :=
  match Cout with
  | dy_c_hole => Cin
  | dy_c_lam x tx C' => dy_c_lam x tx (dy_plugin_c C' Cin)
  | dy_c_lete x tx C' => dy_c_lete x tx (dy_plugin_c C' Cin)
  | dy_c_letm M CM C' => dy_c_letm M CM (dy_plugin_c C' Cin)
  end.

Fixpoint dy_level (C : dy_ctx) : path :=
  match C with
  | dy_c_hole => []
  | dy_c_lam _ t C'
  | dy_c_lete _ t  C' => dy_level C' ++ [t]
  | dy_c_letm _ _  C' => dy_level C'
  end.

Fixpoint addr_x (C : dy_ctx) (x : expr_id) :=
  match C with
  | dy_c_hole => []
  | dy_c_lam x' tx' C'
  | dy_c_lete x' tx' C' =>
    match addr_x C' x with
    | [] => if eq_eid x x' then [tx'] else []
    | addr => addr ++ [tx']
    end
  | dy_c_letm _ _ C' => addr_x C' x
  end.

Fixpoint ctx_M (C : dy_ctx) (M : mod_id) :=
  match C with
  | dy_c_hole => None
  | dy_c_lam _ _ C'
  | dy_c_lete _ _ C' => ctx_M C' M
  | dy_c_letm M' CM' C' =>
    match ctx_M C' M with
    | Some CM => Some CM
    | None => if eq_mid M M' then Some CM' else None
    end
  end.

(* a term, a proof, a path, a context *)
Inductive expr_value :=
  | Val (v : expr_tm) (pf : value v) (C : dy_ctx)
.

Inductive state :=
  | ST (mem : path -> option expr_value)
       (t : time)
.

Definition update_m {X} mem (p : path) (x : X) :=
  fun p1 => if eq_p p1 p then Some x else mem p1.

Definition empty_mem {X} (p : path) : option X := None.

Notation "p '!->' v ';' mem" := (update_m mem p v)
                              (at level 100, v at next level, right associativity).

Notation "Cout '[|' Cin '|]'" := (dy_plugin_c Cout Cin)
                              (at level 100, Cin at next level, right associativity).
Notation "'[||]'" := (dy_c_hole) (at level 100).

Inductive EevalR (C : dy_ctx) (st : state)
    : expr_tm -> expr_value -> state -> Prop :=
  | Eeval_var x v mem t
             (STATE : ST mem t = st)
             (ADDR : [] <> addr_x C x)
             (ACCESS : Some v = mem (addr_x C x))
    : EevalR C st (e_var x) v st
  | Eeval_lam x e
    : EevalR C st (e_lam x e)
            (Val (e_lam x e) (v_fn x e) C) st
  | Eeval_app e1 e2 
              x e C_lam st_lam
              arg mem t
              v st_v
              (FN : EevalR C st e1
                           (Val (e_lam x e) (v_fn x e) C_lam) st_lam)
              (ARG : EevalR C st_lam e2
                            arg (ST mem t))
              (BODY : EevalR (C_lam [|dy_c_lam x t  ([||])|])
                             (ST (t :: (dy_level C_lam) !-> arg ; mem) (update_t t))
                              e v st_v)
    : EevalR C st (e_app e1 e2) v st_v
  | Eeval_link m e C_m st_m v st_v
               (MOD : MevalR C st m C_m st_m)
               (LINK : EevalR C_m st_m e v st_v)
    : EevalR C st (e_link m e) v st_v

with MevalR (C : dy_ctx) (st : state)
    : mod_tm -> dy_ctx -> state -> Prop :=
  | Meval_empty
    : MevalR C st m_empty C st
  | Meval_var M C_M (ACCESS : Some C_M = ctx_M C M)
    : MevalR C st (m_var M) C_M st
  | Meval_lete x e v_e mem t
               m C_m st_m
               (EVALe : EevalR C st e v_e (ST mem t))
               (EVALm : MevalR (C [|dy_c_lete x t ([||])|]) 
                        (ST (t :: (dy_level C) !-> v_e ; mem) (update_t t))
                        m C_m st_m)
    : MevalR C st (m_lete x e m) C_m st_m
  | Meval_letm M m1 C_m1 st_m1
               m2 C_m2 st_m2
               (EVALm1 : MevalR C st m1 C_m1 st_m1)
               (EVALm2 : MevalR (C [|dy_c_letm M C_m1 ([||])|]) st_m1
                         m2 C_m2 st_m2)
    : MevalR C st (m_letm M m1 m2) C_m2 st_m2
.

Scheme EevalR_ind_mut := Induction for EevalR Sort Prop
with MevalR_ind_mut := Induction for MevalR Sort Prop.

Definition Reach (tm1 tm2 : Type) := tm1 -> dy_ctx -> state -> tm2 -> Prop.

(* Reachability relation, sensible version *)
Inductive _EreachE (C : dy_ctx) (st : state)
    : Reach expr_tm expr_tm :=
  | _ere_refl e
    : _EreachE C st e 
               C st e
  | _ere_var x mem t v pf C_v
            (STATE : ST mem t = st)
            (ADDR : [] <> addr_x C x)
            (ACCESS : Some (Val v pf C_v) = mem (addr_x C x))
    : _EreachE C st (e_var x) 
               C_v st v
  | _ere_app_left e1 e2 C' st' e'
                 (REACHl : _EreachE C st e1
                                    C' st' e')
    : _EreachE C st (e_app e1 e2) 
               C' st' e'
  | _ere_app_right e1 e2 st1 v C' st' e'
                  (FN : EevalR C st e1 v st1)
                  (REACHr : _EreachE C st1 e2
                                     C' st' e')
    : _EreachE C st (e_app e1 e2)
               C' st' e'
  | _ere_app_body e1 e2 x e C_lam st_lam
                 arg mem t
                 C' st' e'
                 (FN : EevalR C st e1 
                             (Val (e_lam x e) (v_fn x e) C_lam) st_lam)
                 (ARG : EevalR C st_lam e2
                               arg (ST mem t))
                 (REACHb : _EreachE (C_lam[|dy_c_lam x t  ([||])|]) 
                                    (ST (t :: (dy_level C_lam) !-> arg ; mem) (update_t t)) e
                                     C' st' e')
    : _EreachE C st (e_app e1 e2)
               C' st' e'
  | _ere_link_m m e C' st' e'
               (REACHm : _MreachE C st m
                                  C' st' e')
    : _EreachE C st (e_link m e)
               C' st' e'
  | _ere_link_e m e C_m st_m C' st' e'
               (MOD : MevalR C st m C_m st_m)
               (REACHe : _EreachE C_m st_m e
                                  C' st' e')
    : _EreachE C st (e_link m e)
               C' st' e'

with _MreachE (C : dy_ctx) (st : state)
    : Reach mod_tm expr_tm :=
  | _mre_lete_e x e m C' st' e'
               (REACHe : _EreachE C st e
                                  C' st' e')
    : _MreachE C st (m_lete x e m)
               C' st' e'
  | _mre_lete_m x e m v mem t
                C' st' e'
             (EVALx : EevalR C st e v (ST mem t))
             (REACHm : _MreachE (C[|dy_c_lete x t  ([||])|])
                                (ST (t :: (dy_level C) !-> v ; mem) (update_t t)) m
                                 C' st' e')
    : _MreachE C st (m_lete x e m)
               C' st' e'
  | _mre_letm_m1 M m1 m2 C' st' e'
               (REACHm : _MreachE C st m1
                                  C' st' e')
    : _MreachE C st (m_letm M m1 m2)
               C' st' e'
  | _mre_letm_m2 M m1 m2 C_M st_M
                 C' st' e'
             (EVALM : MevalR C st m1 C_M st_M)
             (REACHm : _MreachE (C[|dy_c_letm M C_M ([||])|]) st_M m2
                                 C' st' e')
    : _MreachE C st (m_letm M m1 m2)
               C' st' e'.

Scheme __EreachE_ind_mut := Induction for _EreachE Sort Prop
with __MreachE_ind_mut := Induction for _MreachE Sort Prop.

Inductive _MreachM (C : dy_ctx) (st : state)
    : Reach mod_tm mod_tm :=
  | _mrm_refl m
    : _MreachM C st m
               C st m
  | _mrm_var M C_M (ACCESS : Some C_M = ctx_M C M)
    : _MreachM C st (m_var M)
               C_M st m_empty
  | _mrm_lete_e x e m C' st' m'
               (REACHe : _EreachM C st e
                                  C' st' m')
    : _MreachM C st (m_lete x e m)
               C' st' m'
  | _mrm_lete_m x e m v mem t
                C' st' m'
             (EVALx : EevalR C st e v (ST mem t))
             (REACHm : _MreachM (C[|dy_c_lete x t  ([||])|]) 
                                (ST (t :: (dy_level C) !-> v ; mem) (update_t t)) m
                                 C' st' m')
    : _MreachM C st (m_lete x e m)
               C' st' m'
  | _mrm_letm_m1 M m1 m2 C' st' m'
               (REACHm : _MreachM C st m1
                                  C' st' m')
    : _MreachM C st (m_letm M m1 m2)
               C' st' m'
  | _mrm_letm_m2 M m1 m2 C_M st_M
                 C' st' m'
             (EVALM : MevalR C st m1 C_M st_M)
             (REACHm : _MreachM (C[|dy_c_letm M C_M ([||])|]) st_M m2
                                 C' st' m')
    : _MreachM C st (m_letm M m1 m2)
               C' st' m'

with _EreachM (C : dy_ctx) (st : state)
    : Reach expr_tm mod_tm :=
  | _erm_app_left e1 e2 C' st' m'
                 (REACHl : _EreachM C st e1
                                    C' st' m')
    : _EreachM C st (e_app e1 e2) 
               C' st' m'
  | _erm_app_right e1 e2 v1 st1 C' st' m'
                  (FN : EevalR C st e1 v1 st1)
                  (REACHr : _EreachM C st1 e2
                                     C' st' m')
    : _EreachM C st (e_app e1 e2)
               C' st' m'
  | _erm_app_body e1 e2 x e C_lam st_lam
                 arg mem t
                 C' st' m'
                 (FN : EevalR C st e1 
                              (Val (e_lam x e) (v_fn x e) C_lam) st_lam)
                 (ARG : EevalR C st_lam e2 arg (ST mem t))
                 (REACHb : _EreachM (C_lam[|dy_c_lam x t ([||])|]) 
                                    (ST (t :: (dy_level C_lam) !-> arg ; mem) (update_t t)) e
                                     C' st' m')
    : _EreachM C st (e_app e1 e2)
               C' st' m'
  | _erm_link_m m e C' st' m'
               (REACHm : _MreachM C st m
                                  C' st' m')
    : _EreachM C st (e_link m e)
               C' st' m'
  | _erm_link_e m e C_m st_m C' st' m'
               (MOD : MevalR C st m C_m st_m)
               (REACHe : _EreachM C_m st_m e
                                  C' st' m')
    : _EreachM C st (e_link m e)
               C' st' m'
.

Scheme __EreachM_ind_mut := Induction for _EreachM Sort Prop
with __MreachM_ind_mut := Induction for _MreachM Sort Prop.

(* for proofs *)
Inductive EreachE (C : dy_ctx) (st : state)
    : Reach expr_tm expr_tm :=
  | ere_refl e
    : EreachE C st e 
              C st e
  | ere_var x mem t v pf C_v
            (STATE : ST mem t = st)
            (ADDR : [] <> addr_x C x)
            (ACCESS : Some (Val v pf C_v) = mem (addr_x C x))
    : EreachE C st (e_var x) 
              C_v st v
  | ere_app_left e1 e2 C' st' e'
                 (REACHl : EreachE C st e1
                                   C' st' e')
    : EreachE C st (e_app e1 e2) 
              C' st' e'
  | ere_app_right e1 e2 st_lam v pf C_lam C' st' e'
                  (FN : EevalR C st e1 (Val v pf C_lam) st_lam)
                  (FNr : EreachE C st e1 C_lam st_lam v)
                  (REACHr : EreachE C st_lam e2
                                    C' st' e')
    : EreachE C st (e_app e1 e2)
              C' st' e'
  | ere_app_body e1 e2 x e C_lam st_lam
                 arg pf C_arg mem t
                 C' st' e'
                 (FN : EevalR C st e1 
                             (Val (e_lam x e) (v_fn x e) C_lam) st_lam)
                 (FNr : EreachE C st e1 C_lam st_lam (e_lam x e))
                 (ARG : EevalR C st_lam e2
                               (Val arg pf C_arg) (ST mem t))
                 (ARGr : EreachE C st_lam e2 C_arg (ST mem t) arg)
                 (REACHb : EreachE (C_lam[|dy_c_lam x t ([||])|]) 
                                    (ST (t :: (dy_level C_lam) !-> (Val arg pf C_arg) ; mem) (update_t t)) e
                                     C' st' e')
    : EreachE C st (e_app e1 e2)
              C' st' e'
  | ere_link_m m e C' st' e'
               (REACHm : MreachE C st m
                                 C' st' e')
    : EreachE C st (e_link m e)
              C' st' e'
  | ere_link_e m e C_m st_m C' st' e'
              (MOD : MevalR C st m C_m st_m)
              (MODr : MreachM C st m C_m st_m m_empty)
              (REACHe : EreachE C_m st_m e
                                C' st' e')
    : EreachE C st (e_link m e)
              C' st' e'

with MreachE (C : dy_ctx) (st : state)
    : Reach mod_tm expr_tm :=
  | mre_lete_e x e m C' st' e'
               (REACHe : EreachE C st e
                                 C' st' e')
    : MreachE C st (m_lete x e m)
              C' st' e'
  | mre_lete_m x e m v pf C_x mem t
               C' st' e'
             (EVALx : EevalR C st e (Val v pf C_x) (ST mem t))
             (EVALxr : EreachE C st e C_x (ST mem t) v)
             (REACHm : MreachE (C[|dy_c_lete x t ([||])|])
                                (ST (t :: (dy_level C) !-> (Val v pf C_x) ; mem) (update_t t)) m
                                 C' st' e')
    : MreachE C st (m_lete x e m)
              C' st' e'
  | mre_letm_m1 M m1 m2 C' st' e'
              (REACHm : MreachE C st m1
                                C' st' e')
    : MreachE C st (m_letm M m1 m2)
              C' st' e'
  | mre_letm_m2 M m1 m2 C_M st_M
                C' st' e'
             (EVALM : MevalR C st m1 C_M st_M)
             (EVALM : MreachM C st m1 C_M st_M m_empty)
             (REACHm : MreachE (C[|dy_c_letm M C_M ([||])|]) st_M m2
                                C' st' e')
    : MreachE C st (m_letm M m1 m2)
              C' st' e'

with MreachM (C : dy_ctx) (st : state)
    : Reach mod_tm mod_tm :=
  | mrm_refl m
    : MreachM C st m
              C st m
  | mrm_var M C_M (ACCESS : Some C_M = ctx_M C M)
    : MreachM C st (m_var M)
              C_M st m_empty
  | mrm_lete_e x e m C' st' m'
               (REACHe : EreachM C st e
                                  C' st' m')
    : MreachM C st (m_lete x e m)
              C' st' m'
  | mrm_lete_m x e m v pf C_x mem t
               C' st' m'
             (EVALx : EevalR C st e (Val v pf C_x) (ST mem t))
             (EVALxr : EreachE C st e C_x (ST mem t) v)
             (REACHm : MreachM (C[|dy_c_lete x t ([||])|]) 
                               (ST (t :: (dy_level C) !-> (Val v pf C_x) ; mem) (update_t t)) m
                                C' st' m')
    : MreachM C st (m_lete x e m)
              C' st' m'
  | mrm_letm_m1 M m1 m2 C' st' m'
               (REACHm : MreachM C st m1
                                 C' st' m')
    : MreachM C st (m_letm M m1 m2)
              C' st' m'
  | mrm_letm_m2 M m1 m2 C_M st_M
                C' st' m'
             (EVALM : MevalR C st m1 C_M st_M)
             (EVALMr : MreachM C st m1 C_M st_M m_empty)
             (REACHm : MreachM (C[|dy_c_letm M C_M ([||])|]) st_M m2
                                C' st' m')
    : MreachM C st (m_letm M m1 m2)
              C' st' m'

with EreachM (C : dy_ctx) (st : state)
    : Reach expr_tm mod_tm :=
  | erm_app_left e1 e2 C' st' m'
                (REACHl : EreachM C st e1
                                  C' st' m')
    : EreachM C st (e_app e1 e2) 
              C' st' m'
  | erm_app_right e1 e2 v pf C_lam st_lam C' st' m'
                 (FN : EevalR C st e1 (Val v pf C_lam) st_lam)
                 (FNr : EreachE C st e1 C_lam st_lam v)
                 (REACHr : EreachM C st_lam e2
                                   C' st' m')
    : EreachM C st (e_app e1 e2)
              C' st' m'
  | erm_app_body e1 e2 x e C_lam st_lam
                 arg pf C_arg mem t
                 C' st' m'
                 (FN : EevalR C st e1 
                              (Val (e_lam x e) (v_fn x e) C_lam) st_lam)
                 (FNr : EreachE C st e1 
                                C_lam st_lam (e_lam x e))
                 (ARG : EevalR C st_lam e2 (Val arg pf C_arg) (ST mem t))
                 (ARGr : EreachE C st_lam e2 C_arg (ST mem t) arg)
                 (REACHb : EreachM (C_lam[|dy_c_lam x t ([||])|]) 
                                   (ST (t :: (dy_level C_lam) !-> (Val arg pf C_arg) ; mem) (update_t t)) e
                                    C' st' m')
    : EreachM C st (e_app e1 e2)
              C' st' m'
  | erm_link_m m e C' st' m'
              (REACHm : MreachM C st m
                                C' st' m')
    : EreachM C st (e_link m e)
              C' st' m'
  | erm_link_e m e C_m st_m C' st' m'
              (MOD : MevalR C st m C_m st_m)
              (MODr : MreachM C st m C_m st_m m_empty)
              (REACHe : EreachM C_m st_m e
                                C' st' m')
    : EreachM C st (e_link m e)
              C' st' m'
.

Scheme _EreachE_ind_mut := Induction for EreachE Sort Prop
with _EreachM_ind_mut := Induction for EreachM Sort Prop
with _MreachE_ind_mut := Induction for MreachE Sort Prop
with _MreachM_ind_mut := Induction for MreachM Sort Prop.

Notation "'<e|' C1 st1 tm1 '~>' C2 st2 tm2 '|e>'" := (EreachE C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

Notation "'<m|' C1 st1 tm1 '~>' C2 st2 tm2 '|e>'" := (MreachE C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

Notation "'<m|' C1 st1 tm1 '~>' C2 st2 tm2 '|m>'" := (MreachM C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

Notation "'<e|' C1 st1 tm1 '~>' C2 st2 tm2 '|m>'" := (EreachM C1 st1 tm1 C2 st2 tm2) 
                                               (at level 10, 
                                                C1 at next level, st1 at next level, tm1 at next level,
                                                C2 at next level, st2 at next level, tm2 at next level).

(* sanity check *)
Lemma ere_trans : forall C1 st1 e1
                         C2 st2 e2
                         C3 st3 e3
                         (REACH1 : <e| C1 st1 e1 ~> C2 st2 e2 |e>)
                         (REACH2 : <e| C2 st2 e2 ~> C3 st3 e3 |e>),
                         <e| C1 st1 e1 ~> C3 st3 e3 |e>.
Proof.
  intros. generalize dependent e3.
  revert C3 st3.
  apply (_EreachE_ind_mut
    (fun C1 st1 e1 
         C2 st2 e2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 e2 |e>)=> 
         forall C3 st3 e3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 e3 |e>),
                <e| C1 st1 e1 ~> C3 st3 e3 |e>)
    (fun C1 st1 e1 
         C2 st2 m2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 e3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 e3 |e>),
                <e| C1 st1 e1 ~> C3 st3 e3 |e>)
    (fun C1 st1 m1
         C2 st2 e2
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 e2 |e>) =>
         forall C3 st3 e3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 e3 |e>),
                <m| C1 st1 m1 ~> C3 st3 e3 |e>)
    (fun C1 st1 m1 
         C2 st2 m2 
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 e3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 e3 |e>),
                <m| C1 st1 m1 ~> C3 st3 e3 |e>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma mrm_trans : forall C1 st1 m1
                         C2 st2 m2
                         C3 st3 m3
                         (REACH1 : <m| C1 st1 m1 ~> C2 st2 m2 |m>)
                         (REACH2 : <m| C2 st2 m2 ~> C3 st3 m3 |m>),
                         <m| C1 st1 m1 ~> C3 st3 m3 |m>.
Proof.
  intros. generalize dependent m3.
  revert C3 st3.
  apply (_MreachM_ind_mut
    (fun C1 st1 e1 
         C2 st2 e2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 e2 |e>)=> 
         forall C3 st3 m3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 m3 |m>),
                <e| C1 st1 e1 ~> C3 st3 m3 |m>)
    (fun C1 st1 e1 
         C2 st2 m2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 m3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 m3 |m>),
                <e| C1 st1 e1 ~> C3 st3 m3 |m>)
    (fun C1 st1 m1
         C2 st2 e2
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 e2 |e>) =>
         forall C3 st3 m3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 m3 |m>),
                <m| C1 st1 m1 ~> C3 st3 m3 |m>)
    (fun C1 st1 m1 
         C2 st2 m2 
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 m3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 m3 |m>),
                <m| C1 st1 m1 ~> C3 st3 m3 |m>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma ermre_trans : forall C1 st1 e1
                           C2 st2 m2
                           C3 st3 e3
                           (REACH1 : <e| C1 st1 e1 ~> C2 st2 m2 |m>)
                           (REACH2 : <m| C2 st2 m2 ~> C3 st3 e3 |e>),
                           <e| C1 st1 e1 ~> C3 st3 e3 |e>. 
Proof.
  intros. generalize dependent e3.
  revert C3 st3.
  apply (_EreachM_ind_mut
    (fun C1 st1 e1 
         C2 st2 e2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 e2 |e>)=> 
         forall C3 st3 e3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 e3 |e>),
                <e| C1 st1 e1 ~> C3 st3 e3 |e>)
    (fun C1 st1 e1 
         C2 st2 m2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 e3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 e3 |e>),
                <e| C1 st1 e1 ~> C3 st3 e3 |e>)
    (fun C1 st1 m1
         C2 st2 e2
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 e2 |e>) =>
         forall C3 st3 e3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 e3 |e>),
                <m| C1 st1 m1 ~> C3 st3 e3 |e>)
    (fun C1 st1 m1 
         C2 st2 m2 
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 e3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 e3 |e>),
                <m| C1 st1 m1 ~> C3 st3 e3 |e>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma mrerm_trans : forall C1 st1 m1
                           C2 st2 e2
                           C3 st3 m3
                           (REACH1 : <m| C1 st1 m1 ~> C2 st2 e2 |e>)
                           (REACH2 : <e| C2 st2 e2 ~> C3 st3 m3 |m>),
                           <m| C1 st1 m1 ~> C3 st3 m3 |m>. 
Proof.
  intros. generalize dependent m3.
  revert C3 st3.
  apply (_MreachE_ind_mut
    (fun C1 st1 e1 
         C2 st2 e2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 e2 |e>)=> 
         forall C3 st3 m3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 m3 |m>),
                <e| C1 st1 e1 ~> C3 st3 m3 |m>)
    (fun C1 st1 e1 
         C2 st2 m2 
         (REACH1 : <e| C1 st1 e1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 m3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 m3 |m>),
                <e| C1 st1 e1 ~> C3 st3 m3 |m>)
    (fun C1 st1 m1
         C2 st2 e2
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 e2 |e>) =>
         forall C3 st3 m3 
                (REACH2 : <e| C2 st2 e2 ~> C3 st3 m3 |m>),
                <m| C1 st1 m1 ~> C3 st3 m3 |m>)
    (fun C1 st1 m1 
         C2 st2 m2 
         (REACH1 : <m| C1 st1 m1 ~> C2 st2 m2 |m>)=> 
         forall C3 st3 m3 
                (REACH2 : <m| C2 st2 m2 ~> C3 st3 m3 |m>),
                <m| C1 st1 m1 ~> C3 st3 m3 |m>));
   eauto using EreachE, EreachM, MreachE, MreachM;
   intros; try inversion pf; subst; inversion REACH2; subst;
   eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma c_plugin_assoc : forall C1 C2 C3, C1[| C2[| C3 |] |] = ((C1[|C2|])[|C3|]).
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
  rewrite IHC1_2. eauto.
Qed.

Lemma eq_p_eq : forall p1 p2, eq_p p1 p2 = true <-> p1 = p2.
Proof.
  induction p1; induction p2;
  intros; simpl;
  try rewrite IHp1; try rewrite IHp2;
  eauto.
  - split; eauto.
  - split; intros contra; inversion contra.
  - split; intros contra; inversion contra.
  - unfold eq_t. remember (a =? a0) as eqa.
    destruct eqa; simpl; symmetry in Heqeqa;
    try rewrite Nat.eqb_eq in Heqeqa;
    try rewrite Nat.eqb_neq in Heqeqa.
    + split; intros. rewrite Heqeqa in *.
      apply IHp1 in H. rewrite H. eauto.
      eapply IHp1. inversion H; eauto.
    + split; intros contra; inversion contra.
      apply Heqeqa in H0; inversion H0.
Qed.

Lemma c_plugin_adds_level : forall C1 C2, eq_p (dy_level(C1[|C2|])) (dy_level C2 ++ dy_level C1) = true.
Proof.
  induction C1;
  intros; try rewrite IHC1;
  try apply Nat.eqb_eq; try rewrite app_nil_r in *; 
  try rewrite c_plugin_assoc in *; simpl in *; 
  eauto; try apply eq_p_eq; eauto;
  specialize (IHC1 C2); rewrite eq_p_eq in IHC1;
  rewrite IHC1; rewrite app_assoc; eauto.
Qed.

(* equivalence between reachability relations *)
Lemma Eeval_then_reach :
    forall Ci sti ei v stv
           (EVAL : EevalR Ci sti ei v stv)
           ev pf Cv mem t
           (VAL : v = Val ev pf Cv)
           (STATE : stv = ST mem t),
          <e| Ci sti ei ~> Cv stv ev |e>.
Proof.
  apply (EevalR_ind_mut
    (fun Ci sti ei v stv
        (EVAL : EevalR Ci sti ei v stv) =>
        forall ev pf Cv mem t
              (VAL : v = Val ev pf Cv)
              (STATE : stv = ST mem t),
        <e| Ci sti ei ~> Cv stv ev |e>)
    (fun Ci sti mi Cv stv
        (EVAL : MevalR Ci sti mi Cv stv) =>
        <m| Ci sti mi ~> Cv stv m_empty |m>));
  intros; try inversion STATE0; try inversion STATE;
          try inversion VAL; try destruct st_lam;
          try destruct st_m; try destruct v_e;
          try destruct v_m1; try destruct arg; subst; 
          eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma Meval_then_reach :
    forall Ci sti mi Cv stv
           (EVAL : MevalR Ci sti mi Cv stv),
           <m| Ci sti mi ~> Cv stv m_empty |m>.
Proof.
  apply (MevalR_ind_mut
    (fun Ci sti ei v stv
        (EVAL : EevalR Ci sti ei v stv) =>
        forall ev pf Cv mem t
              (VAL : v = Val ev pf Cv)
              (STATE : stv = ST mem t),
        <e| Ci sti ei ~> Cv stv ev |e>)
    (fun Ci sti mi Cv stv
        (EVAL : MevalR Ci sti mi Cv stv) =>
        <m| Ci sti mi ~> Cv stv m_empty |m>));
  intros; try inversion STATE0; try inversion STATE;
          try inversion VAL; try destruct st_lam;
          try destruct st_m; try destruct v_e;
          try destruct v_m1; try destruct arg; subst; 
          eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma EreachE_equiv_left :
    forall C1 st1 e1 C2 st2 e2,
          <e| C1 st1 e1 ~> C2 st2 e2 |e> ->
          _EreachE C1 st1 e1 C2 st2 e2.
Proof.
  apply (_EreachE_ind_mut 
    (fun C1 st1 e1 C2 st2 e2
        (REACH : <e| C1 st1 e1 ~> C2 st2 e2 |e>) =>
        _EreachE C1 st1 e1 C2 st2 e2)
    (fun C1 st1 e1 C2 st2 m2
        (REACH : <e| C1 st1 e1 ~> C2 st2 m2 |m>) =>
        _EreachM C1 st1 e1 C2 st2 m2)
    (fun C1 st1 m1 C2 st2 e2
        (REACH : <m| C1 st1 m1 ~> C2 st2 e2 |e>) =>
        _MreachE C1 st1 m1 C2 st2 e2)
    (fun C1 st1 m1 C2 st2 m2
        (REACH : <m| C1 st1 m1 ~> C2 st2 m2 |m>) =>
        _MreachM C1 st1 m1 C2 st2 m2));
  intros; eauto using EreachE, EreachM, MreachE, MreachM, _EreachE, _MreachE, _EreachM, _MreachM.
Qed.

Lemma EreachE_equiv_right :
    forall C1 st1 e1 C2 st2 e2,
          _EreachE C1 st1 e1 C2 st2 e2 ->
          <e| C1 st1 e1 ~> C2 st2 e2 |e>.
Proof.
  apply (__EreachE_ind_mut 
    (fun C1 st1 e1 C2 st2 e2
        (REACH : _EreachE C1 st1 e1 C2 st2 e2) =>
        <e| C1 st1 e1 ~> C2 st2 e2 |e>)
    (fun C1 st1 m1 C2 st2 e2
        (REACH : _MreachE C1 st1 m1 C2 st2 e2) =>
        <m| C1 st1 m1 ~> C2 st2 e2 |e>));
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
  forall C1 st1 e1 C2 st2 e2,
         _EreachE C1 st1 e1 C2 st2 e2 <->
          <e| C1 st1 e1 ~> C2 st2 e2 |e>.
Proof. 
  intros; split; try apply EreachE_equiv_left; try apply EreachE_equiv_right. 
Qed.

Fixpoint dy_to_st C :=
  match C with
  | ([||]) => st_c_hole
  | dy_c_lam x _ C' => st_c_lam x (dy_to_st C')
  | dy_c_lete x _ C' => st_c_lete x (dy_to_st C')
  | dy_c_letm M CM C' => st_c_letm M (dy_to_st CM) (dy_to_st C')
  end.

Lemma dy_to_st_plugin :
  forall Cout Cin,
    dy_to_st (Cout[|Cin|]) = st_c_plugin (dy_to_st Cout) (dy_to_st Cin).
Proof.
  induction Cout; intros; simpl; try rewrite IHCout; eauto.
  rewrite IHCout2. eauto.
Qed. 

Lemma mod_is_static_none : forall (dC : dy_ctx) (M : mod_id),
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

Lemma mod_is_static_some : forall (dC : dy_ctx) (M : mod_id),
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

(* Induction principle: preserves a predicate on C, st, e *)
Lemma EreachE_ind_mut : 
  forall (Pe : forall (C : dy_ctx) (st : state) (e : expr_tm), Prop)
         (Pm : forall (C : dy_ctx) (st : state) (m : mod_tm), Prop),
    (forall C st e, (Pe C st e) -> 
      (match st with
      | ST mem _ =>
          forall addr,
          match mem addr with
            | None => True
            | Some (Val v pf C') => Pe C' st v
          end
      end)) ->
    (forall C st e1 e2,
            Pe C st (e_app e1 e2) -> Pe C st e1) ->
    (forall C st e1 e2 C_lam st_lam lam,
            Pe C st (e_app e1 e2) -> 
            Pe C_lam st_lam lam -> Pe C st_lam e2) ->
    (forall C st e1 e2 C_lam st_lam x e
            C_arg mem t arg pf,
            Pe C st (e_app e1 e2) ->
            Pe C_lam st_lam (e_lam x e) ->
            Pe C_arg (ST mem t) arg ->
            Pe (C_lam[|dy_c_lam x t  ([||])|])
              (ST (t :: (dy_level C_lam) !-> (Val arg pf C_arg) ; mem) (update_t t)) e) ->
    (forall C st m e, Pe C st (e_link m e) -> Pm C st m) ->
    (forall C st m e C_m st_m,
            Pe C st (e_link m e) -> (MevalR C st m C_m st_m) ->
            Pm C_m st_m m_empty -> Pe C_m st_m e) ->
    (forall C st M C_M (ACCESS : Some C_M = ctx_M C M),
            Pm C st (m_var M) -> Pm C_M st m_empty) ->
    (forall C st x e m,
            Pm C st (m_lete x e m) -> Pe C st e) ->
    (forall C st x e m C_x mem t v pf,
            Pm C st (m_lete x e m) ->
            Pe C_x (ST mem t) v ->
            Pm (C[|dy_c_lete x t  ([||])|])
              (ST (t :: (dy_level C) !-> (Val v pf C_x) ; mem) (update_t t)) m) ->
    (forall C st M m1 m2,
            Pm C st (m_letm M m1 m2) -> Pm C st m1) ->
    (forall C st M m1 m2 C_M st_M,
            Pm C st (m_letm M m1 m2) ->
            (MevalR C st m1 C_M st_M) ->
            Pm C_M st_M m_empty ->
            Pm (C[|dy_c_letm M C_M  ([||])|]) st_M m2) ->
    (forall C st e C' st' e'
            (INIT : Pe C st e)
            (REACH : <e| C st e ~> C' st' e' |e>),
            Pe C' st' e').
Proof. 
(* intros just before our goal, then fix 8, on REACH, 
   with mutual induction on EreachM, MreachE, MreachM *)
  intros Pe Pm MEM APPl APPr APPb LINKm LINKe MVAR LETex LETem LETm1 LETm2.
  fix IHere 8 with 
    (IHerm C st e C' st' m'
          (INIT : Pe C st e)
          (REACH : <e| C st e ~> C' st' m' |m>)
          { struct REACH }
          : Pm C' st' m')
    (IHmre C st m C' st' e'
          (INIT : Pm C st m)
          (REACH : <m| C st m ~> C' st' e' |e>)
          { struct REACH }
          : Pe C' st' e')
    (IHmrm C st m C' st' m'
          (INIT : Pm C st m)
          (REACH : <m| C st m ~> C' st' m' |m>)
          { struct REACH }
          : Pm C' st' m').
  - intros. destruct REACH.
    + exact INIT.
    + specialize (MEM C st (e_var x) INIT).
      destruct st. specialize (MEM (addr_x C x)).
      inversion STATE; subst. rewrite <- ACCESS in MEM.
      exact MEM.
    + apply (IHere C st e1 C' st' e'). eapply APPl.
      exact INIT. exact REACH.
    + apply (IHere C st_lam e2 C' st' e').
      apply APPr with (st := st) (e1 := e1) (C_lam := C_lam) (lam := v).
      exact INIT. apply (IHere C st e1 C_lam st_lam v).
      eapply APPl. exact INIT. exact REACH1. exact REACH2.
    + assert (LAM : Pe C_lam st_lam (e_lam x e)).
      apply (IHere C st e1 C_lam st_lam (e_lam x e)).
      eapply APPl. exact INIT. exact REACH1.
      apply (IHere (C_lam [|dy_c_lam x t ([||])|])
            (ST (t :: (dy_level C_lam) !-> Val arg pf C_arg; mem)
            (update_t t)) e C' st' e').
      apply APPb with (C := C) (st := st) (e1 := e1) (e2 := e2) (st_lam := st_lam).
      exact INIT. exact LAM. 
      apply (IHere C st_lam e2 C_arg (ST mem t) arg).
      apply (APPr C st e1 e2 C_lam st_lam (e_lam x e)).
      exact INIT. exact LAM. exact REACH2. exact REACH3.
    + apply (IHmre C st m C' st' e'). apply LINKm with (e := e). exact INIT. exact REACHm.
    + apply (IHere C_m st_m e C' st' e'). apply LINKe with (C := C) (st := st) (m := m).
      exact INIT. exact MOD.
      apply (IHmrm C st m C_m st_m m_empty).
      eapply LINKm. exact INIT. exact MODr. exact REACH.
  - intros. destruct REACH.
    + apply (IHerm C st e1 C' st' m'). eapply APPl.
      exact INIT. exact REACH.
    + apply (IHerm C st_lam e2 C' st' m').
      eapply APPr with (C_lam := C_lam) (lam := v). exact INIT.
      apply (IHere C st e1 C_lam st_lam v).
      eapply APPl. exact INIT. exact FNr. exact REACH.
    + assert (LAM : Pe C_lam st_lam (e_lam x e)).
      apply (IHere C st e1 C_lam st_lam (e_lam x e)).
      eapply APPl. exact INIT. exact FNr.
      apply (IHerm (C_lam [|dy_c_lam x t ([||])|])
            (ST (t :: (dy_level C_lam) !-> Val arg pf C_arg; mem)
            (update_t t)) e C' st' m').
      eapply APPb with (st_lam := st_lam). exact INIT. exact LAM.
      apply (IHere C st_lam e2 C_arg (ST mem t) arg).
      apply (APPr C st e1 e2 C_lam st_lam (e_lam x e)).
      exact INIT. exact LAM. exact ARGr. exact REACH.
    + apply (IHmrm C st m C' st' m').
      eapply LINKm. exact INIT. exact REACHm.
    + apply (IHerm C_m st_m e C' st' m').
      eapply LINKe. exact INIT. exact MOD.
      apply (IHmrm C st m C_m st_m m_empty).
      eapply LINKm. exact INIT. exact MODr. exact REACH.
  - intros. destruct REACH.
    + apply (IHere C st e C' st' e').
      eapply LETex. exact INIT. exact REACHe.
    + apply (IHmre (C [|dy_c_lete x t ([||])|])
        (ST (t :: (dy_level C) !-> Val v pf C_x; mem) (update_t t)) m
        C' st' e').
      eapply LETem. exact INIT.
      apply (IHere C st e C_x (ST mem t) v).
      eapply LETex. exact INIT. exact EVALxr. exact REACH.
    + apply (IHmre C st m1 C' st' e').
      eapply LETm1. exact INIT. exact REACH.
    + apply (IHmre (C [|dy_c_letm M C_M ([||])|]) st_M m2 C' st' e').
      eapply LETm2. exact INIT. exact EVALM.
      apply (IHmrm C st m1 C_M st_M m_empty).
      eapply LETm1. exact INIT. exact EVALM0. exact REACH.
  - intros. destruct REACH.
    + exact INIT.
    + specialize (MVAR C st M C_M ACCESS).
      apply MVAR. exact INIT.
    + apply (IHerm C st e C' st' m').
      eapply LETex. exact INIT. exact REACHe.
    + apply (IHmrm (C [|dy_c_lete x t ([||])|])
        (ST (t :: (dy_level C) !-> Val v pf C_x; mem) (update_t t)) m
        C' st' m').
      eapply LETem. exact INIT.
      apply (IHere C st e C_x (ST mem t) v).
      eapply LETex. exact INIT. exact EVALxr. exact REACH.
    + apply (IHmrm C st m1 C' st' m').
      eapply LETm1. exact INIT. exact REACH.
    + apply (IHmrm (C [|dy_c_letm M C_M ([||])|]) st_M m2 C' st' m').
      eapply LETm2. exact INIT. exact EVALM.
      apply (IHmrm C st m1 C_M st_M m_empty).
      eapply LETm1. exact INIT. exact REACH1. exact REACH2.
Qed.

Lemma value_reach_only_itself_e :
  forall C st v (pf : value v)
         C' st' e'
         (REACH : <e| C st v ~> C' st' e' |e>),
         C = C' /\ st = st' /\ v = e'.
Proof.
  intros; repeat split; inversion pf; inversion REACH; subst; eauto using EreachE;
  try inversion H0.
Qed.

Lemma value_reach_only_itself_m :
  forall C st v (pf : value v)
         C' st' m'
         (REACH : <e| C st v ~> C' st' m' |m>),
         False.
Proof.
  intros; repeat split; inversion pf; inversion REACH; subst; eauto using EreachM;
  try inversion H0.
Qed.

Lemma collect_ctx_expr_refl : forall e C, In C (collect_ctx_expr C e).
Proof.
  apply (expr_ind_mut
    (fun e =>
      forall C, In C (collect_ctx_expr C e))
    (fun m =>
      forall C, 
        let (o, ctxs) := collect_ctx_mod C m in In C ctxs));
  intros; simpl; eauto.
  - apply in_app_iff. left. apply H.
  - remember (collect_ctx_mod C m) as ol. destruct ol as [o l].
    specialize (H C). rewrite <- Heqol in H.
    destruct o; eauto. apply in_app_iff. left. eauto.
  - destruct (st_ctx_M C M); simpl; left; eauto.
  - destruct (collect_ctx_mod (C [[|st_c_lete x ([[||]])|]]) m).
    apply in_app_iff. left. apply H.
  - remember (collect_ctx_mod C m1) as ol.
    destruct ol as [o l]. specialize (H C). rewrite <- Heqol in H.
    destruct o; eauto.
    + destruct (collect_ctx_mod (C [[|st_c_letm M s ([[||]])|]]) m2).
      apply in_app_iff. left. eauto.
Qed.

Lemma Meval_then_collect :
  forall C st m C_m st_m
         (EVAL : MevalR C st m C_m st_m),
        match collect_ctx_mod (dy_to_st C) m with
        | (Some C_m', _) => C_m' = dy_to_st C_m
        | (None, _) => False
        end.
Proof.
  intros. induction EVAL; simpl; eauto.
  - pose proof mod_is_static_some as H.
    specialize (H C M). destruct H as [A B].
    specialize (A C_M). symmetry in ACCESS.
    specialize (A ACCESS). rewrite A. eauto.
  - rewrite dy_to_st_plugin in IHEVAL.
    simpl in IHEVAL.
    remember (collect_ctx_mod (dy_to_st C [[|st_c_lete x ([[||]])|]]) m) as ol.
    destruct ol. exact IHEVAL.
  - rewrite dy_to_st_plugin in IHEVAL2. simpl in IHEVAL2.
    destruct (collect_ctx_mod (dy_to_st C) m1). destruct o; try apply IHEVAL1.
    rewrite <- IHEVAL1 in IHEVAL2.
    destruct (collect_ctx_mod (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2).
    exact IHEVAL2.
Qed.

Definition ctx_bound_st ub st:=
  match st with
  | ST mem t =>
    forall addr,
      match mem addr with
      | Some (Val v _ C_v) =>
        forall sC (IN : In sC (collect_ctx_expr (dy_to_st C_v) v)),
               In sC ub
      | None => True
      end
  end.

Definition ctx_bound_expr ub C st e :=
  ctx_bound_st ub st /\
  forall sC (IN : In sC (collect_ctx_expr (dy_to_st C) e)),
         In sC ub.

Definition ctx_bound_mod ub C st m :=
  ctx_bound_st ub st /\
  let (o, ctxs) := collect_ctx_mod (dy_to_st C) m in
  forall sC (IN : In sC ctxs),
         In sC ub.

Lemma ere_ctx_bound :
  forall ub
         C st e
         C' st' e'
         (INIT : ctx_bound_expr ub C st e)
         (REACH : <e| C st e ~> C' st' e' |e>),
    ctx_bound_expr ub C' st' e'.
Proof.
  intros ub.
  apply (EreachE_ind_mut (ctx_bound_expr ub) (ctx_bound_mod ub)).
  - intros. unfold ctx_bound_expr in *. destruct H as [mem expr].
    destruct st. intros. remember (mem0 addr) as v.
    destruct v; eauto. destruct e0.
    split; eauto.
    unfold ctx_bound_st in *. specialize (mem addr).
    rewrite <- Heqv in mem. eauto.
  - intros. unfold ctx_bound_expr in *. destruct H as [mem expr].
    split; eauto. intros. specialize (expr sC).
    assert (In sC (collect_ctx_expr (dy_to_st C) (e_app e1 e2))).
    simpl. apply in_app_iff. left. eauto. eauto.
  - intros. unfold ctx_bound_expr in *. destruct H as [memi expri].
    destruct H0 as [memlam exprlam]. split; eauto.
    intros. specialize (expri sC). specialize (exprlam sC).
    assert (In sC (collect_ctx_expr (dy_to_st C) (e_app e1 e2))).
    simpl. apply in_app_iff. right. eauto. eauto.
  - intros. unfold ctx_bound_expr in *. destruct H as [memi expri].
    destruct H0 as [memlam exprlam]. destruct H1 as [memarg exprarg].
    split. 
    + unfold ctx_bound_st. unfold update_m. intro addr.
      destruct (eq_p addr (t :: (dy_level C_lam))). exact exprarg.
      apply memarg. 
    + rewrite dy_to_st_plugin. simpl. remember (dy_to_st C_lam) as st_C.
      simpl in exprlam. eauto.
  - intros C st m e [mem expr]. split. exact mem.
    simpl in expr. remember (collect_ctx_mod (dy_to_st C) m) as ol.
    destruct ol. destruct o; intros; specialize (expr sC).
    + assert (In sC (l ++ collect_ctx_expr s e)) as HINT.
      apply in_app_iff. left; eauto. eauto.
    + apply expr. eauto.
  - intros C st m e C_m st_m [mem expr] meval [memm exprm]. split. exact memm.
    apply Meval_then_collect in meval.
    simpl in expr. simpl in exprm. remember (collect_ctx_mod (dy_to_st C) m) as ol.
    destruct ol; destruct o; intros; specialize (expr sC). 
    + rewrite <- meval in *. 
      assert (In sC (l ++ collect_ctx_expr s e)) as HINT.
      apply in_app_iff. right. eauto. eauto.
    + inversion meval.
  - intros C st M C_M ACCESS [mem expr].
    split. exact mem. simpl in expr.
    pose proof mod_is_static_some as MOD.
    specialize (MOD C M). destruct MOD as [MODl MODr].
    symmetry in ACCESS. specialize (MODl C_M ACCESS).
    rewrite MODl in expr. simpl. intros; inversion IN; try inversion H.
    specialize (expr (dy_to_st C_M)).
    assert (In (dy_to_st C_M) [dy_to_st C; dy_to_st C_M]) as HINT.
    simpl; right; eauto. eauto.
  - intros C st x e m [mem expr].
    split. exact mem. simpl in expr.
    destruct (collect_ctx_mod (st_c_plugin (dy_to_st C) (st_c_lete x st_c_hole)) m).
    intros. specialize (expr sC).
    assert (In sC (collect_ctx_expr (dy_to_st C) e ++ l)) as HINT.
    apply in_app_iff. left. eauto. eauto.
  - intros C st x e m C_x mem t v pf 
    [memi expri] [memm exprm]. split.
    + unfold ctx_bound_st. unfold update_m. intro addr.
      destruct (eq_p addr (t :: (dy_level C))). exact exprm.
      apply memm.
    + simpl in expri. rewrite dy_to_st_plugin. simpl.
      destruct (collect_ctx_mod (st_c_plugin (dy_to_st C) (st_c_lete x st_c_hole)) m).
      intros. specialize (expri sC).
      assert (In sC (collect_ctx_expr (dy_to_st C) e ++ l)) as HINT.
      apply in_app_iff. right. eauto. eauto.
  - intros C st M m1 m2 [mem expr]. split. exact mem. simpl in expr.
    destruct (collect_ctx_mod (dy_to_st C) m1). destruct o; eauto.
    destruct (collect_ctx_mod (st_c_plugin (dy_to_st C) (st_c_letm M s st_c_hole)) m2). destruct o;
    intros; specialize (expr sC); 
    assert (In sC (l ++ l0)) as HINT; try apply in_app_iff; try left; eauto.
  - intros C st M m1 m2 C_M st_M [memi expri] meval [memm exprm].
    apply Meval_then_collect in meval. simpl in expri. simpl in exprm.
    remember (collect_ctx_mod (dy_to_st C) m1) as ol1. 
    destruct ol1. destruct o; unfold ctx_bound_mod in *;
    rewrite dy_to_st_plugin in *; simpl; split; try inversion meval; 
    try rewrite <- meval; eauto.
    destruct (collect_ctx_mod (dy_to_st C [[|st_c_letm M s ([[||]])|]]) m2).
    intros. assert (In sC (l ++ l0)) as HINT. apply in_app_iff. right. eauto. eauto.
Qed.

Theorem expr_ctx_bound :
  forall e C' st' e'
         (REACH : <e|  ([||]) (ST empty_mem 0) e ~> C' st' e' |e>),
         In (dy_to_st C') (collect_ctx_expr ([[||]]) e).
Proof.
  intros.
  pose proof (ere_ctx_bound (collect_ctx_expr st_c_hole e)  ([||]) (ST empty_mem 0) e C' st' e') as H.
  assert (ctx_bound_expr (collect_ctx_expr ([[||]]) e)  ([||])
          (ST empty_mem 0) e) as FINAL.
  - unfold ctx_bound_expr; split; simpl; eauto.
  - apply H in FINAL; try apply REACH. 
    destruct FINAL as [MEM KILLER].
    apply KILLER. apply collect_ctx_expr_refl.
Qed.
