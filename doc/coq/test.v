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

Definition eq_eid id1 id2 :=
  match id1, id2 with
  | eid x1, eid x2 => x1 =? x2
  end.

Definition eq_mid id1 id2 :=
  match id1, id2 with
  | mid M1, mid M2 => M1 =? M2
  end.

Fixpoint dy_level (C : dy_ctx) : path :=
  match C with
  | dy_c_hole => []
  | dy_c_lam _ t C'
  | dy_c_lete _ t  C' => t :: dy_level C'
  | dy_c_letm _ _  C' => dy_level C'
  end.

Fixpoint addr_x (C : dy_ctx) (x : expr_id) :=
  match C with
  | dy_c_hole => []
  | dy_c_lam x' tx' C'
  | dy_c_lete x' tx' C' =>
    match addr_x C' x with
    | [] => if eq_eid x x' then [tx'] else []
    | addr => tx' :: addr
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
  | Val (e : expr_tm) (v : value e) (C : dy_ctx)
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
              (BODY : EevalR (C_lam [|dy_c_lam x t dy_c_hole|])
                             (ST ((dy_level C_lam) ++ [t] !-> arg ; mem) (update_t t))
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
               (EVALm : MevalR (C [|dy_c_lete x t dy_c_hole|]) 
                        (ST ((dy_level C ++ [t]) !-> v_e ; mem) (update_t t))
                        m C_m st_m)
    : MevalR C st (m_lete x e m) C_m st_m
  | Meval_letm M m1 C_m1 st_m1
               m2 C_m2 st_m2
               (EVALm1 : MevalR C st m1 C_m1 st_m1)
               (EVALm2 : MevalR (C [|dy_c_letm M C_m1 dy_c_hole|]) st_m1
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
                 (REACHb : _EreachE (C_lam[|dy_c_lam x t dy_c_hole|]) 
                                    (ST ((dy_level C_lam ++ [t]) !-> arg ; mem) (update_t t)) e
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
             (REACHm : _MreachE (C[|dy_c_lete x t dy_c_hole|])
                                (ST ((dy_level C ++ [t]) !-> v ; mem) (update_t t)) m
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
             (REACHm : _MreachE (C[|dy_c_letm M C_M dy_c_hole|]) st_M m2
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
             (REACHm : _MreachM (C[|dy_c_lete x t dy_c_hole|]) 
                                (ST ((dy_level C ++ [t]) !-> v ; mem) (update_t t)) m
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
             (REACHm : _MreachM (C[|dy_c_letm M C_M dy_c_hole|]) st_M m2
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
                 (REACHb : _EreachM (C_lam[|dy_c_lam x t dy_c_hole|]) 
                                    (ST ((dy_level C_lam ++ [t]) !-> arg ; mem) (update_t t)) e
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
                 (REACHb : EreachE (C_lam[|dy_c_lam x t dy_c_hole|]) 
                                    (ST ((dy_level C_lam ++ [t]) !-> (Val arg pf C_arg) ; mem) (update_t t)) e
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
             (REACHm : MreachE (C[|dy_c_lete x t dy_c_hole|])
                                (ST ((dy_level C ++ [t]) !-> (Val v pf C_x) ; mem) (update_t t)) m
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
             (REACHm : MreachE (C[|dy_c_letm M C_M dy_c_hole|]) st_M m2
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
             (REACHm : MreachM (C[|dy_c_lete x t dy_c_hole|]) 
                               (ST ((dy_level C ++ [t]) !-> (Val v pf C_x) ; mem) (update_t t)) m
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
             (REACHm : MreachM (C[|dy_c_letm M C_M dy_c_hole|]) st_M m2
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
                 (REACHb : EreachM (C_lam[|dy_c_lam x t dy_c_hole|]) 
                                   (ST ((dy_level C_lam ++ [t]) !-> (Val arg pf C_arg) ; mem) (update_t t)) e
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

Lemma c_plugin_adds_level : forall C1 C2, eq_p (dy_level(C1[|C2|])) (dy_level C1 ++ dy_level C2) = true.
Proof.
  induction C1; induction C2;
  intros; simpl; 
  try rewrite IHC1; try rewrite IHC2; try unfold eq_t;
  eauto; try (assert (RR : tx =? tx = true);
  try apply Nat.eqb_eq; eauto; try rewrite RR; try clear RR; eauto).
  - assert (RR : dy_level (dy_c_letm M C2_1 C2_2) = dy_level C2_2); eauto;
    rewrite <- RR; clear RR; eapply IHC1.
  - assert (RR : dy_level (dy_c_letm M C2_1 C2_2) = dy_level C2_2); eauto;
    rewrite <- RR; clear RR; eapply IHC1.
  - assert (RR : dy_level (dy_c_letm M0 C2_1 C2_2) = dy_level C2_2); eauto;
    rewrite <- RR; clear RR; eapply IHC1_2.
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

Inductive st_ctx :=
  | st_c_hole
  | st_c_lam (x : expr_id) (C : st_ctx)
  | st_c_lete (x : expr_id) (C : st_ctx)
  | st_c_letm (M : mod_id) (CM : st_ctx) (C : st_ctx)
.

Fixpoint st_level (C : st_ctx) : nat :=
  match C with
  | st_c_hole => 0
  | st_c_lam _ C'
  | st_c_lete _ C' => S (st_level C')
  | st_c_letm _ _ C' => st_level C'
  end.

Fixpoint st_ctx_M (C : st_ctx) (M : mod_id) :=
  match C with
  | st_c_hole => None
  | st_c_lam _ C'
  | st_c_lete _ C' => st_ctx_M C' M
  | st_c_letm M' CM' C' =>
    match st_ctx_M C' M with
    | Some CM => Some CM
    | None => if eq_mid M M' then Some CM' else None
    end
  end.

Fixpoint st_c_plugin (Cout : st_ctx) (Cin : st_ctx) :=
  match Cout with
  | st_c_hole => Cin
  | st_c_lam x C' => st_c_lam x (st_c_plugin C' Cin)
  | st_c_lete x C' => st_c_lete x (st_c_plugin C' Cin)
  | st_c_letm M' CM' C' => st_c_letm M' CM' (st_c_plugin C' Cin)
  end.

Lemma st_c_plugin_assoc : forall C1 C2 C3,
  st_c_plugin (st_c_plugin C1 C2) C3 =
  st_c_plugin C1 (st_c_plugin C2 C3). 
Proof.
  induction C1; eauto; 
  intros; simpl; try rewrite IHC1; eauto.
  rewrite IHC1_2. eauto.
Qed.

(* given a static context and an expression, 
   return the maximum level of the context
   that can be reached from here *)
Fixpoint level_expr (C : st_ctx) e :=
  match e with
  | e_var x => st_level C
  | e_lam x e' => level_expr (st_c_plugin C (st_c_lam x st_c_hole)) e'
  | e_app e1 e2 => Nat.max (level_expr C e1) (level_expr C e2)
  | e_link m e =>
    match level_mod C m with
    | (Some C_m, l) => Nat.max (level_expr C_m e) l
    | (None, l) => l
    end
  end

with level_mod (C : st_ctx) m :=
  match m with
  | m_empty => (Some C, st_level C)
  | m_var M =>
    match st_ctx_M C M with
    | None => (None, st_level C)
    | Some C_m => (Some C_m, Nat.max (st_level C) (st_level C_m))
    end
  | m_lete x e m' => 
    match level_expr C e with
    | l_e => 
      match level_mod (st_c_plugin C (st_c_lete x st_c_hole)) m' with
      | (context, l_m) => (context, Nat.max l_e l_m)
      end
    end
  | m_letm M m1 m2 =>
    match level_mod C m1 with
    | (Some C_m, l1) =>
      match level_mod (st_c_plugin C (st_c_letm M C_m st_c_hole)) m2 with
      | (context, l2) => (context, Nat.max l1 l2)
      end
    | (None, l1) => (None, l1)
    end
  end.

Lemma st_c_plugin_add_level :
  forall C1 C2, st_level (st_c_plugin C1 C2) = st_level C1 + st_level C2.
Proof.
  induction C1; induction C2; intros; simpl; eauto.
  - assert (RR : st_level (st_c_letm M C2_1 C2_2) = st_level C2_2); eauto.
    specialize (IHC1 (st_c_letm M C2_1 C2_2)).
    rewrite IHC1. rewrite RR. eauto.
  - assert (RR : st_level (st_c_letm M C2_1 C2_2) = st_level C2_2); eauto.
    specialize (IHC1 (st_c_letm M C2_1 C2_2)).
    rewrite IHC1. rewrite RR. eauto.
  - assert (RR : st_level (st_c_letm M0 C2_1 C2_2) = st_level C2_2); eauto.
    specialize (IHC1_2 (st_c_letm M0 C2_1 C2_2)).
    rewrite IHC1_2. rewrite RR. eauto.
Qed.

(* sanity check *)
Lemma level_increase : forall e C, st_level C <= level_expr C e.
Proof.
  apply (expr_ind_mut
    (fun e =>
      forall C, st_level C <= level_expr C e)
    (fun m =>
      forall C, 
      match level_mod C m with
        | (_, l) => st_level C <= l
      end)); 
  intros; simpl in *; try nia.
  induction C; intros; simpl in *; try nia.
  - assert (RR : st_level (st_c_lam x0 (st_c_plugin C (st_c_lam x st_c_hole))) =
            S (S(st_level C))); simpl; try rewrite st_c_plugin_add_level; simpl; try nia;
      assert (middle : S (S (st_level C)) <= level_expr (st_c_lam x0 (st_c_plugin C (st_c_lam x st_c_hole))) e);
      try rewrite <- RR; try apply H; try nia.
  - assert (RR : st_level (st_c_lete x0 (st_c_plugin C (st_c_lam x st_c_hole))) =
            S (S(st_level C))); simpl; try rewrite st_c_plugin_add_level; simpl; try nia;
    assert (middle : S (S (st_level C)) <= level_expr (st_c_lete x0 (st_c_plugin C (st_c_lam x st_c_hole))) e);
    try rewrite <- RR; try apply H; try nia.
  - assert (RR : st_level (st_c_letm M C1 (st_c_plugin C2 (st_c_lam x st_c_hole))) =
            (st_level C2) + 1); simpl; repeat try rewrite st_c_plugin_add_level; simpl; eauto; try nia.
    assert (middle : (st_level C2) + 1 <= level_expr (st_c_letm M C1 (st_c_plugin C2 (st_c_lam x st_c_hole))) e);
    try rewrite <- RR; try apply H; try nia.
  - specialize (H C). specialize (H0 C). nia.
  - remember (level_mod C m) as ol. destruct ol.
    destruct o; specialize (H C); rewrite <- Heqol in H; nia.
  - remember (st_ctx_M C M) as o. destruct o; nia.
  - remember (level_mod (st_c_plugin C (st_c_lete x st_c_hole)) m) as ol. destruct ol.
    specialize (H0 (st_c_plugin C (st_c_lete x st_c_hole))). rewrite <- Heqol in H0.
    rewrite st_c_plugin_add_level in H0. simpl in H0. nia.
  - remember (level_mod C m1) as ol1. destruct ol1.
    destruct o;
    try remember (level_mod (st_c_plugin C (st_c_letm M s st_c_hole)) m2) as ol2; try destruct ol2;
    try specialize (H C); eauto; try specialize (H0 (st_c_plugin C (st_c_letm M s st_c_hole)));
    rewrite <- Heqol1 in H; try rewrite <- Heqol2 in H0;
    try rewrite st_c_plugin_add_level in H0; try simpl in H0; try nia.
Qed.

Fixpoint dy_to_st C :=
  match C with
  | dy_c_hole => st_c_hole
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

Lemma st_ctx_M_plugin :
  forall Cout Cin M,
    st_ctx_M (st_c_plugin Cout Cin) M =
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
    st_ctx_M (st_c_plugin Cout0 Cin0) M0 = None -> st_ctx_M Cin0 M0 = None).
    { induction Cout0; intros; simpl; eauto. 
      simpl in H. apply IHCout0_2.
      destruct (st_ctx_M (st_c_plugin Cout0_2 Cin0) M0).
      inversion H. eauto. }
    specialize (IHCout1 Cin M0).
    rewrite (RR Cout2 Cin IHCout2) in IHCout1.
    destruct (eq_mid M0 M).
    eauto. eauto.
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
            | Some (Val v _ C') => Pe C' st v
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
            Pe (C_lam[|dy_c_lam x t dy_c_hole|])
              (ST ((dy_level C_lam ++ [t]) !-> (Val arg pf C_arg) ; mem) (update_t t)) e) ->
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
            Pm (C[|dy_c_lete x t dy_c_hole|])
              (ST ((dy_level C ++ [t]) !-> (Val v pf C_x) ; mem) (update_t t)) m) ->
    (forall C st M m1 m2,
            Pm C st (m_letm M m1 m2) -> Pm C st m1) ->
    (forall C st M m1 m2 C_M st_M,
            Pm C st (m_letm M m1 m2) ->
            Pm C_M st_M m_empty ->
            Pm (C[|dy_c_letm M C_M dy_c_hole|]) st_M m2) ->
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
      apply (IHere (C_lam [|dy_c_lam x t dy_c_hole|])
            (ST (dy_level C_lam ++ [t] !-> Val arg pf C_arg; mem)
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
      apply (IHerm (C_lam [|dy_c_lam x t dy_c_hole|])
            (ST (dy_level C_lam ++ [t] !-> Val arg pf C_arg; mem)
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
    + apply (IHmre (C [|dy_c_lete x t dy_c_hole|])
        (ST (dy_level C ++ [t] !-> Val v pf C_x; mem) (update_t t)) m
        C' st' e').
      eapply LETem. exact INIT.
      apply (IHere C st e C_x (ST mem t) v).
      eapply LETex. exact INIT. exact EVALxr. exact REACH.
    + apply (IHmre C st m1 C' st' e').
      eapply LETm1. exact INIT. exact REACH.
    + apply (IHmre (C [|dy_c_letm M C_M dy_c_hole|]) st_M m2 C' st' e').
      eapply LETm2. exact INIT.
      apply (IHmrm C st m1 C_M st_M m_empty).
      eapply LETm1. exact INIT. exact EVALM0. exact REACH.
  - intros. destruct REACH.
    + exact INIT.
    + specialize (MVAR C st M C_M ACCESS).
      apply MVAR. exact INIT.
    + apply (IHerm C st e C' st' m').
      eapply LETex. exact INIT. exact REACHe.
    + apply (IHmrm (C [|dy_c_lete x t dy_c_hole|])
        (ST (dy_level C ++ [t] !-> Val v pf C_x; mem) (update_t t)) m
        C' st' m').
      eapply LETem. exact INIT.
      apply (IHere C st e C_x (ST mem t) v).
      eapply LETex. exact INIT. exact EVALxr. exact REACH.
    + apply (IHmrm C st m1 C' st' m').
      eapply LETm1. exact INIT. exact REACH.
    + apply (IHmrm (C [|dy_c_letm M C_M dy_c_hole|]) st_M m2 C' st' m').
      eapply LETm2. exact INIT.
      apply (IHmrm C st m1 C_M st_M m_empty).
      eapply LETm1. exact INIT. exact REACH1. exact REACH2.
Qed.

Definition level_bound ub st :=
    match st with
    | ST mem _ =>
        (forall (addr : path),
          match mem addr with
          | Some (Val v _ C_v) => level_expr (dy_to_st C_v) v <= ub
          | None => True
          end)
    end.

Lemma Meval_then_level :
  forall C st m C_m st_m
         (EVAL : MevalR C st m C_m st_m),
        match level_mod (dy_to_st C) m with
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
    remember (level_mod (st_c_plugin (dy_to_st C) (st_c_lete x st_c_hole)) m) as lev.
    destruct lev. exact IHEVAL.
  - rewrite dy_to_st_plugin in IHEVAL2. simpl in IHEVAL2.
    destruct (level_mod (dy_to_st C) m1). destruct o; try apply IHEVAL1.
    rewrite <- IHEVAL1 in IHEVAL2.
    destruct (level_mod
              (st_c_plugin (dy_to_st C) (st_c_letm M s st_c_hole)) m2).
    exact IHEVAL2.
Qed.

Lemma ere_level_bound : 
    forall ub
           C st e
           C' st' e'
          (INIT : level_bound ub st /\ level_expr (dy_to_st C) e <= ub)
          (REACH : <e| C st e ~> C' st' e' |e>),
          level_bound ub st' /\ level_expr (dy_to_st C') e' <= ub.
Proof. 
  intros ub.
  apply (EreachE_ind_mut
    (fun C st e =>
          level_bound ub st /\ 
          level_expr (dy_to_st C) e <= ub)
    (fun C st m => 
          level_bound ub st /\ 
          let (o, l) := level_mod (dy_to_st C) m in l <= ub)).
  - intros C st e [mem expr].
    unfold level_bound in *. destruct st.
    intros addr. specialize (mem addr) as valtrue.
    remember (mem0 addr) as val.
    destruct val. destruct e0. split. exact mem. exact valtrue. eauto.
  - intros C st e1 e2 [mem expr].
    split. exact mem. remember (dy_to_st C) as st_C.
    simpl in expr. nia.
  - intros C st e1 e2 C_lam st_lam lam [memi expri] [memlam exprlam].
    split. exact memlam. remember (dy_to_st C) as st_C.
    simpl in expri. nia.
  - intros C st e1 e2 C_lam st_lam x e C_arg mem t arg pf
    [memi expri] [memlam exprlam] [memarg exprarg]. split.
    + unfold level_bound. unfold update_m. intro addr.
      destruct (eq_p addr (dy_level C_lam ++ [t])). exact exprarg.
      apply memarg.
    + rewrite dy_to_st_plugin. simpl. remember (dy_to_st C_lam) as st_C.
      simpl in exprlam. eauto.
  - intros C st m e [mem expr]. split. exact mem.
    simpl in expr. remember (level_mod (dy_to_st C) m) as lev.
    destruct lev. destruct o. nia. eauto.
  - intros C st m e C_m st_m [mem expr] meval [memm exprm]. split. exact memm.
    apply Meval_then_level in meval.
    simpl in expr. simpl in exprm. remember (level_mod (dy_to_st C) m) as lv.
    destruct lv; destruct o. rewrite <- meval. nia. inversion meval.
  - 
  Admitted.
