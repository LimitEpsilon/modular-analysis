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

Definition eq_eid id1 id2 :=
  match id1, id2 with
  | eid x1, eid x2 => x1 =? x2
  end.

Definition eq_mid id1 id2 :=
  match id1, id2 with
  | mid M1, mid M2 => M1 =? M2
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
              arg e_mem_a m_mem_a t_a
              v st_v
              (FN : EevalR p (C [|c_app_left c_hole e2|]) st
                           e1 (Closure x e_lam p_lam C_lam) st_lam)
              (ARG : EevalR p (C [|c_app_right e1 c_hole|]) st_lam
                            e2 arg (ST e_mem_a m_mem_a t_a))
              (BODY : EevalR (t_a :: p_lam) (C_lam [|c_lam x c_hole|])
                             (ST ((t_a :: p_lam) !-> arg ; e_mem_a) m_mem_a (update_t t_a))
                              e_lam v st_v)
    : EevalR p C st (e_app e1 e2) v st_v
  | Eeval_link m e p_m C_m st_m 
               v st_v
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

(* Reachability relation *)
Inductive EreachE (p : path) (C : ctx) (st : state)
    : expr_tm -> path -> ctx -> state -> expr_tm -> Prop :=
  | ere_refl e 
    : EreachE p C st e 
              p C st e
  | ermre_trans e p_m C_m st_m m
                p' C' st' e'
              (REACHm : EreachM p C st e
                                p_m C_m st_m m)
              (REACHe' : MreachE p_m C_m st_m m
                                 p' C' st' e')
    : EreachE p C st e
              p' C' st' e'
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
                 (REACHb : EreachE (t_a :: p_lam) (C_lam[|c_lam x c_hole|]) (ST ((t_a :: p_lam) !-> arg ; e_mem) m_mem (update_t t_a)) e_lam
                                    p' C' st' e')
    : EreachE p C st (e_app e1 e2)
              p' C' st' e'
  | ere_link m e p_m C_m st_m p' C' st' e'
               (MOD : MevalR p C st m (Mod p_m C_m) st_m)
               (REACHe : EreachE p_m C_m st_m e
                                 p' C' st' e')
    : EreachE p C st (e_link m e)
              p' C' st' e'

with EreachM (p : path) (C : ctx) (st : state)
    : expr_tm -> path -> ctx -> state -> mod_tm -> Prop :=
  | erm_link m e
    : EreachM p C st (e_link m e)
              p C st m
  | ermrm_trans e p_m C_m st_m m p' C' st' m'
                (REACHm : EreachM p C st e
                                  p_m C_m st_m m)
                (REACHm' : MreachM p_m C_m st_m m
                                   p' C' st' m')
    : EreachM p C st e
              p' C' st' m'

with MreachE (p : path) (C : ctx) (st : state)
    : mod_tm -> path -> ctx -> state -> expr_tm -> Prop :=
  | mre_lete x e m
    : MreachE p C st (m_lete x e m)
              p C st e
  | mrere_trans m p_e C_e st_e e p' C' st' e'
                (REACHe : MreachE p C st m
                                  p_e C_e st_e e)
                (REACHe' : EreachE p_e C_e st_e e
                                   p' C' st' e')
    : MreachE p C st m
              p' C' st' e'

with MreachM (p : path) (C : ctx) (st : state)
    : mod_tm -> path -> ctx -> state -> mod_tm -> Prop :=
  | mrm_refl m
    : MreachM p C st m
              p C st m
  | mrerm_trans m p_e C_e st_e e
                p' C' st' m'
              (REACHe : MreachE p C st m
                                p_e C_e st_e e)
              (REACHm' : EreachM p_e C_e st_e e
                                 p' C' st' m')
    : MreachM p C st m
              p C' st' m'
  | mrm_lete x e m v e_mem m_mem t_e
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
             (EVALm1 : MevalR p C st m1 v (ST e_mem m_mem t_m))
             (REACHm : MreachM (t_m :: p) (C[|c_letm M m1 c_hole|]) (ST e_mem ((t_m :: p) !-> v ; m_mem) (update_t t_m)) m2
                                p' C' st' m' )
    : MreachM p C st (m_letm M m1 m2)
              p' C' st' m'
.

(* Tactics from Gil Hur, from his Software Foundations Class *)

Ltac on_last_hyp tac :=
  match goal with [ H : _ |- _ ] => first [ tac H | fail 1 ] end.

(* revert until id *)
Ltac revert_until id :=
  on_last_hyp
    ltac:(fun id' =>
            match id' with
            | id => idtac
            | _ => revert id' ; revert_until id
            end).

(* most general induction *)
Ltac ginduction H :=
  move H at top; revert_until H; induction H.

Lemma ere_trans : forall e1 p1 C1 st1
                         e2 p2 C2 st2
                         e3 p3 C3 st3
                        (REACH1 : EreachE p1 C1 st1 e1
                                          p2 C2 st2 e2)
                        (REACH2 : EreachE p2 C2 st2 e2
                                          p3 C3 st3 e3),
                        EreachE p1 C1 st1 e1
                                p3 C3 st3 e3.
Proof.
  intros. 
  ginduction REACH1; eauto using EreachE, EreachM, MreachE, MreachM.
Qed.

Lemma c_plugin_assoc : forall C1 C2 C3, C1[| C2[| C3 |] |] = ((C1[|C2|])[|C3|]).
Proof.
  induction C1; eauto using ctx; 
  intros; simpl; try rewrite IHC1; eauto.
Qed.