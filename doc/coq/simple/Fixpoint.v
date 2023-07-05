From Simple Require Import Abstract.

Generalizable Variables T.

(* step_eval C st e v st' n : 
    Given that \A{a} reached (C, st, e), the result (v, st') will be computed in n iterations *)
Inductive step_eval `{time T} (C : @dy_ctx T) (st : @state T)
    : tm -> dy_value -> state -> nat -> Prop :=
  | s_var_e 
    x v mem t addr
    (STATE : ST mem t = st)
    (ADDR : Some addr = addr_x C x)
    (ACCESS : In v (mem addr))
    : step_eval C st (e_var x) (EVal v) st 1
  | s_lam x e
    : step_eval C st (e_lam x e) (EVal (Closure x e C)) st 1
  | s_app 
    e1 e2 x e C_lam st_lam step1
    arg mem t step2
    v st_v step3
    (FN : step_eval C st e1 (EVal (Closure x e C_lam)) st_lam step1)
    (ARG : step_eval C st_lam e2 (EVal arg) (ST mem t) step2)
    (BODY : step_eval (C_lam [|dy_c_lam x t ([||])|])
                      (ST (t !#-> arg ; mem) (tick C (ST mem t) x arg))
                      e (EVal v) st_v step3)
    : step_eval C st (e_app e1 e2) (EVal v) st_v (4 + step1 + step2 + step3)
  | s_link
    m e C_m st_m step1 v st_v step2
    (MOD : step_eval C st m (MVal C_m) st_m step1)
    (LINK : step_eval C_m st_m e v st_v step2)
    : step_eval C st (e_link m e) v st_v (3 + step1 + step2)
  | s_empty
    : step_eval C st m_empty (MVal C) st 1
  | s_var_m
    M C_M (ACCESS : Some C_M = ctx_M C M)
    : step_eval C st (m_var M) (MVal C_M) st 1
  | s_lete
    x e v mem t step1
    m C_m st_m step2
    (EVALe : step_eval C st e (EVal v) (ST mem t) step1)
    (EVALm : step_eval (C [|dy_c_lete x t ([||])|])
                       (ST (t !#-> v ; mem) (tick C (ST mem t) x v))
                       m (MVal C_m) st_m step2)
    : step_eval C st (m_lete x e m) (MVal C_m) st_m (3 + step1 + step2)
  | s_letm
    M m' C' st' step1
    m'' C'' st'' step2
    (EVALm' : step_eval C st m' (MVal C') st' step1)
    (EVALm'' : step_eval (C [|dy_c_letm M C' ([||])|]) st'
                         m'' (MVal C'') st'' step2)
    : step_eval C st (m_letm M m' m'') (MVal C'') st'' (3 + step1 + step2)
.

Inductive step_one `{time T} (C : @dy_ctx T) (st : @state T)
    : tm -> dy_ctx -> state -> tm -> nat -> Prop :=
  | s_appl 
    e1 e2
    : step_one C st (e_app e1 e2) C st e1 1
  | s_appr
    e1 e2 x e C_lam st_lam step1
    (FN : step_eval C st e1 (EVal (Closure x e C_lam)) st_lam step1)
    : step_one C st (e_app e1 e2) C st_lam e2 (2 + step1)
  | s_appbody
    e1 e2 x e C_lam st_lam step1
    arg mem t step2
    (FN : step_eval C st e1 (EVal (Closure x e C_lam)) st_lam step1)
    (ARG : step_eval C st_lam e2 (EVal arg) (ST mem t) step2)
    : step_one C st (e_app e1 e2) 
               (C_lam [|dy_c_lam x t ([||])|])
               (ST (t !#-> arg ; mem) (tick C (ST mem t) x arg))
               e (3 + step1 + step2)
  | s_linkl
    m e
    : step_one C st (e_link m e) C st m 1
  | s_linkr
    m e C_m st_m step1
    (MOD : step_eval C st m (MVal C_m) st_m step1)
    : step_one C st (e_link m e) C_m st_m e (2 + step1)
  | s_letel
    x e m
    : step_one C st (m_lete x e m) C st e 1
  | s_leter
    x e m v mem t step1
    (EVALe : step_eval C st e (EVal v) (ST mem t) step1)
    : step_one C st (m_lete x e m)
               (C [|dy_c_lete x t ([||])|])
               (ST (t !#-> v ; mem) (tick C (ST mem t) x v))
               m (2 + step1)
  | s_letml
    M m' m''
    : step_one C st (m_letm M m' m'') C st m' 1
  | s_letmr
    M m' m'' C' st' step1
    (EVALm' : step_eval C st m' (MVal C') st' step1)
    : step_one C st (m_letm M m' m'') 
               (C [|dy_c_letm M C' ([||])|]) st' m'' (2 + step1)
.

Inductive step_multi `{time T} (C : @dy_ctx T) (st : @state T)
    : tm -> dy_ctx -> state -> tm -> nat -> Prop :=
  | s_refl e : step_multi C st e C st e 0
  | s_trans e C' st' e' step1 C'' st'' e'' step2
            (STEP1 : step_one C st e C' st' e' step1)
            (STEP2 : step_multi C' st' e' C'' st'' e'' step2)
    : step_multi C st e C'' st'' e'' (step1 + step2)
.

Lemma step_bound `{time T} n :
  forall (C : @dy_ctx T) st e v st_v 
    (EVAL : step_eval C st e v st_v (S (S n))),
    exists p q C' st' e',
      step_one C st e C' st' e' p /\
      step_eval C' st' e' v st_v q /\
      p + q = S n.
Proof.
  induction n; intros; inversion EVAL.
  - exists (3 + step1 + step2). exists step3.
    exists (C_lam [|dy_c_lam x t ([||])|]).
    exists (ST (t !#-> arg; mem) (tick C (ST mem t) x arg)).
    exists e0.
    split. eapply s_appbody; eauto.
    split; eauto.
  - exists (2 + step1). exists step2.
    exists C_m. exists st_m. exists e0.
    split. eapply s_linkr; eauto.
    split; eauto.
  - exists (2 + step1). exists step2.
    exists (C [|dy_c_lete x t ([||])|]).
    exists (ST (t !#-> v0; mem) (tick C (ST mem t) x v0)).
    exists m.
    split. eapply s_leter; eauto.
    split; eauto.
  - exists (2 + step1). exists step2.
    exists (C [|dy_c_letm M C' ([||])|]). exists st'. exists m''.
    split. eapply s_letmr; eauto.
    split; eauto.
Qed.
