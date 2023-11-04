From Signature Require Export Syntax.

Generalizable Variables T.

Class time `{TotalOrder T} :=
{
  tick : dy_ctx T -> memory T -> T -> ID -> expr_value T -> T;
  (* functional extensionality *)
  tick_ext : forall C m m' t x v (EQ : same m m'), tick C m t x v = tick C m' t x v;
  (* fresh timestamp *)
  tick_lt : forall C mem t x v, t << tick C mem t x v
}.

Inductive step `{time T} : (config T) -> (config T) -> Prop :=
  | ExprID x C m t v addr
    (ADDR : addr_x C x = Some addr)
    (ACCESS : read m addr = Some v)
    : step (Cf (e_var x) C m t) (Rs (EVal v) m t)

  | Fn x e C m t
    : step (Cf (e_lam x e) C m t) (Rs (EVal (Fun x e C)) m t)
  
  | EAppL e1 e2 C m t
    : step (Cf (e_app e1 e2) C m t) (Cf e1 C m t)

  | FnEAppR e1 e2 C m t x e C_f m_f t_f
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    : step (Cf (e_app e1 e2) C m t) (Cf e2 C m_f t_f)

  | FtEAppR e1 e2 C m t M s_M e C_f m_f t_f
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    : step (Cf (e_app e1 e2) C m t) (Cf e2 C m_f t_f)
  
  | FnEAppBody e1 e2 C m t x e C_f m_f t_f v m_a t_a
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    : step (Cf (e_app e1 e2) C m t) (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v))

  | FtEAppBody e1 e2 C m t M s_M e C_f m_f t_f C_v m_a t_a C_M
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    : step (Cf (e_app e1 e2) C m t) (Cf e (dy_bindm M C_M C_f) m_a t_a)
  
  | FnEApp e1 e2 C m t x e C_f m_f t_f v m_a t_a v' m' t'
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    (BODY : step (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v)) (Rs (EVal v') m' t'))
    : step (Cf (e_app e1 e2) C m t) (Rs (EVal v') m' t')
  
  | FtEApp e1 e2 C m t M s_M e C_f m_f t_f C_v m_a t_a C_M v' m' t'
    (FN : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    (BODY : step (Cf e (dy_bindm M C_M C_f) m_a t_a) (Rs (EVal v') m' t'))
    : step (Cf (e_app e1 e2) C m t) (Rs (EVal v') m' t')
  
  | LinkL e1 e2 C m t
    : step (Cf (e_link e1 e2) C m t) (Cf e1 C m t)
  
  | LinkR e1 e2 C m t C' m' t'
    (MOD : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    : step (Cf (e_link e1 e2) C m t) (Cf e2 C' m' t')
  
  | Link e1 e2 C m t C' m' t' V m'' t''
    (MOD : step (Cf e1 C m t) (Rs (MVal C') m' t'))
    (LINK : step (Cf e2 C' m' t') (Rs V m'' t''))
    : step (Cf (e_link e1 e2) C m t) (Rs V m'' t'')
  
  | Empty C m t
    : step (Cf m_empty C m t) (Rs (MVal C) m t)
  
  | ModID M C m t C_M
    (ACCESS : ctx_M C M = Some C_M)
    : step (Cf (m_var M) C m t) (Rs (MVal (C_M[|C|])) m t)
  
  | Ft M e s_M C m t
    : step (Cf (m_lam M s_M e) C m t) (Rs (EVal (Func M s_M e C)) m t)

  | MAppL e1 e2 s C m t
    : step (Cf (m_app e1 e2 s) C m t) (Cf e1 C m t)

  | FnMAppR e1 e2 s C m t x e C_f m_f t_f
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e2 C m_f t_f)

  | FtMAppR e1 e2 s C m t M s_M e C_f m_f t_f
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e2 C m_f t_f)
  
  | FnMAppBody e1 e2 s C m t x e C_f m_f t_f v m_a t_a
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    : step (Cf (m_app e1 e2 s) C m t) (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v))

  | FtMAppBody e1 e2 s C m t M s_M e C_f m_f t_f C_v m_a t_a C_M
    (FT : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    : step (Cf (m_app e1 e2 s) C m t) (Cf e (dy_bindm M C_M C_f) m_a t_a)
  
  | FnMApp e1 e2 s C m t x e C_f m_f t_f v m_a t_a C' m' t' C_s
    (FN : step (Cf e1 C m t) (Rs (EVal (Fun x e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (EVal v) m_a t_a))
    (BODY : step (Cf e (dy_binde x (tick C m_a t_a x v) C_f) ((tick C m_a t_a x v) !-> v; m_a) (tick C m_a t_a x v)) (Rs (MVal C') m' t'))
    (PROJs : project C' s = Some C_s)
    : step (Cf (m_app e1 e2 s) C m t) (Rs (MVal (C_s[|C|])) m' t')
  
  | FtMApp e1 e2 s C m t M s_M e C_f m_f t_f C_v m_a t_a C_M C' m' t' C_s
    (FN : step (Cf e1 C m t) (Rs (EVal (Func M s_M e C_f)) m_f t_f))
    (ARG : step (Cf e2 C m_f t_f) (Rs (MVal C_v) m_a t_a))
    (PROJ : project C_v s_M = Some C_M)
    (BODY : step (Cf e (dy_bindm M C_M C_f) m_a t_a) (Rs (MVal C') m' t'))
    (PROJs : project C' s = Some C_s)
    : step (Cf (m_app e1 e2 s) C m t) (Rs (MVal (C_s[|C|])) m' t')
.

#[export] Hint Constructors step : core.

Inductive multi_step `{time T} : (@config T) -> (@config T) -> Prop :=
  | Refl cf : multi_step cf cf
  | Trans cf cf' cf''
    (REACHl : step cf cf')
    (REACHr : multi_step cf' cf'')
    : multi_step cf cf''
.

#[export] Hint Constructors multi_step : core.

Notation "'{|' ll '~>' rr '|}'" := 
  (step ll rr) 
  (at level 10, ll at next level, rr at next level).

Notation "'{|' ll '~>*' rr '|}'" := 
  (multi_step ll rr) 
  (at level 10, ll at next level, rr at next level).
