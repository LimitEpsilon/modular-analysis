From MODULAR Require Import Abstract.
From MODULAR Require Import Concrete.

Inductive sound (C : Concrete.dy_ctx) (mem : Concrete.path -> option Concrete.expr_value)
                (abs_C : Abstract.dy_ctx) (abs_mem : Abstract.path -> option (list Abstract.expr_value)) : Prop :=
| Sound_empty (EQ : Concrete.dy_to_st C = Abstract.dy_to_st abs_C)
              (EMPTY : mem = Concrete.empty_mem)
  : sound C mem abs_C abs_mem
.
| Sound (EQ : conc_to_abs_C (dy_to_st C) = Abstract.dy_to_st abs_C)
        (ACCESS : forall x,
                  match mem (addr_x C x) with
                  | None => True
                  | Some (Val v pf Cv) =>
                  exists vl abs_Cv, 
                    (Some vl = abs_mem (Abstract.addr_x abs_C x)) /\
                    (In (Abstract.Val v pf abs_Cv) vl) /\
                    (conc_to_abs_C (dy_to_st Cv) = Abstract.dy_to_st abs_Cv) /\

                    sound Cv mem abs_Cv abs_mem
                  end)
        (ACCESS' : forall conc_C, exists abs_C',
                   forall x,
                   (conc_to_abs_C (dy_to_st conc_C) = Abstract.dy_to_st abs_C') /\
                   match mem (addr_x conc_C x) with
                   | None => True
                   | Some (Val v pf Cv) =>
                    exists abs_Cv vl,
                      (Some vl = abs_mem (Abstract.addr_x abs_C' x)) /\
                      (In (Abstract.Val v pf abs_Cv) vl) /\
                      sound Cv mem abs_Cv abs_mem
                    end)
        : sound C mem abs_C abs_mem.

Fixpoint abs_st_sound C (mem : Concrete.path -> option expr_value)
                      abs_C (abs_mem : Abstract.path -> option (list Abstract.expr_value)) :=
  (conc_to_abs_C (dy_to_st C) = Abstract.dy_to_st abs_C) /\
  forall x,
    match mem (addr_x C x) with
    | None => True
    | Some (Val v pf Cv) =>
      exists vl abs_Cv, 
        (Some vl = abs_mem (Abstract.addr_x abs_C x)) /\
        (In (Abstract.Val v pf abs_Cv) vl) /\
        abs_st_sound Cv mem abs_Cv abs_mem
    end /\
  forall conc_C, exists abs_C',
    forall x,
    (conc_to_abs_C (dy_to_st conc_C) = Abstract.dy_to_st abs_C') /\
    match mem (addr_x conc_C x) with
    | None => True
    | Some (Val v pf Cv) =>
      exists abs_Cv vl,
        (Some vl = abs_mem (Abstract.addr_x abs_C' x)) /\
        (In (Abstract.Val v pf abs_Cv) vl) /\
        abs_st_sound Cv mem abs_Cv abs_mem
    end.

Lemma addr_x_eq : forall C abs_C x (EQ : conc_to_abs_C (dy_to_st C) = Abstract.dy_to_st abs_C),
  len_p (addr_x C x) = Abstract.len_p (Abstract.addr_x abs_C x).
Proof.
  induction C; induction abs_C; intros; simpl in *; try inversion EQ; eauto.
  - specialize (IHC abs_C x1 H1).
    remember (addr_x C x1) as c_addr.
    remember (Abstract.addr_x abs_C x1) as a_addr.
    destruct c_addr; destruct a_addr; simpl in *; try inversion IHC; eauto.
    unfold eq_eid, Abstract.eq_eid. destruct x1; destruct x0.
    destruct (x1 =? x0); eauto.
  - specialize (IHC abs_C x1 H1).
    remember (addr_x C x1) as c_addr.
    remember (Abstract.addr_x abs_C x1) as a_addr.
    destruct c_addr; destruct a_addr; simpl in *; try inversion IHC; eauto.
    unfold eq_eid, Abstract.eq_eid. destruct x1; destruct x0.
    destruct (x1 =? x0); eauto.
Qed.

Lemma eval_sound :
  forall C1 st1 e1 v2 st2
         (EVAL : EevalR C1 st1 e1 v2 st2),
         forall v pf C2 (VAL : Val v pf C2 = v2)
                mem1 t1 (STATE1 : st1 = ST mem1 t1)
                mem2 t2 (STATE2 : st2 = ST mem2 t2)
                abs_C1 abs_mem1 abs_t1 
                (SOUND : abs_st_sound C1 mem1 abs_C1 abs_mem1),
         exists abs_C2 abs_mem2 abs_t2,
         abs_st_sound C2 mem2 abs_C2 abs_mem2 /\
         Abstract.EevalR abs_C1 (Abstract.ST abs_mem1 abs_t1) e1
                         (Abstract.Val v pf abs_C2) (Abstract.ST abs_mem2 abs_t2).
Proof.
  apply (Concrete.EevalR_ind_mut
    (fun C1 st1 e1 v2 st2
         (EVAL : EevalR C1 st1 e1 v2 st2) =>
         forall v pf C2 (VAL : Val v pf C2 = v2)
                mem1 t1 (STATE1 : st1 = ST mem1 t1)
                mem2 t2 (STATE2 : st2 = ST mem2 t2)
                abs_C1 abs_mem1 abs_t1 
                (SOUND : abs_st_sound C1 mem1 abs_C1 abs_mem1),
         exists abs_C2 abs_mem2 abs_t2,
         abs_st_sound C2 mem2 abs_C2 abs_mem2 /\
         Abstract.EevalR abs_C1 (Abstract.ST abs_mem1 abs_t1) e1
                         (Abstract.Val v pf abs_C2) (Abstract.ST abs_mem2 abs_t2))
    (fun C1 st1 m1 C2 st2
         (EVAL : MevalR C1 st1 m1 C2 st2) =>
         forall mem1 t1 (STATE1 : st1 = ST mem1 t1)
                mem2 t2 (STATE2 : st2 = ST mem2 t2)
                abs_C1 abs_mem1 abs_t1 
                (SOUND : abs_st_sound C1 mem1 abs_C1 abs_mem1),
         exists abs_C2 abs_mem2 abs_t2,
         abs_st_sound C2 mem2 abs_C2 abs_mem2 /\
         Abstract.MevalR abs_C1 (Abstract.ST abs_mem1 abs_t1) m1
                         abs_C2 (Abstract.ST abs_mem2 abs_t2))). intros.
    - rewrite STATE1 in STATE2. inversion STATE2; subst.
      unfold abs_st_sound in *. destruct SOUND as [EQ MEM].
      specialize (MEM x). inversion STATE1; subst.
      rewrite <- ACCESS in MEM. destruct MEM as [EXISTS FORALL]. 
      destruct EXISTS as [vl [abs_Cv [ABS_ACCESS [EQ_Cv IN_Cv]]]].
      exists abs_Cv. exists abs_mem1. exists abs_t1.
      split; eauto. split; eauto. eapply Abstract.Eeval_var.
      eauto. remember (Abstract.addr_x abs_C1 x) as a_addr.
      destruct a_addr. specialize (addr_x_eq C abs_C1 x CTX).
      rewrite <- Heqa_addr. destruct (addr_x C x).
      specialize (ADDR eq_refl). inversion ADDR. simpl; intro contra; inversion contra.
      intro contra; inversion contra. rewrite 

Theorem soundness :
  forall e C' st' e'
         (REACH : <e| ([||]) (ST empty_mem 0) e ~> C' st' e' |e>),
         exists abs_st,
         <e| ([#||#]) (Abstract.ST empty_mem 0) e ~#> (conc_to_abs_C C') abs_st e' |e>.