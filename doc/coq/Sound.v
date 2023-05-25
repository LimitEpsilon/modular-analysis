From MODULAR Require Export Abstract.
From MODULAR Require Export Concrete.
Require Export Coq.Logic.FunctionalExtensionality.

Fixpoint list_to_mem l :=
  match l with
  | [] => Concrete.empty_mem
  | (addr, (Val v pf Cv)) :: tl => 
    (addr !-> (Val v pf Cv) ; (list_to_mem tl))
  end.

Fixpoint increasing (l : list (prod path expr_value)) :=
  match l with
  | [] => True
  | [(t :: _, _)] => True
  | (t1 :: _, _) :: 
    (t2 :: _, _) :: tl => (t1 > t2) /\ increasing tl
  | _ => False
  end.

Definition finite_mem mem :=
  exists l, mem = list_to_mem l /\ increasing l.

Fixpoint sound_addr C mem_list abs_C abs_mem : Prop :=
  Concrete.dy_to_st C = Abstract.dy_to_st abs_C /\
  forall x,
    match mem_list with
    | [] => True
    | (addr, Val v pf Cv) :: tl =>
      if eq_p addr (addr_x C x) 
      then exists abs_Cv, 
        (In (Abstract.Val v pf abs_Cv) (abs_mem (Abstract.addr_x abs_C x))) /\
        sound_addr Cv tl abs_Cv abs_mem
      else sound_addr C tl abs_C abs_mem
    end.

Theorem soundness :
  forall e C' st' e'
         (REACH : <e| ([||]) (ST empty_mem 0) e ~> C' st' e' |e>),
         exists abs_C abs_st,
         <e| ([#||#]) (Abstract.ST Abstract.empty_mem true) e ~#> abs_C abs_st e' |e>.