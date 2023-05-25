From MODULAR Require Import Abstract.
From MODULAR Require Import Concrete.

Theorem soundness :
  forall e C' st' e'
         (REACH : <e| ([||]) (ST empty_mem 0) e ~> C' st' e' |e>),
         exists abs_C abs_st,
         <e| ([#||#]) (Abstract.ST Abstract.empty_mem true) e ~#> abs_C abs_st e' |e>.