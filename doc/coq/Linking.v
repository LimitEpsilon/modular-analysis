From MODULAR Require Import Concrete.

Fixpoint inject_ctx Cout Cin :=
  match Cin with
  | ([||]) => Cout
  | dy_c_lam x t C' =>
    inject_ctx (Cout [|dy_c_lam x t ([||])|]) C'
  | dy_c_lete x t C' =>
    inject_ctx (Cout [|dy_c_lete x t ([||])|]) C'
  | dy_c_letm M CM C' => 
    inject_ctx (Cout [|dy_c_letm M (inject_ctx Cout CM) ([||])|]) C'
  end.