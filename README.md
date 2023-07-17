# Modular Analysis

A static analyzer for a model language `L` that is defined as:
```shell
<e> ::= <consonant-id>          ;; expression identifer (C-style)
      | \ <id> . <e>            ;; abstraction
      | <e> <e>                 ;; application
      | <e> ! <e>               ;; linking
      | ε                       ;; empty module
      | <capital-id>            ;; module identifier
      | let <expr> = <e> in <e> ;; expression binding
      | let <mod> = <e> in <e>  ;; module binding
```

To execute, run:
```shell
dune clean && dune build
./run <input_file>
```
