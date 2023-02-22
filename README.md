# Lambda Interpreter

A simple interpreter for a toy language `L` that is defined as:
```shell
<e> ::= <id>                  ;; identifer (C-style)
      | \ <id> . <e>          ;; abstraction
      | <e> <e>               :: application
      | let <id> = <e> in <e> :: let expression
```

An example program is presented in `test/factorial.l`.

The implementation is based on a notion of environments that do not map ids to values, but rather to "continuations".

To view the environment after `n` iterations, do:
```shell
./_build/default/bin/main.exe -step <n> <input_file>
```
