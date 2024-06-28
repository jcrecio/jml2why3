# Jml2Why3 - a prototype tool to convert Java/JML to Why3

Jml2Why3 is a prototype tool to convert Java programs with JML annotations to programs in
the Why3 language, in order to use Why3's verification generation and its interaction with
automatic provers to verify properties of the Java/JML program.

## Installation

```
$ opam --version 
2.0.2

$ opam switch 4.08.0  # at least 4.08
$ eval $(opam env)
$ opam install --deps-only .
$ make
```

## Test

```shell
$ why3 config --detect
At least Alt-Ergo (2.3.0), CVC4 (1.6), Z3 (4.6.0).
$ make test
```

## Read report

The command `make -C report` renders the report about Jml2Why3 in <report/main.pdf>.
