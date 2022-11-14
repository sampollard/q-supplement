# Hierarchical Statecharts in Coq

## Building

Don't edit the Makefiles directly, instead change `_CoqProject`.  To
produce the Makefile run:

```
$ coq_makefile -f _CoqProject -o Makefile
```

## Understanding this Code

These proofs represent an idealized version of the state charts used in
the Q Framework. The best place to start to understand these is in
`coq/src/Semantics/ConfigEnv.v`, which has some explanation in the
comments.
