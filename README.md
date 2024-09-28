# Points Game Field Implementation in Agda

This repository contains an implementation of the game of Points in Agda, a
dependently-typed programming language.

The implementation features advanced compile time checks, specifically the
verification that every next point in a calculated surrounding chain is
adjacent to the previous one, and that the first point is adjacent to the last one.

Additionally, it allows to put points only on empty space within the field. The
point placement function takes coordinates as finite numbers bounded by the size
of the field and requires a proof that putting is allowed.

Some functions use the TERMINATING pragma to bypass Agda's termination checking.

## Benchmark

Build with:

```sh
agda --ghc-flag=-O2 --compile src/Bench.agda
```

Run with:

```sh
time ./src/Bench 39 32 5 7
```
