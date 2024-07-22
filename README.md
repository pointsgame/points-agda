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

The repository also includes both compile-time and runtime tests. While the
compile-time tests are executed at the type level, they can be quite slow, with
even simple tests requiring several hours to execute. This is why runtime tests
are also included to provide an additional layer of verification.
