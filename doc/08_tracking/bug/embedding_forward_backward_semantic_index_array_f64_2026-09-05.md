# Embedding.forward/backward undrivable on the interpreter: "cannot index array with type f64"

**Date:** 2026-09-05
**Found by:** sspec score-80 wave 3 (modernizing `test/01_unit/lib/gc_async_mut/embedding_spec.spl`)

## Symptom

Any call to `Embedding.forward` or `Embedding.backward`
(`src/lib/gc_async_mut/embedding.spl`) from a spec running on the fresh Sep-5
seed (`src/compiler_rust/target/bootstrap/simple run`) raises:

```
semantic: cannot index array with type f64
```

raised inside the product body under nested interpretation. The old spec never
called these methods — its "forward" scenarios were self-referential literal
tautologies — so the defect was invisible until the modernization rewrote them
onto the drivable surface (constructor/layout/gradient-slot/index-log/
parameters/modes + datasets). Several scenario names were renamed to state
which contract is pinned instead.

## Reproduce

```simple
use std.gc_async_mut.embedding.{Embedding}
fn main():
    val e = Embedding(num_embeddings: 4, embedding_dim: 3)   # constructor works
    val out = e.forward([0, 1])                               # semantic error here
```

## Suspects

Index expression typing inside a nested interpreted call: the indices
parameter (typed `[i64]` at the API surface) arrives as f64-tagged values at
the array index site, or the indices array is being confused with the f64
weight matrix. Same class as previously filed seed typing divergences (see
`doc/08_tracking/bug/seed_noarg_split_and_implicit_return_diverge_2026-09-05.md`
for the divergences found the same day).

## Unblock condition

`Embedding.forward(indices)` and `.backward(...)` execute on the interpreter
and the two renamed scenarios in
`test/01_unit/lib/gc_async_mut/embedding_spec.spl` (and its `test/unit` twin)
can be pointed back at them.
