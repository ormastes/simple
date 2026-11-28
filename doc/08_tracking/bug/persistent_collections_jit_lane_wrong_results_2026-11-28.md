# Persistent collections under the JIT lane: segfault and wrong results

- **Status:** OPEN
- **Component:** `src/lib/nogc_async_immut/persistent_{list,map,set}`
- **Found:** 2026-11-28, S8-K review (`SIMPLE_JIT_SPEC_ENTRY=1`, or code under `fn main`)

## Symptom

- PersistentList segfaults (rc=139) under `fn main`. On the pre-S8-K tree the
  same program ran but produced silently wrong results.
- PersistentMap and PersistentSet give wrong results identically on the old and
  new node representations (not introduced by the typed nodes).
- `persistent_collections_native_spec` goes OK -> ERROR under
  `SIMPLE_JIT_SPEC_ENTRY=1`.

## Next step

Reproduce with the S8-K probes, bisect the JIT lowering of struct-with-Option
fields (`ConsCell<T>.tail`, `HamtNode`), and confirm whether the old silent
wrong answer and the new crash share a root cause.
