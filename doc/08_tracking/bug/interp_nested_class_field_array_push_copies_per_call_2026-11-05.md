# Interpreter: nested class-field array push copies the array per call

- **Filed:** 2026-11-05 (libbug coordinator, from PR #6727 review)
- **Status:** open (P2 perf)
- **Symptom:** after #6727, `self.store.items.push(x)` from another class's `me` method is
  correct, but when the array sits behind two class-instance hops the tree-walk
  interpreter reads it, mutates a copy and writes it back via `write_place`, so each
  push is O(len) and a push loop is O(n^2).
- **Where:** `src/compiler_rust/compiler/src/interpreter/place.rs` (`projections_live` /
  `write_place` path).
- **Fix direction:** mutate in place under the class-instance lock, as #6646 did for a
  single-hop `self.parts.push` (5.7 s -> 0.37 s per 20k ops).
- **Repro:** `test/01_unit/compiler/interpreter/nested_class_field_array_mutation_spec.spl`
  (correctness); time a 20k-push loop through two class hops.

## 2026-11-06 NOT REPRODUCIBLE on current seed
Two- and three-hop `self.a.b.items.push(x)` loops (interpret lane): 20k pushes 0.07-0.11 s, 40k 0.17 s, 80k 0.17 s on simple-ref and a fresh build: linear, not O(n^2). Candidate to close; re-open with a repro that is superlinear.
