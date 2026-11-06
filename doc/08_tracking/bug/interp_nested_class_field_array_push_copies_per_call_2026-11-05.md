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

## 2026-11-06 round 8: FIXED
`try_place_mutation_in_place` now resolves a pure field chain whose holders are all `ClassInstance`s and mutates the array under the innermost instance lock (`class_hop_leaf`). 20k pushes through three class hops: 2923 ms -> 288 ms. Spec: test/01_unit/compiler/interpreter/nested_class_hop_array_push_spec.spl.
