# Seed value join: Any / Option / disagreeing arms produce wrong values (2026-11-27)

Sections (A) and (C) are owned by lanes d29-c and d29-e; (B) below is lane d29-d.

## (B) Option-wrapped weak-empty arms

Repro (seed r, `simple-local-20261127r.exe`): `val r = if c: Some([]) else: Some(xs)`
(or the `match` form) with `xs: [f64]`, then `match r: case Some(v): v[0] + 0.25`
returned `0.0` for BOTH arms (expected `-2.0`/`1.75` with a `len() > 0` guard).

Root cause, two parts in `src/compiler_rust/compiler/src/hir/lower/expr/`:

1. `calls.rs`: `Some(x)` only kept a typed `Option<T>` for Function/Struct
   payloads; an array/dict payload was erased to `ANY`, so the join type and the
   `v` binding were `ANY` and `v[0]` was a dynamic index over raw f64 storage
   (garbage). This also broke the non-empty `Some(ys)` vs `Some(xs)` join and a
   plain `val r = Some(xs); match r:` read.
2. `control.rs`: the PR #12202 weak-empty rule (`weak_expr`, `same_collection_kind`,
   `ast_expr_tail_is_array_repeat`) did not look through `Some(...)`, so even once
   typed, `Some([])` (`Option<[i32]>`) won the join over `Some(xs)`.

Fix: `Some(<array|dict>)` now types as `Option<payload>`; `weak_expr` treats
`Some(e)` as `e`; `same_collection_kind` compares Option payloads;
`ast_expr_tail_is_array_repeat` sees through `Some(..)` so `Some([x; 0])` is never
weak. Tests: `hir/lower/tests/conditional_empty_array_tests.rs`
(`option_wrapped_*`).

Not covered here (siblings): `if c: Some(xs) else: None` / `None` first, and
other Any-typed payload reads.

Verification (seed r vs v = r + this fix; 77 probes from rv3 a/b/c + mt/mt2): 6
probe files differ. Fixed: `p_opt` o1/o2 (`0.0 0.0` -> `-2.0 1.75` / `1.75 -2.0`),
`q_s5` and the `n3` tail lines (`0.0 0.0` -> `-2.0 1.75`). The remaining diffs
(`n1` line 24, `n3` line 4, `q_s2` line 2, `p_any` y3/y4/y7) are garbage values on
BOTH seeds (differ run to run: uninitialised/address-like reads) and stay wrong
(sibling lanes). No probe that was correct on r changed on v. Specs on v:
storage_view_v1 34/34, parsers_json_core 101/101, match_empty_array_bug 10/10.

### (B) revision after review (c41c12ff143 blocked)

The first fix typed `Some([])` as `Option<[i32;0]>` (the empty-array default became
authoritative), so an untyped `Some([])` later replaced or filled read garbage (probes
rvd a02/a03/a18/b02/b03/b05/c04). Revised: `Some(<weak empty literal>)` is NOT typed
(it keeps the pre-existing erased type, exactly as before the change; `Some([x; 0])`
still types), only `Some(<concrete array|dict>)` becomes `Option<T>`. The join treats
the erased weak `Some([])` as weak and adopts the concrete sibling's Option type
(`same_collection_kind` now looks through Option only, never Result).
`hir_types_compatible` admits pointer-form `T?` vs `Option<T>` (no more "declared
return type mismatch admitted" for `-> [T]?`). Dict sibling (a15) uses the same path.
Tests: `some_empty_array_stays_weak_when_later_replaced_or_filled`,
`option_wrapped_empty_dict_defers_and_option_never_adopts_result`.
