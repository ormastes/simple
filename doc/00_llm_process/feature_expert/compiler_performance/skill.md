# Compiler Performance Expert

## Scope

Own optimizer activation truth, performance/memory diagnostics, shared MIR facts,
CollectionPlan decisions, symbolic summaries, and profile correlation.

## Non-negotiable rules

- Inspect requested and effective pipelines separately.
- Never activate a dormant pass mechanically.
- Treat `Unknown` alias, effect, escape, trip-count, and lifetime facts as rejection.
- Use source warnings for likely application mistakes and remarks for compiler decisions.
- Profiles affect priority and profitability only, never transformation legality.
- Preserve order, errors, traps, numeric semantics, ownership, destruction timing, and ABI.
- Reuse `PerfFacts`; do not add private CFG/loop/alias scans to a pass.
- Require positive/negative sentinels, verification, idempotence, and differential evidence.
- Run only an admitted pure-Simple binary and retain its stage/hash/provenance.

## Primary references

- `doc/01_research/local/simple_compiler_performance_memory_efficiency_audit.md`
- `doc/04_architecture/simple_compiler_performance_memory_efficiency.md`
- `doc/05_design/simple_compiler_performance_memory_efficiency.md`
- `doc/07_guide/compiler/performance_diagnostics.md`
- `doc/03_plan/sys_test/simple_compiler_performance_memory_efficiency.md`

## Review questions

1. Is the pass operational status honest?
2. What exact facts prove legality, and how are they invalidated?
3. Is the opportunity a lint, transform, remark, deep analysis, or profile finding?
4. Are uncertainty and rejection reasons serialized?
5. What positive and adversarial witnesses prove behavior?
6. What before/after compile-time, runtime, allocation, copy, and RSS evidence exists?

## Dataframe way — LLM-safe collections (2026-09-18)

Plan: `doc/03_plan/compiler/collection_planner/adaptive_collections_typed_query_rc1_plan_2026-09-18.md`.
Guide: `doc/07_guide/language/collections/dataframe_way.md`.

- **Library:** `std.common.frame` holds `key_set`, `index_by`, `distinct_by`,
  `group_by_key`, `count_by`, `semi_join`, `anti_join` and `top_k_by`.
  `std.common.collection_profile` is the opt-in profiler whose `coll_advice`
  recommends a switch.
- **Lint:** COLL002, COLL015, COLL016, COLL020, COLL021 and COLL022. COLL009–018
  are reserved with fixed meanings. Only COLL002 and COLL020 carry `Certain`
  fixes, and only when textual preconditions are proven. `simple fix <file>`
  applies them. `simple lint --fix` needs the seed fix `1f570918de4` to be
  deployed first: before that change, `filter_internal_flags` stripped `--fix*`
  for every command.
- **Trap: two `std.df` copies.** Which copy `use std.df` loads depends on the importing family context
  (the test runner loaded `nogc_async_mut/df`, although `resolution.spl` tier order lists `nogc_sync_mut` first). Edit both, and import the
  family explicitly in specs. Otherwise the spec passes on the unfixed copy.
- **Trap: Dict keys compare bitwise.** For `f64`, `-0.0 != 0.0` and
  `NaN == NaN`. Fold `-0.0` and bypass NaN to keep `==` semantics.
- **Trap: silent Dict misses.** A missed `d[k]` returns `0` silently. Always
  call `contains_key` first. Keep Dicts local and never call `.set()` or
  `.get()`.
- **Trap: seed method calls.** On the seed, `impl` method calls are
  superlinear in receiver size. See
  `doc/08_tracking/bug/seed_method_dispatch_superlinear_series_2026-09-18.md`.
  An O(n) body can still time as O(n²) when called as a method.
- **Measured:** `std.df` `unique_f64` with n=25000 went from TIMEOUT (120 s) to
  2.2 s. The compiler SCC scheduler, HIR demand reachability and action-graph
  BFS moved to a local Dict index. `99.loader` and `95.interp` were already
  Dict-based.
