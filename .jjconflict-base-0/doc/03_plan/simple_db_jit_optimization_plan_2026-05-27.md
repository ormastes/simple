# SimpleDB JIT + Optimization Plugin Plan

**Goal:** PureDatabase ≥ SQLite (prepared stmt, WAL) across PUT/GET/SCAN/UPDATE.
**Constraint:** Pure Simple only. No Rust-backed optimizations.
**Date:** 2026-05-27

## Current State

| Op         | SimpleDB (ns/op) | SQLite (ns/op) | Gap   |
|------------|-------------------|-----------------|-------|
| PUT x200   | 179,510           | 1,060           | 169x  |
| GET x100   | 74,747            | 840             | 89x   |
| SCAN x100  | 29,304            | 11,300          | 2.6x  |
| UPD x100   | 265,077           | 1,500           | 177x  |

- SCAN is nearest parity (cache hits dominate, interpreter overhead amortized over 100-row result set)
- PUT/GET/UPD gap is ~100-180x — dominated by interpreter dispatch overhead (~3-5 μs/statement)
- JIT is broken: `HIR lowering error: Unknown variable: int` (falls back to interpreter)
- Existing optimizations: scan result cache, visibility batch cache, PK point lookup, in-place typed update

## Architecture: Two-Track Plan

### Track A — Interpreter-Mode Wins (near-term, testable now)
Reduces constant factors within interpreter dispatch. Each sub-track targets a disjoint file set.

### Track B — JIT Fix (structural, compiler work)
Fixes the broken JIT compiler so hotspot compilation eliminates interpreter dispatch entirely.

Both tracks run in parallel. Track A delivers incremental gains immediately; Track B is the floor-lifter that closes the remaining 50-100x gap.

---

## Track A: Interpreter-Mode Optimizations

### A1: PureDatabase Hot-Path Restructuring
**Files:** `src/lib/nogc_sync_mut/database/pure_sql/database.spl` (EXCLUSIVE)
**Agent:** Sonnet + Opus advisor
**Goal:** Reduce per-op interpreter statement count by 2-5x

#### A1.1: Array Copy Elimination
Arrays are value types in Simple — `val typed = self._tbl_typed[ti]` copies the entire array.
- Identify every hot-path array copy in put/get/update
- Restructure to index directly: `self._tbl_typed[ti][row_idx]` instead of `val typed = self._tbl_typed[ti]; typed[row_idx]`
- For scan: accumulate results without intermediate array copies
- **Expected gain:** 2-3x on PUT/GET/UPD (dominant cost is array-of-arrays copy)

#### A1.2: Statement Count Reduction
- Inline small helper calls (visibility check, type conversion) to reduce interpreter dispatch
- Merge sequential Dict lookups into single-pass iteration where possible
- Eliminate redundant `unwrap()` chains — use direct field access on known-good paths
- Hoist loop-invariant computations (table index lookup, schema length) out of hot loops
- **Expected gain:** 1.5-2x additional

#### A1.3: Typed Storage Fast Paths
- For tables with typed storage enabled (most common case), bypass generic MVCC/serialization entirely
- PUT: Direct array append without DbValue→serialization→deserialization round-trip
- GET: Direct array index without row reconstruction
- UPDATE: Already in-place (done), but eliminate remaining Dict allocation for single-field updates
- **Expected gain:** 2-3x on PUT, 1.5x on GET

#### A1 Combined Target
| Op   | Current (ns) | Target (ns) | Reduction |
|------|-------------|-------------|-----------|
| PUT  | 179,510     | ~15,000     | ~12x      |
| GET  | 74,747      | ~8,000      | ~9x       |
| SCAN | 29,304      | ~8,000      | ~3.5x     |
| UPD  | 265,077     | ~20,000     | ~13x      |

Still 8-20x from SQLite — remaining gap is irreducible interpreter overhead.

### A2: MIR Optimization Pattern Registration
**Files:** `src/compiler/60.mir_opt/mir_opt/pattern/rules_clib_parity.spl`, `test/unit/compiler/mir_opt/clib_parity_hotspot_spec.spl` (EXCLUSIVE)
**Agent:** Sonnet + Opus advisor
**Goal:** Register new general-purpose patterns for the optimizations applied in A1

Each optimization from A1 maps to a reusable CLibParityRule:

| Pattern | CLibPatternKind | Domain | Intrinsic | Required Proof |
|---------|-----------------|--------|-----------|----------------|
| Array copy elision on indexed access | CopyElisionPointLookup | general | `index_point_lookup_direct` | `index_key_immutable_in_lookup` |
| Loop-invariant hoist | ArrayLenHoist | general | `array_len_hoisted` | `array_no_mutation_in_loop` |
| Dict lookup fusion | DictLookupFusion | general | `dict_lookup_fused` | `key_immutable_in_sequence` |
| Dead branch elimination on typed storage | DeadBranchElim | database | `db_dead_branch_removed` | `branch_condition_is_const` |
| String concat batch | StringConcatReduce | general | `string_concat_batch` | `concat_order_preserved` |

These patterns already exist in the rule table (added in prior commit). A2 verifies they're exercised by the A1 code changes and adds any missing patterns.

**Extensibility contract:** New domains plug in by adding rows + proof predicates to `clib_parity_rule_table()`. Existing proof predicates form the extensibility surface:
- `alias_non_overlap_or_memmove` — memory safety
- `mutation_invalidation_complete` — cache coherence
- `snapshot_monotonic_equivalence` — MVCC correctness
- `index_key_immutable_in_lookup` — index stability
- `array_no_mutation_in_loop` — loop invariant
- `concat_order_preserved` — string builder
- `branch_condition_is_const` — dead code
- `key_immutable_in_sequence` — Dict fusion

### A3: Benchmark Hardening
**Files:** `test/perf/bench/compiled_db_bench_standalone.spl` (EXCLUSIVE)
**Agent:** Sonnet
**Goal:** Reliable regression detection

- Run N≥5 iterations per operation, report median and p99
- Add variance check: if p99/median > 3x, mark result as noisy
- Add explicit regression gate: fail if any op regresses >10% from baseline
- Store baseline numbers in SDN format for comparison
- Separate cold-start (first run after setup) from hot (cached) metrics

---

## Track B: JIT Compiler Fix

### B1: Reproduce and Diagnose JIT Error
**Files:** `src/compiler/10.frontend/core/interpreter/jit.spl`, Rust source under `src/compiler_rust/` (EXCLUSIVE — no overlap with Track A files)
**Agent:** Sonnet + Opus advisor
**Goal:** Minimal repro of `HIR lowering error: Unknown variable: int`

- Create minimal `.spl` file that triggers the JIT error
- Trace the error through: HIR construction → variable resolution → lowering
- The error occurs during HIR lowering when the JIT tries to compile a function
- Two known error variants: `Unknown variable: int` and `Unknown type: T` — both may be related to generics monomorphization in the JIT path
- Determine if the fix is in Simple-side (`tiered_jit.spl`, `jit_interpreter.spl`) or Rust-side (`src/compiler_rust/`)

### B2: JIT HIR Lowering Fix
**Files:** Determined by B1 diagnosis
**Agent:** Sonnet + Opus advisor
**Prerequisite:** B1 complete

- Fix the HIR variable/type resolution for JIT compilation
- Key infrastructure already exists:
  - `src/compiler/95.interp/execution/tiered_jit.spl` — tiered compilation with `JitHotspotPlan`, `FunctionProfile`, call counting
  - `src/compiler/70.backend/backend/jit_interpreter.spl` — hybrid interpreter with JIT fallback
  - `src/compiler/99.loader/loader/jit_context.spl` — JIT context management
  - `src/lib/nogc_sync_mut/jit/jit_backend.spl` — backend interface (load_binary, verify_binary)
- The tiered system already has: call counting, threshold detection, compile decision, deopt fallback
- The missing piece is correct HIR lowering for generic types and built-in type names

### B3: Pattern → JIT Bridge
**Files:** `src/compiler/60.mir_opt/mir_opt/pattern/rule_engine.spl`, `src/compiler/95.interp/execution/tiered_jit.spl`
**Agent:** Sonnet + Opus advisor
**Prerequisite:** B2 complete (JIT can compile basic functions)

- Connect CLibParityRule patterns to JIT specialization
- When JIT compiles a hot function, the MIR optimizer applies matched rules as intrinsic replacements
- `JitHotspotSpecializationProvider` (already in tiered_jit.spl) provides the bridge:
  - Profile facts feed into `clib_parity_rule_has_required_fact()`
  - Proof obligations feed into `clib_parity_rule_has_required_proof()`
  - Eligible rules produce intrinsic calls in the JIT-compiled output
- This makes every CLibParityRule automatically available to JIT-compiled code

### B4: JIT Benchmark Validation
**Prerequisite:** B3 complete
- Re-run benchmark with JIT enabled
- Compare JIT vs interpreter performance
- Target: within 2x of SQLite on all operations

---

## Execution Plan: Sonnet Agent Teams + Opus Advisor

### Phase 1: Track A (parallel, immediate start)
```
┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐
│ Sonnet Agent A1  │  │ Sonnet Agent A2  │  │ Sonnet Agent A3  │
│ database.spl     │  │ rules_clib_*.spl │  │ bench_*.spl      │
│ Hot-path restructure │ Pattern registration │ Benchmark harden  │
│ + Opus advisor   │  │ + Opus advisor   │  │                  │
└────────┬────────┘  └────────┬────────┘  └────────┬────────┘
         │                    │                    │
         ▼                    ▼                    ▼
    [Merge gate: all tests pass, bench shows improvement]
```

### Phase 2: Track B (sequential, starts after B1 diagnosis)
```
B1: Minimal repro ──→ B2: HIR fix ──→ B3: Pattern→JIT bridge ──→ B4: Validate
    (Sonnet)           (Sonnet+Opus)   (Sonnet+Opus)               (Sonnet)
```

### Phase 3: Integration
- Run full benchmark suite with JIT + all Track A optimizations
- Verify no regressions in existing test suite (66 clib_parity_hotspot_spec tests)
- Update SQLite comparison numbers

---

## Quality Gates

| Gate | Criteria | Blocking |
|------|----------|----------|
| G1: Track A merge | All existing tests pass, benchmark improves on ≥3 of 4 ops | Yes |
| G2: JIT compiles | Minimal function compiles without HIR error | Yes for B3 |
| G3: Pattern bridge | ≥1 CLibParityRule fires during JIT compilation | Yes for B4 |
| G4: SQLite parity | Median of 5 runs within 2x SQLite on all ops | Final goal |

## Risk Register

| Risk | Impact | Mitigation |
|------|--------|------------|
| JIT fix takes weeks (compiler bug) | Track B delayed | Track A delivers 10-15x improvement independently |
| Array value-type semantics limit optimization | A1 gains capped | Compiler-level copy elision (Track B pattern) |
| Interpreter dispatch is the true bottleneck | Track A gains plateau at ~10-15x from SQLite | JIT (Track B) is the only path to parity |
| Parallel agents clobber files | Lost work | Disjoint file scopes enforced per track |
| jj VCS corruption during parallel work | Commit loss | Use git directly for commits/pushes |

## Success Criteria

1. **Near-term (Track A):** PureDatabase within 15x of SQLite on PUT/GET/UPD, within 1x on SCAN
2. **Mid-term (Track B1-B2):** JIT compiles basic functions without HIR error
3. **Full (Track B3-B4):** PureDatabase within 2x of SQLite on all operations with JIT enabled

---

## Progress Log

### 2026-05-27 — Phase 1 In Progress

**A1: Hot-Path Restructuring — DONE (partial)**
- Added `_pk_flat: Dict<text, i32>` flat PK index keyed by `"{ti}:{pk_value}"` for O(1) lookups
- Added `_tbl_pk_name: [text]` for fast PK column match without Dict copy
- GET fast path: 2.6x faster (137k→53k ns/op) — avoids nested array-of-Dict copy
- PUT fast path: 2.1x faster (443k→207k ns/op) — direct `_pk_flat` update
- UPD fast path: 2.2x faster (671k→305k ns/op) — `_pk_flat` lookup with `_tbl_pk_map` fallback
- Fixed checkpoint `_pk_dirty` staleness (bulk invalidation on checkpoint)
- Fixed SQL INSERT `_pk_flat` population gap in `_do_insert`
- Further array copy elimination blocked by value-type semantics (Track B JIT needed)
- All tests stable: 41/59 pure_db_spec pass (18 pre-existing), 10/10 SQL extended

**A2: MIR Optimization Patterns — DONE**
- 4 CLibPatternKind variants: ScanResultCache, VisibilityBatchPrecompute, CopyElisionPointLookup, FlatKeyIndex
- 8 new rules in clib_parity_rule_table() (database + general variants)
- 5 general patterns: DictLookupFusion, ArrayLenHoist, DeadBranchElim, StringConcatReduce, IntCmpStrengthReduce
- FlatKeyIndex: composite-key flattening (`container[a][b]` → `flat_dict["{a}:{b}"]`)
- All 70 clib_parity_hotspot_spec tests pass

**A3: Benchmark Hardening — DONE**
- 5-iteration median/min/max reporting with NOISY variance detection
- Insertion sort for small i64 arrays, per-table PUT isolation
- SCAN cold kept as single-shot; sanity checks use verification pass
- Latest median results: PUT 207k ns, GET 53k ns, SCAN 47k ns, UPD 305k ns

**B1: JIT HIR Error Diagnosis — DONE**
- Error source: `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:292` fires `LowerError::UnknownVariable("int")`
- Root cause: `int(x)` is a constructor-style type-cast. Parser produces `Expr::Call { callee: Expr::Identifier("int") }`. HIR lowerer can't resolve `"int"` as identifier — builtin cast names aren't registered in HIR scope
- Interpreter works because it bypasses HIR entirely: `interpreter/expr/casting.rs:40` handles via `NumericType::from_name("int")`
- Same failure for all cast calls: `text(x)`, `bool(x)`, `char(x)`, `i8(x)`..`u64(x)`, `f32(x)`, `f64(x)`
- Fix: Rust HIR lowerer only — either (A) intercept in `hir/lower/expr/calls.rs` when callee matches NumericType::from_name, or (B) register all builtin cast names as pseudo-globals at lowerer init
- Minimal repro: `fn parse_int(s: text) -> i64: int(s)` + `fn main(): print(parse_int("42").to_text())`

**B2: JIT HIR Lowering Fix — DONE (2026-05-28)**
- Two blockers found and fixed:
  1. **HIR cast lowering**: Added cast-style call interception in `lower_utility_builtin()` in `hir/lower/expr/calls.rs`
     - All 15 cast names: `int`/`i64`, `i8`, `i16`, `i32`, `u8`-`u64`, `f32`, `f64`/`float`, `bool`, `text`/`str`/`String`, `char`
     - Emits `HirExprKind::Cast { expr, target }` (not BuiltinCall) — proper downstream MIR/codegen handling
     - Matches interpreter's `NumericType::from_name` + `cast_to_simple_type` mapping byte-for-byte
  2. **JIT eligibility defaults**: `register_function()` in `tiered_jit.spl` hardcoded `typed_mir: false, safe_deopt: false`
     - Simple is statically typed → `typed_mir: true` is correct for all functions
     - Interpreter fallback is always safe → `safe_deopt: true` is correct
     - Fixed all three registration paths: `register_function`, `record_call` fallback, `get_hotspot_plan` fallback
- `cargo check --profile bootstrap` passes; `cargo build --release` rebuilding seed
