# Scilib Port — Perf-Sugar Agent Task List

**Area:** `perf_sugar`  
**File:** `doc/03_plan/agent_tasks/scilib_port_perf_sugar.md`  
**Date:** 2026-04-27  
**Status:** Phase 3 arch complete; ready for Phase 5 execution  
**Upstream:** None — this is the lowest layer; must complete before `scilib_port_ndarray.md` begins  
**Downstream gate:** `scilib_port_ndarray.md` (PERF-SUGAR-001 must be `fixed` before any T-NDARRAY-* allocates a typed buffer)

Cross-reference IDs in `doc/08_tracking/feature_request/scilib_perf_sugar.md`.

---

## Anti-Patterns (do NOT propose these)

- **No silent workarounds.** Every observed friction gets an append to `scilib_perf_sugar.md` with a concrete entry (AC-6 contract). Do not adjust code to hide the wedge.
- **No `rt_bytes_alloc` + reinterpret-cast bypass.** Using the `[u8]` allocator for `f64` data is a cover-up. `feedback_no_coverups` and architecture §10 OQ-F both lock this out.
- **No `--mode=native` or `--mode=smf` for any measurement or spec run.** Both produce false-green results. All scilib specs run under `bin/simple test` (interpreter mode), per `feedback_compile_mode_false_greens` and PERF-SUGAR-012.
- **No `bin/simple build bootstrap` for the rebuild step.** That command falls through the wrapper whitelist and silently no-ops. Use `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (per `feedback_extern_bootstrap_rebuild`).
- **No new tracking IDs for already-filed entries.** If measurement confirms a wedge, append to the existing PERF-SUGAR-NNN entry and update its `Status` field; do not create a duplicate.
- **No TODO → NOTE conversions.** Implement or delete. (`feedback_no_coverups`)

---

## Dependency Graph

```
T-PERFSUGAR-01 (rt_f64_array_alloc Rust impl)
  └─ T-PERFSUGAR-02 (rt_f32_array_alloc Rust impl)
  └─ T-PERFSUGAR-03 (rt_i64_array_alloc Rust impl)
  └─ T-PERFSUGAR-04 (rt_i32_array_alloc Rust impl)
       └─ T-PERFSUGAR-05 (interpreter whitelist all four)
            └─ T-PERFSUGAR-06 (Simple-side extern fn decls)
                 └─ T-PERFSUGAR-07 (bootstrap rebuild + verify)
                      └─ T-PERFSUGAR-08 (smoke spec: large typed alloc)
                           └─ T-PERFSUGAR-09 (promote PERF-SUGAR-001 to fixed)

T-PERFSUGAR-10 (AC-6 capture harness: protocol + script)  [parallel to above, no dep]

v1.1 observation tasks (after T-PERFSUGAR-09 is done, during ndarray/linalg impl):
  T-PERFSUGAR-11 (observe PERF-SUGAR-002: math-block intermediate alloc)
  T-PERFSUGAR-12 (observe PERF-SUGAR-003: generic <T> boxing cost)
  T-PERFSUGAR-13 (observe PERF-SUGAR-011: Float64(x) heap alloc cost)
  T-PERFSUGAR-14 (observe PERF-SUGAR-004: FFI extern call overhead)
  T-PERFSUGAR-15 (observe PERF-SUGAR-005: strided view vs copy cost)
  T-PERFSUGAR-16 (observe PERF-SUGAR-006: symbol intern vs string compare)
  T-PERFSUGAR-17 (observe PERF-SUGAR-007: groupby materialization cost)
  T-PERFSUGAR-18 (observe PERF-SUGAR-008: FMA missing: 2× ops estimate)
  T-PERFSUGAR-19 (observe PERF-SUGAR-009: broadcast sugar: element loop cost)
  T-PERFSUGAR-20 (observe PERF-SUGAR-010: in-place += copy cost)
  T-PERFSUGAR-21 (observe PERF-SUGAR-012: interp false-green process wedge)
  T-PERFSUGAR-22 (observe PERF-SUGAR-013: loop fusion / SIMD gap)

v2 design tasks (no impl; after v1.1 observations complete):
  T-PERFSUGAR-23 (design: math-block kernel fusion pass — PERF-SUGAR-002 fix)
  T-PERFSUGAR-24 (design: interpreter monomorphization cache — PERF-SUGAR-003 fix)
  T-PERFSUGAR-25 (design: FMA peephole + SIMD loop fusion — PERF-SUGAR-008/013 fix)
  T-PERFSUGAR-26 (design: newtype zero-cost + in-place augmented assign — PERF-SUGAR-011/010)
```

Total: **26 tasks** — 10 v1 / 12 v1.1 / 4 v2.

---

## v1 Tasks — PERF-SUGAR-001 Impl (Gating)

### T-PERFSUGAR-01 — Implement `rt_f64_array_alloc` in Rust runtime

**Effort:** 1 day  
**Priority:** P0 — hard gate  
**PERF-SUGAR ref:** 001  
**Deps:** None

Implement `rt_f64_array_alloc(len: u64) -> [f64]` in the Rust interpreter extern layer. Pattern: mirror `rt_bytes_alloc` (located in `src/compiler_rust/compiler/src/interpreter_extern/` — verify exact file during impl; do not assume filename). The function must:

- Accept `len` as element count (number of `f64` values), not byte count.
- Allocate a zero-filled `Vec<f64>` of length `len` C-side.
- Return it as a Simple `[f64]` value (not `[u8]`); use the same return-value wrapping that `rt_bytes_alloc` uses for `[u8]`.
- Match observed performance: 1 MiB f64 (128 Ki elements) under 50 ms in interpreter mode; 32 MiB f64 (4 Mi elements) under 2 s (comparable to `rt_bytes_alloc` 32 MiB = 1.5 s benchmark).

Do NOT use `rt_bytes_alloc` + reinterpret-cast. That is a cover-up (`feedback_no_coverups`, architecture §10 OQ-F).

**Deliverable:** Rust function committed in the runtime extern module.

---

### T-PERFSUGAR-02 — Implement `rt_f32_array_alloc` in Rust runtime

**Effort:** 0.5 day  
**Priority:** P0  
**PERF-SUGAR ref:** 001  
**Deps:** T-PERFSUGAR-01 (same module; implement in the same commit batch)

Implement `rt_f32_array_alloc(len: u64) -> [f32]`. Same pattern as T-PERFSUGAR-01 but for `f32`. Zero-fill. Element-count semantics.

**Deliverable:** Rust function in same module as T-PERFSUGAR-01.

---

### T-PERFSUGAR-03 — Implement `rt_i64_array_alloc` in Rust runtime

**Effort:** 0.5 day  
**Priority:** P0  
**PERF-SUGAR ref:** 001  
**Deps:** T-PERFSUGAR-01

Implement `rt_i64_array_alloc(len: u64) -> [i64]`. Zero-fill. Element-count semantics. Covers `NDArray<Int64>` and `NDArray<Index>` backing buffers.

**Deliverable:** Rust function in same module.

---

### T-PERFSUGAR-04 — Implement `rt_i32_array_alloc` in Rust runtime

**Effort:** 0.5 day  
**Priority:** P0  
**PERF-SUGAR ref:** 001  
**Deps:** T-PERFSUGAR-01

Implement `rt_i32_array_alloc(len: u64) -> [i32]`. Zero-fill. Element-count semantics. Covers `DType.I32` ndarray backing.

**Deliverable:** Rust function in same module.

---

### T-PERFSUGAR-05 — Wire all four externs into interpreter whitelist

**Effort:** 0.5 day  
**Priority:** P0  
**PERF-SUGAR ref:** 001  
**Deps:** T-PERFSUGAR-01, T-PERFSUGAR-02, T-PERFSUGAR-03, T-PERFSUGAR-04

Add `rt_f64_array_alloc`, `rt_f32_array_alloc`, `rt_i64_array_alloc`, `rt_i32_array_alloc` to the interpreter's extern dispatch table (whitelist). Verify: the interpreter must recognize each function name string and route to the correct Rust implementation. A missing whitelist entry causes a silent "extern not found" at runtime — not a compile error — which is the most common failure mode for new externs.

Check the dispatch module (likely `mod.rs` or `extern_dispatch.rs` in the interpreter_extern directory — verify during impl). Add one match arm per extern name.

**Deliverable:** All four names registered in the dispatch table; a `bin/simple` invocation calling each extern at the REPL level returns a non-error value.

---

### T-PERFSUGAR-06 — Add Simple-side `extern fn` declarations

**Effort:** 0.5 day  
**Priority:** P0  
**PERF-SUGAR ref:** 001  
**Deps:** T-PERFSUGAR-05

Create or update the Simple-side extern declaration file for the four allocators. Location: a new file `src/lib/nogc_sync_mut/ndarray/rt_alloc.spl` (or colocated with the NDArray impl file — agree with the ndarray agent before writing; coordinate on file path to avoid scope collision per `feedback_parallel_scope_partition`).

Declarations:
```
extern fn rt_f64_array_alloc(len: u64) -> [f64]
extern fn rt_f32_array_alloc(len: u64) -> [f32]
extern fn rt_i64_array_alloc(len: u64) -> [i64]
extern fn rt_i32_array_alloc(len: u64) -> [i32]
```

These declarations must be visible to NDArray factory methods (`zeros`, `ones`, `from_seq`). Scope must be `nogc_sync_mut` or `common`; do not place in `gc_async_mut`.

**Deliverable:** `.spl` file with the four declarations, importable from ndarray impl.

---

### T-PERFSUGAR-07 — Run bootstrap-from-scratch rebuild and verify

**Effort:** 1 day  
**Priority:** P0  
**PERF-SUGAR ref:** 001  
**Deps:** T-PERFSUGAR-06

After any new `extern fn` is added, the self-hosted (Simple) compiler must be rebuilt from scratch. The command is:

```
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

Do NOT use `bin/simple build bootstrap` — it falls through the wrapper whitelist and silently no-ops without rebuilding the self-hosted binary (`feedback_extern_bootstrap_rebuild`).

Verify after rebuild:
1. `bin/simple` is the newly built self-hosted binary (check mtime or version output).
2. `bin/simple test` still passes all pre-existing tests (no regression).
3. A minimal inline test calling `rt_f64_array_alloc(1024)` runs without "extern not found" error.

Record the bootstrap duration and any failures in the task completion note. If bootstrap fails, do not proceed to T-PERFSUGAR-08 — diagnose and fix the root cause.

**Deliverable:** Rebuilt `bin/simple` with the four externs active; all pre-existing tests green.

---

### T-PERFSUGAR-08 — Write smoke spec: large typed buffer alloc in interpreter mode

**Effort:** 1 day  
**Priority:** P0  
**PERF-SUGAR ref:** 001  
**Deps:** T-PERFSUGAR-07

Write `test/perf/typed_array_alloc_spec.spl` (interpreter mode; no `--mode` flag). The spec must:

- Allocate a 1 MiB f64 buffer (131,072 elements) and assert all elements are `0.0`.
- Allocate a 4 MiB f64 buffer (524,288 elements) — assert non-error return.
- Allocate an equivalent i64 buffer; assert element count.
- Assert each alloc completes in < 200 ms wall-clock (use `rt_clock_ms()` or equivalent if available; otherwise annotate as manual timing check).
- Use `bin/simple test` (interpreter mode); must pass with zero `skip()`.

This spec is the `rt_bytes_alloc` parallel for typed arrays (see `feedback_interpreter_bulk_buffer`; that note measured 1 MiB at 45 ms, 32 MiB at 1.5 s for `[u8]`). The f64 case may differ; record actual measurements.

Do NOT use `--mode=native` or `--mode=smf` to make the spec pass. Interpreter mode only.

**Deliverable:** `test/perf/typed_array_alloc_spec.spl` passing under `bin/simple test`.

---

### T-PERFSUGAR-09 — Promote PERF-SUGAR-001 to `fixed` in tracking file

**Effort:** 0.25 day  
**Priority:** P0  
**Deps:** T-PERFSUGAR-08 (smoke spec green)

Update `doc/08_tracking/feature_request/scilib_perf_sugar.md` entry PERF-SUGAR-001:
- `Status: anticipated` → `Status: fixed`
- Append measured timings from T-PERFSUGAR-08 under `Current-cost`.
- Note the bootstrap rebuild date and `bin/simple` version hash.

Use the append protocol defined in T-PERFSUGAR-10 (append to existing entry; do not rewrite it). If T-PERFSUGAR-10 is not yet complete, follow the schema in the tracking file's `## Schema` section manually.

This task unblocks `scilib_port_ndarray.md`. Do not signal "ndarray agent may begin" until this task is merged.

**Deliverable:** PERF-SUGAR-001 status = `fixed` in the tracking file.

---

### T-PERFSUGAR-10 — Create AC-6 capture harness (protocol + script)

**Effort:** 1 day  
**Priority:** P0 (AC-6 contract)  
**Deps:** None (can run in parallel with T-PERFSUGAR-01..09)

AC-6 requires that every observed perf or ergonomic wedge is captured as a concrete tracking entry, not silently worked around. This task delivers the capture harness so future impl agents can append entries without rewriting the tracking file.

**Part A — Append protocol (documentation):**

Add a `## Append Protocol` section to `doc/08_tracking/feature_request/scilib_perf_sugar.md` immediately after `## Schema`:

```
## Append Protocol

Rules:
1. Never edit or rewrite an existing entry. Only append new content below it.
2. Assign a monotonically increasing id (next = current max + 1).
3. Fill all schema fields. `Current-cost` may be `unknown — measure during impl`
   if the wedge is anticipated; update the field in-place (append a `Measured:` line)
   once measured.
4. `Status` transitions: anticipated → observed → fixed | wontfix.
   Never skip `observed` — every fix must have a measurement confirming improvement.
5. Use `scripts/scilib_perf_capture.shs` for convenience (optional).
6. Never create a duplicate id for an already-filed wedge.
   If you hit the same wedge again, update the existing entry's status/notes.
```

**Part B — Convenience script:**

Create `scripts/scilib_perf_capture.shs` with the following interface:

```sh
# Usage:
#   sh scripts/scilib_perf_capture.shs \
#       --id=014 \
#       --title="Short verb-led title ≤80 chars" \
#       --priority=P1 \
#       --repro="minimal code snippet" \
#       --cost="unknown — measure during impl" \
#       --sugar="proposed compiler/stdlib change"
#
# Appends a formatted PERF-SUGAR-NNN entry to:
#   doc/08_tracking/feature_request/scilib_perf_sugar.md
#
# Does NOT overwrite existing entries.
# Exits non-zero if the id already exists in the file.
```

The script appends (does not rewrite) the formatted block. It must:
- Exit 1 with a clear error message if `--id=NNN` already exists in the file.
- Write the new entry block using the schema (id, title, filed-on = today, filed-by = `$USER`, priority, status = `anticipated`, expected-repro, current-cost, proposed-sugar).
- Be a `.shs` file (Simple shell); follow project convention (no Python/Bash; `.shs` files use Simple scripting per CLAUDE.md).

**Deliverable:** Append protocol section added to tracking file; `scripts/scilib_perf_capture.shs` created.

---

## v1.1 Tasks — Observation During Impl

These tasks run **during** the ndarray/linalg/df implementation phases (not before). Each task measures a specific wedge in interpreter mode, then updates the corresponding `scilib_perf_sugar.md` entry with real data. The outcome of each task is either:

- **Confirm** → set status `observed`; file a concrete fix task if P0/P1.
- **Downgrade** → set status `wontfix` or `P2` with written rationale.

None of these tasks produce code changes. They only produce measurements and tracking file updates.

---

### T-PERFSUGAR-11 — Observe PERF-SUGAR-002: math-block intermediate alloc cost

**Effort:** 1 day  
**Priority:** P1  
**PERF-SUGAR ref:** 002  
**Deps:** `scilib_port_math_block.md` has at least one `math { A @ B + v }` spec running

Write a measurement script (or in-test timing) that compares:
- `math { A @ B + v }` in interpreter mode (expected: 2 intermediate Block allocs)
- Equivalent explicit `linalg.gemm(alpha, A, B, beta, v)` call

Measure wall-clock time and (if accessible) allocation count for matrices of size 64×64, 256×256, 1024×1024. Record in PERF-SUGAR-002 entry.

**Threshold:** if math-block is > 2× slower than explicit extern call at 256×256, set status `observed` and flag as P0 for v2 fusion design (T-PERFSUGAR-23). If within 2×, set status `observed` with a note that the overhead is acceptable for v1 (fusion still desired for v2).

Reminder from architecture §7: "Teams must not use `math{}` in hot inner loops in v1 — use explicit `linalg.gemm` calls instead." This observation task validates that guidance empirically.

**Deliverable:** PERF-SUGAR-002 `Current-cost` filled; status updated.

---

### T-PERFSUGAR-12 — Observe PERF-SUGAR-003: generic `<T>` dispatch boxing overhead

**Effort:** 1.5 days  
**Priority:** P1 (blocker for AC-7 quality)  
**PERF-SUGAR ref:** 003  
**Deps:** `scilib_port_ndarray.md` has a working `NDArray<T>` and at least one generic `fn dot<T>`

Measure:
- `fn dot<T>(a: NDArray<T>, b: NDArray<T>) -> T` called with `T=Float64` in interpreter mode: time for n=1000, n=10000, n=100000 element dot product.
- Equivalent hand-written `fn dot_f64(a: NDArray<Float64>, b: NDArray<Float64>) -> Float64` (non-generic specialization): same sizes.

Ratio = `generic_time / specialized_time`. Record this ratio at each size.

**Threshold:** if ratio > 3× at n=10000, status `observed` and flag as P1 requiring the stdlib-workaround mitigation path (provide `dot_f64`, `dot_f32` specializations alongside generic facade for v1). If ratio < 1.5×, status `observed` with note that boxing cost is acceptable in interp-mode for v1; v2 monomorphization cache still desired.

Note: the v1 mitigation (non-generic specializations) is a stdlib workaround, not a compiler fix. The compiler fix (monomorphization cache) is T-PERFSUGAR-24 (v2 design). Both are valid responses; the measurement decides which is needed for v1.

**Deliverable:** PERF-SUGAR-003 `Current-cost` filled with ratios; status updated; mitigation path documented in entry.

---

### T-PERFSUGAR-13 — Observe PERF-SUGAR-011: `Float64(x)` wrapper construction heap overhead

**Effort:** 1 day  
**Priority:** P1  
**PERF-SUGAR ref:** 011  
**Deps:** `scilib_port_ndarray.md` has `Float64` wrapper type defined

Measure:
- `NDArray.from_list([Float64(1.0), Float64(2.0), ..., Float64(n)])` for n=1000, n=10000, n=100000 in interpreter mode.
- Compare to a hypothetical raw `[f64]` construction of same size (if feasible without breaking no-primitive rule — if not, estimate from alloc count alone).

The concern from architecture §3: "if `Float64(x)` allocates a heap object in the interpreter, then the no-primitive-in-public-API rule imposes a 1M-alloc tax on every large array literal."

**Threshold:** if 100K-element construction allocates > 100K heap objects (measurable via profiling or synthetic timing), set status `observed` and flag PERF-SUGAR-011 as P1 soft-gate for v1.1; document in the tracking entry that v1 impl agents must avoid `from_list` with literal `Float64(x)` constructions at scale (use `zeros`/`ones` + `rt_f64_array_alloc` instead). If heap alloc count is bounded (compiler already value-inlines), set `observed` + `wontfix` with note.

**Deliverable:** PERF-SUGAR-011 `Current-cost` filled; status updated.

---

### T-PERFSUGAR-14 — Observe PERF-SUGAR-004: FFI extern call overhead per BLAS level-1 op

**Effort:** 1 day  
**Priority:** P1  
**PERF-SUGAR ref:** 004  
**Deps:** `scilib_port_blas.md` has `linalg.dot` (BLAS ddot) working under mock backend

Measure wall-clock time for:
- 1000 calls to `linalg.dot(x, y)` where `x`, `y` are 128-element `Vector<Float64>` — each call crosses the FFI boundary once.
- Single call to `linalg.dot(x, y)` where `x`, `y` are 128,000-element vectors.

Expected per the architecture: FFI overhead estimated at 50–200 ns per crossing; crossover threshold around 64–512 bytes. At 128 elements × 8 bytes = 1 KiB per vector, the compute may dominate. Verify.

**Threshold:** if 1000 calls to 128-element dot take > 5 ms total (i.e., > 5 µs per call overhead), set status `observed` and flag as needing batch-call design (T-PERFSUGAR-25 scope). If < 1 ms, downgrade to `wontfix` with note that FFI overhead is not measurable at this vector size.

**Deliverable:** PERF-SUGAR-004 `Current-cost` filled; status updated.

---

### T-PERFSUGAR-15 — Observe PERF-SUGAR-005: strided view vs copy cost for NDArray slice

**Effort:** 1 day  
**Priority:** P1 (df gate)  
**PERF-SUGAR ref:** 005  
**Deps:** `scilib_port_ndarray.md` has `NDArray[.., j]` column-slice implemented

Measure:
- `A[.., j]` column slice on a 1024×1024 `NDArray<Float64>` — is it O(1) or O(n)?
- If it copies, measure copy time vs expected O(1) view time (reference: any pointer-arithmetic operation on the same array).

**Threshold:** if column slice is O(n) copy (measured time scales linearly with number of rows), set status `observed` and confirm PERF-SUGAR-005 is a hard gate before v1.1 df impl (architecture §10 locks this). If O(1) view is already implemented (via `_offset` + `_strides` in `NDArray`), set status `fixed` and note the implementation approach.

**Deliverable:** PERF-SUGAR-005 `Current-cost` filled; status updated (`observed` or `fixed`).

---

### T-PERFSUGAR-16 — Observe PERF-SUGAR-006: symbol intern vs string compare for column names

**Effort:** 0.5 day  
**Priority:** P1  
**PERF-SUGAR ref:** 006  
**Deps:** `scilib_port_df.md` has at least a stub `DataFrame.select` that takes column names

Measure:
- `df.select(["revenue"])` with column lookup using `text` equality (O(len) string compare) for a DataFrame with 100 columns.
- Repeat 10,000 times; record total time.
- If `rt_intern_symbol` is available: compare against pointer-equality path.

**Threshold:** if 100-column lookup, 10K iterations takes > 50 ms (i.e., string comparison dominates), set status `observed` and flag `rt_intern_symbol` as needed before v1.1 groupby spec. If < 5 ms, downgrade to `wontfix` with note that string compare is acceptable at typical column counts.

**Deliverable:** PERF-SUGAR-006 `Current-cost` filled; status updated.

---

### T-PERFSUGAR-17 — Observe PERF-SUGAR-007: groupby iterator materialization cost

**Effort:** 1 day  
**Priority:** P1  
**PERF-SUGAR ref:** 007  
**Deps:** `scilib_port_df.md` has `DataFrame.groupby` implemented (even as stub)

Measure — or design-verify:
- If groupby returns a lazy `(key, RowRange)` iterator (architecture §8 mandates this), verify no full-group copy occurs by checking memory use before/after `groupby("region").sum()` on a 10K-row DataFrame with 10 groups.
- If groupby materializes groups (deviates from lazy design), record the alloc count per group.

**Threshold:** if groupby is lazy (per architecture), set status `observed` + `confirmed lazy path — no fix needed`. If groupby materializes, set status `observed` + P0 for df phase; log the fix requirement in the entry.

**Deliverable:** PERF-SUGAR-007 `Current-cost` filled; status updated.

---

### T-PERFSUGAR-18 — Observe PERF-SUGAR-008: FMA absence; estimate 2× ops overhead

**Effort:** 0.5 day  
**Priority:** P2 (v2 relevance)  
**PERF-SUGAR ref:** 008  
**Deps:** Any working `Float64` arithmetic in interpreter mode

This is a lightweight observation task. Do not benchmark in interpreter mode (FMA is a compiled-mode concern; interpreter has no FMA dispatch). Instead:

- Confirm by code inspection that the interpreter has no FMA contraction pass.
- Confirm by Cranelift backend inspection (or compiler team confirmation) that the Cranelift backend does not emit `fma` instructions for `a * b + c`.
- Write a short note in the tracking entry confirming the gap and estimating the impact as "2× float ops vs hardware FMA on AVX2/AVX-512 in compiled mode."

Set status `observed`. This feeds T-PERFSUGAR-25 (v2 design).

**Deliverable:** PERF-SUGAR-008 `Current-cost` updated with inspection findings; status = `observed`.

---

### T-PERFSUGAR-19 — Observe PERF-SUGAR-009: broadcast scalar op forces element loop

**Effort:** 1 day  
**Priority:** P2  
**PERF-SUGAR ref:** 009  
**Deps:** `scilib_port_ndarray.md` has `NDArray<Float64>` and element access

Measure:
- `a + Float64(1.0)` on a 1024×1024 `NDArray<Float64>` — does it use `rt_ndarray_broadcast_add` or fall back to an element loop?
- If element loop: measure time for 1024×1024 (1M elements). Compare to the `rt_f64_array_alloc` timing (which is pure C-side alloc): broadcast should be faster since it is alloc + one C-side scalar-add pass.

**Threshold:** if broadcast is implemented via element loop in the interpreter and 1M-element add takes > 500 ms, set status `observed` + P1 for ndarray phase; escalate to ndarray agent. If `rt_ndarray_broadcast_add` extern is already provided, set `fixed`.

**Deliverable:** PERF-SUGAR-009 `Current-cost` filled; status updated.

---

### T-PERFSUGAR-20 — Observe PERF-SUGAR-010: `+=` forces copy-assign for NDArray

**Effort:** 0.5 day  
**Priority:** P2  
**PERF-SUGAR ref:** 010  
**Deps:** `scilib_port_ndarray.md` has basic `NDArray` arithmetic

Measure:
- `a += Float64(1.0)` — does it allocate a new backing buffer or mutate in-place?
- If copy-assign: record allocation count for 100 iterations of `a += x` on a 1024×1024 array (expect 100 full allocs).

**Threshold:** if 100 iterations allocate 100 new 8 MiB buffers (i.e., `a += x` is always copy), set status `observed`. Flag as P1 for v2 augmented-assign generalization (T-PERFSUGAR-26 scope). If in-place mutation already works, set `fixed`.

**Deliverable:** PERF-SUGAR-010 `Current-cost` filled; status updated.

---

### T-PERFSUGAR-21 — Observe PERF-SUGAR-012: false-green process wedge — document and monitor

**Effort:** 0.25 day  
**Priority:** P1 (process)  
**PERF-SUGAR ref:** 012  
**Deps:** None (can run any time)

Review the current test harness (`bin/simple test`) to confirm:
1. There is no `--assert-ran` flag that detects stub-skipped `it` blocks.
2. `--mode=native` and `--mode=smf` are the false-green paths (per `feedback_compile_mode_false_greens`).

Update PERF-SUGAR-012 entry:
- Document which test invocations are safe (interpreter mode via `bin/simple test` with no `--mode` flag).
- Add a note for impl agents: any CI pipeline entry that adds `--mode=native` to a scilib spec must be rejected in review.
- Set status `observed` (not `fixed` — the `--assert-ran` flag does not exist yet).

**Deliverable:** PERF-SUGAR-012 status = `observed`; safety note appended to entry.

---

### T-PERFSUGAR-22 — Observe PERF-SUGAR-013: loop fusion / SIMD gap for element-wise ops

**Effort:** 1 day  
**Priority:** P1 (v2 input)  
**PERF-SUGAR ref:** 013  
**Deps:** `scilib_port_ndarray.md` has basic element-wise indexing

Measure:
- `for i in 0..n: c[i] = a[i] + b[i]` (element-wise add via index loop) for n = 1M elements in interpreter mode.
- Compare to: a hypothetical `rt_array_add_f64(a, b, c, n)` extern (if not yet implemented, estimate from `rt_f64_array_alloc` alloc speed as a lower bound — pure C-side ops are much faster than interpreter dispatch).

Estimate slowdown factor vs NumPy equivalent (reference: NumPy element-wise add on 1M f64 elements is ~1 ms on modern hardware; interpreter dispatch per element will be far slower).

**Threshold:** if element-wise loop in interpreter is > 50× slower than estimated NumPy equivalent, set status `observed` + P1 for v2 design (T-PERFSUGAR-25 scope). This is expected — the observation task's purpose is to record concrete numbers, not to fix the gap in v1.

**Deliverable:** PERF-SUGAR-013 `Current-cost` filled with measured slowdown; status = `observed`.

---

## v2 Tasks — Design Only (No Impl)

These tasks produce design documents, not code. They depend on v1.1 observation data to be grounded in real numbers.

---

### T-PERFSUGAR-23 — Design: math-block kernel fusion pass (PERF-SUGAR-002)

**Effort:** 2 days  
**Priority:** P1  
**PERF-SUGAR ref:** 002  
**Deps:** T-PERFSUGAR-11 (observation data); math-block architecture (`scilib_port_math_block.md` complete)

Write a design note for the v2 kernel-fusion pass in the math-block lowerer. The note must cover:

1. **Pattern detection:** what AST patterns in `MathExpr` constitute a fusable kernel (e.g., `MatMul(A, B)` followed by `Add(result, v)` → single `rt_gemm_add` call).
2. **IR representation:** how the fusion pass represents fused kernels (a new `FusedKernel(op, args)` AST node, or an annotation on existing nodes?).
3. **Intermediate Block suppression:** how the pass eliminates the intermediate `Block` allocations that the v1 lowering creates.
4. **Fallback:** if a pattern is not recognizable as fusable, fall through to v1 lowering (no regression).
5. **Dependency on HIR-lift:** note that this design is only implementable after `math{}` is promoted from a string-payload runtime interpreter to a proper grammar node with HIR sub-tree access (v2 OQ-A path).

The note should be appended to `doc/08_tracking/feature_request/scilib_perf_sugar.md` under PERF-SUGAR-002's `Proposed-sugar` section, or placed in a new file `doc/05_design/math_block_fusion_design.md` if length warrants.

**Deliverable:** Design note written; PERF-SUGAR-002 `Proposed-sugar` field updated with reference.

---

### T-PERFSUGAR-24 — Design: interpreter monomorphization cache (PERF-SUGAR-003)

**Effort:** 2 days  
**Priority:** P1  
**PERF-SUGAR ref:** 003  
**Deps:** T-PERFSUGAR-12 (observation data with boxing ratio measurements)

Write a design note for adding a monomorphization cache to the interpreter. The note must cover:

1. **Cache key:** `(generic_fn_id, [concrete_type_id])` — a pair of the function's stable id and the vector of concrete type arguments at each call site.
2. **Cache value:** a specialized interpreter closure (or pre-evaluated body env) with the concrete type substituted for `T` in all type-checked positions.
3. **Scope:** which generic constructs benefit most — `NDArray<T>` methods, `fn dot<T>`, `Pipeline<Steps>`. Measure T-PERFSUGAR-12 data to prioritize.
4. **Cold path:** if cache miss, fall through to erased-dispatch path; populate cache on first call.
5. **Invalidation:** the cache is per-session (no cross-run persistence); no invalidation needed.
6. **v1 short-term workaround acknowledgment:** document that v1 uses `dot_f64`/`dot_f32` non-generic specializations as a workaround; the monomorphization cache makes those unnecessary in v2.
7. **Risk:** does adding a monomorphization cache touch the interpreter dispatch path broadly? Identify which interpreter files are affected. This is the highest-risk aspect — the cache must not regress non-generic function call overhead.

The note must reference the boxing ratio measured in T-PERFSUGAR-12 to justify the priority.

**Deliverable:** Design note written; PERF-SUGAR-003 `Proposed-sugar` updated with reference.

---

### T-PERFSUGAR-25 — Design: FMA peephole + SIMD loop fusion (PERF-SUGAR-008/013)

**Effort:** 2 days  
**Priority:** P2 (pure-Simple backend gate)  
**PERF-SUGAR ref:** 008, 013  
**Deps:** T-PERFSUGAR-18 (FMA gap confirmed); T-PERFSUGAR-22 (loop-fusion slowdown measured)

Write a combined design note covering two compiler passes:

**Part A — FMA contraction (PERF-SUGAR-008):**
- Cranelift backend peephole: detect `Mul(a, b)` immediately followed by `Add(result, c)` where all operands are `Float64` or `Float32`, and emit a single `fma` Cranelift instruction.
- Opt-in annotation (`#[allow_fma]` or module-level pragma) to signal that IEEE-754 strict semantics may be relaxed (FMA is not bit-identical to separate mul+add under strict IEEE).
- Scope: Cranelift backend only; interpreter has no FMA dispatch.

**Part B — Element-wise loop fusion / autovectorization (PERF-SUGAR-013):**
- Compiler pattern: recognize `for i in 0..n: c[i] = f(a[i], b[i])` where `f` is a binary element-wise op on `Float64`/`Float32` and lower to `rt_array_map2_f64(a, b, c, n, op_id)` (a C-side SIMD loop).
- Alternative: a `vectorize { ... }` block annotation that explicitly marks a body as element-wise vectorizable.
- Longer-term: loop fusion pass — merge two adjacent `for i in 0..n` loops with the same bounds and no aliasing into one pass.
- Scope: both Cranelift and a new `rt_array_map2_*` extern family (one task for the extern, one for the compiler pattern recognition).

**Deliverable:** Design note written referencing measurements from T-PERFSUGAR-18/22; PERF-SUGAR-008 and 013 `Proposed-sugar` fields updated.

---

### T-PERFSUGAR-26 — Design: newtype zero-cost construction + in-place augmented assign (PERF-SUGAR-011/010)

**Effort:** 2 days  
**Priority:** P2  
**PERF-SUGAR ref:** 010, 011  
**Deps:** T-PERFSUGAR-13 (Float64 alloc cost measured); T-PERFSUGAR-20 (in-place += cost measured)

Write a combined design note:

**Part A — Newtype optimization (PERF-SUGAR-011):**
- Compiler optimization: structs with exactly one field of a primitive type (`f64`, `f32`, `i64`, `i32`) are value-inlined — passed in registers, not heap-allocated, at the ABI level. The public API remains typed (no primitive leaks); the optimization is transparent to users.
- Applies to: `Float64`, `Float32`, `Int64`, `Index`, `Scalar<T>` (rank-0 linalg result).
- Implementation scope: interpreter value representation + Cranelift ABI lowering.
- Prerequisite analysis: does the interpreter's `Value` enum already handle primitive-typed struct fields without heap boxing? If yes, the optimization may be partial or free. T-PERFSUGAR-13 data drives priority.

**Part B — In-place augmented assign for NDArray (PERF-SUGAR-010):**
- Extend the augmented-assign sugar (`+=`, `-=`, `*=`, `/=`) to call a user-defined method (`fn iadd(self, rhs: T)`) on the LHS type, rather than desugaring to `lhs = lhs + rhs` (which copies). Pattern established by B4-sugar bitfield augmented assigns (commits `aff5c9f49f`, `df1ea290fd`).
- For `NDArray`: `a += x` lowers to `a.iadd(x)` which calls `rt_ndarray_iadd` extern (mutates buffer C-side, no new allocation).
- Trait-backed `__iadd__` protocol design — how impl agents declare an `iadd` method and how the compiler recognizes it as the augmented-assign target.

**Deliverable:** Design note written; PERF-SUGAR-010 and 011 `Proposed-sugar` fields updated.

---

## Summary

| Wave | Task ids | Count | Description |
|------|----------|-------|-------------|
| v1 (gating) | T-PERFSUGAR-01..10 | 10 | `rt_f{64,32}_array_alloc` + `rt_i{64,32}_array_alloc` impl, whitelist, extern decls, bootstrap rebuild, smoke spec, tracking promotion, AC-6 harness |
| v1.1 (observation) | T-PERFSUGAR-11..22 | 12 | Measure each PERF-SUGAR-002..013 during impl; update tracking entries; flag any that escalate to P0/P1 blockers |
| v2 (design) | T-PERFSUGAR-23..26 | 4 | Fusion-pass design (002), monomorphization cache design (003), FMA+SIMD design (008/013), newtype+iadd design (010/011) |
| **Total** | | **26** | |

**Three highest-risk tasks:**

1. **T-PERFSUGAR-05 (interpreter whitelist)** — a missing whitelist entry causes silent "extern not found" at interpreter runtime (no compile error). This is the most common silent failure mode for new externs in this codebase. If the whitelist step is missed, T-PERFSUGAR-08 (smoke spec) will fail with a confusing error rather than a clear compiler error, and the ndarray agent will be unblocked on a false premise.

2. **T-PERFSUGAR-23 (fusion-pass design)** — the math-block kernel fusion fix for PERF-SUGAR-002 depends on `math{}` being promoted from a string-payload runtime interpreter to a proper grammar node with HIR sub-tree access (v2 OQ-A path, deferred from v1). If the compiler team does not commit to HIR-lift, this design cannot proceed. The risk is that T-PERFSUGAR-23 produces a design that becomes orphaned. Mitigate by including a "feasibility gate" in the note: the design is conditional on HIR-lift being scheduled.

3. **T-PERFSUGAR-24 (monomorphization cache design)** — the monomorphization cache for PERF-SUGAR-003 touches the interpreter's core dispatch path. Risk: a poorly designed cache key or cache miss path regresses non-generic function call performance across the entire interpreter (not just scilib). T-PERFSUGAR-12's boxing ratio measurement is load-bearing: if the ratio is low, the cache is not justified; if high, the cache is justified but must not regress other paths. The design note must include a non-regression test plan.
