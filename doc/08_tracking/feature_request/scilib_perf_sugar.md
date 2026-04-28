# Scilib Perf-Sugar Wedge Tracker

Tracks compiler and interpreter performance and ergonomics wedges discovered
during the `std.linalg` / `std.ndarray` / `std.df` / `std.ml` port.
Append new entries as you hit them during implementation.

**Scope:** disjoint from Fortran/CUDA ABI (separate sibling file),
Python inventory, math-block spec, naming audit, and Codex risk research.

---

## Schema

| Field | Notes |
|-------|-------|
| Id | `PERF-SUGAR-###`, monotonic |
| Title | verb-led, ≤ 80 chars |
| Filed-on | `YYYY-MM-DD` |
| Filed-by | author / agent / session |
| Priority | `P0` / `P1` / `P2` |
| Status | `anticipated` / `observed` / `fixed` / `wontfix` |
| Expected-repro | minimal API call pattern that exhibits the wedge |
| Current-cost | measured time/allocation, or `unknown — measure during impl` |
| Proposed-sugar | compiler change / stdlib change / extern / `none yet` |

---

## Open Entries

---

### PERF-SUGAR-001 — Typed numeric buffer ctor is O(n²) in interpreter (no rt_typed_alloc)

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P0
- **Status:** anticipated
- **Expected-repro:**
  ```
  let a: NDArray<Float64> = NDArray.zeros(Shape(1024, 1024))
  ```
  Under the hood this calls `.push(Float64(0.0))` in a loop → interpreter
  dispatch per element → O(n²) for large arrays.
- **Current-cost:** unknown — measure during impl. Analogous `[u8]` push-loop cost
  was >30 s for 32 MiB before `rt_bytes_alloc` fixed it (feedback_interpreter_bulk_buffer).
- **Proposed-sugar:** Add `extern fn rt_f64_array_alloc(len: u64) -> [Float64]`
  (and `rt_i64_array_alloc`, `rt_f32_array_alloc`) that zero-fill C-side, matching
  the `rt_bytes_alloc` pattern. Alternatively, a generic
  `rt_typed_array_alloc<T>(len: u64, default: T) -> [T]` extern if the compiler
  can monomorphize it.
- **Notes:** `rt_bytes_alloc` fixed the `[u8]` case (B2, 2026-04-25). The typed
  numeric case has no equivalent yet. This is the top blocking wedge for ndarray.

---

### PERF-SUGAR-002 — math{} block allocates a new Block value per expression, no fusion

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P0
- **Status:** anticipated
- **Expected-repro:**
  ```
  let c = math { A @ B + v }
  ```
  If the compiler lowers each operator in `math{}` to a separate intermediate
  `Block` allocation (matmul result, then add result), hot linalg loops pay
  O(k) heap allocations for k operators.
- **Current-cost:** unknown — measure during impl. math{} spec says each block
  is "a self-contained DSL expression that returns a Block value"; lowering
  strategy not yet documented.
- **Proposed-sugar:** Kernel-fusion pass in the math-block lowerer: detect
  `A @ B + v`-class patterns and lower to a single fused `rt_gemm_add` extern
  call (BLAS-style combined kernel), suppressing intermediate Block allocs.
  Alternatively, expression-tree capture deferring allocation to the outermost
  `let` binding.
- **Notes:** Analogous to the O(n²) concat-in-loop problem fixed by StringBuilder
  across rich_text/report/office (commits de423c7957, d70015731a, 0100347c06).
  Linalg ops are in hot inner loops, so allocation cost compounds severely.

---

### PERF-SUGAR-003 — Generic <T> dispatch is erased/boxed in interpreter; no monomorphization

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P0
- **Status:** anticipated
- **Expected-repro:**
  ```
  fn dot<T>(a: NDArray<T>, b: NDArray<T>) -> T { ... }
  dot(x, y)   // T=Float64
  ```
  In interpreter mode, generic instantiation goes through erased dispatch
  (dynamic value boxing) rather than specialised monomorphs. For tight
  numeric loops the boxing overhead dominates.
- **Current-cost:** unknown — measure during impl. No monomorphization pass
  exists in the interpreter path; Cranelift backend does specialize but
  interpreter mode is required by AC-7 (feedback_compile_mode_false_greens).
- **Proposed-sugar:** (a) Interpreter-side monomorphization cache: generate a
  specialized interpreter closure for each concrete `<T>` instantiation seen
  at call sites, keyed by type-id. (b) Short-term stdlib workaround: provide
  non-generic `dot_f64`, `dot_f32` specializations alongside generic facade.
- **Notes:** This is a blocking wedge for all of `std.linalg` / `std.ndarray`
  in interpreter-mode testing (required by AC-7). Cranelift mode is not a valid
  substitute (feedback_compile_mode_false_greens: compile-mode can produce
  false-green test results).

---

### PERF-SUGAR-004 — FFI extern call overhead per BLAS operation; no call batching

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P1
- **Status:** anticipated
- **Expected-repro:**
  ```
  for i in 0..n:
      let y_i = blas_ddot(a_i, b_i)   // one extern call per row
  ```
  Each `extern fn` crossing pays interpreter dispatch + marshalling overhead
  (~50–200 ns per call at FFI boundary, per text_encoding_engine SIMD
  crossover benchmark estimate). For n=1000 inner-loop BLAS calls the cost
  becomes measurable.
- **Current-cost:** unknown — measure during impl. FFI crossover threshold
  estimated at 64–512 bytes from text_encoding SIMD study (OQ-1).
- **Proposed-sugar:** (a) Batch extern: `rt_blas_dgemm_batch(ops: [GemmOp])`
  to coalesce multiple BLAS calls into one FFI crossing. (b) Compiler: detect
  `extern fn` call in a `for` loop body and emit a batch-call desugaring if
  the extern declares `#[batchable]`. Neither exists yet.
- **Notes:** The FFI overhead is acceptable for large matrix ops (BLAS level-3),
  but becomes a wedge for BLAS level-1 (axpy, dot) in vectorized loops over
  many small vectors (common in DataFrame column operations).

---

### PERF-SUGAR-005 — No stride-aware typed slice view; ndarray slicing copies data

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P1
- **Status:** anticipated
- **Expected-repro:**
  ```
  let row = A[i, ..]        // expected: O(1) view, not O(cols) copy
  let col = A[.., j]        // column slice with stride != 1
  ```
  Simple's current slice (`[lo..hi]`) is contiguous and does not carry a
  stride field. NDArray column slices and non-contiguous views require either
  a copy or a wrapper struct that tracks `(ptr, len, stride)` — but no
  built-in stride-view type exists.
- **Current-cost:** unknown — measure during impl. Likely O(n) copy per slice
  vs the desired O(1) view.
- **Proposed-sugar:** Add `StridedView<T>` stdlib type backed by
  `(ptr: *T, len: i64, stride: i64)` with index sugar `view[i]` lowering to
  `ptr[i * stride]`. Compiler: allow `NDArray[i, ..]` to return `StridedView`
  without copying. Alternatively, a `rt_strided_view_alloc` extern that creates
  a view struct C-side.
- **Notes:** NumPy slicing is always O(1) via strides; without this, all
  ndarray column operations become O(n), blocking any pandas-style column-
  oriented DataFrame implementation.

---

### PERF-SUGAR-006 — String/Symbol column names in DataFrame have no intern table

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P1
- **Status:** anticipated
- **Expected-repro:**
  ```
  df.select(["revenue", "cost", "profit"])
  df.groupby("region")
  ```
  Each string column name is a heap-allocated `String`; equality checks in
  `select` and `groupby` are O(len) string compares rather than O(1) pointer
  compares. For DataFrames with many columns or repeated groupby the cost
  accumulates.
- **Current-cost:** unknown — measure during impl.
- **Proposed-sugar:** Add `Symbol` type to stdlib (interned string, pointer-
  equal if content-equal) backed by a process-global `rt_intern_symbol(str)`
  extern that returns a stable `u64` id. Column names, schema keys, and
  groupby keys should use `Symbol`. A lighter alternative: a
  `SymbolTable` struct local to each DataFrame schema, avoiding global state.
- **Notes:** Pandas uses Python's intern mechanism implicitly; Simple's pure
  type system needs an explicit Symbol primitive or a stdlib-level SymbolTable.

---

### PERF-SUGAR-007 — Iterator protocol (yield/generator) is materialized in interpreter

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P1
- **Status:** anticipated
- **Expected-repro:**
  ```
  for group in df.groupby("region"):
      agg(group)
  ```
  If `groupby` uses a generator/yield protocol, each `yield` in interpreter
  mode materializes a full group copy rather than yielding a view. For a
  DataFrame with 10M rows and 1000 groups this means 1000 allocations of
  ~10K-row sub-DataFrames.
- **Current-cost:** unknown — measure during impl.
- **Proposed-sugar:** (a) Lazy groupby: return an iterator of `(key, RowRange)`
  pairs rather than materialized sub-DataFrames; the aggregation function
  operates on a range-backed view. (b) Compiler: detect `for x in expr` where
  `expr` is a known-lazy iterator and avoid intermediate materialization
  (analogous to `for x in s.chars()` → `for x in s` desugar, commit
  b88b8aa6c7).
- **Notes:** This is a stdlib design choice as much as a compiler feature;
  record it here so the arch phase picks the lazy-range design from the start.

---

### PERF-SUGAR-008 — No fused-multiply-add (FMA) sugar; a*b+c emits two ops

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P1
- **Status:** anticipated
- **Expected-repro:**
  ```
  let r = a * b + c    // Float64 scalar or NDArray element
  ```
  The compiler emits a multiply then an add; no FMA contraction pass exists.
  In compiled (Cranelift) mode this may miss hardware FMA instructions on
  AVX2/AVX-512. In interpreter mode there is no FMA dispatch anyway.
- **Current-cost:** unknown — estimate 2× ops vs native FMA on float-heavy code.
- **Proposed-sugar:** Compiler peephole: contract `a * b + c` → `rt_fma(a,b,c)`
  when all operands are `Float64` or `Float32`, and the Cranelift backend emits
  `fma` instruction. Requires `#[allow_fma]` or similar annotation to opt in
  (IEEE-754 strict vs. relaxed semantics choice).
- **Notes:** Low priority relative to P0 wedges but critical for BLAS-level
  performance in the pure-Simple backend once that lands.

---

### PERF-SUGAR-009 — No broadcast sugar for scalar op on NDArray; forces element loop

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P2
- **Status:** anticipated
- **Expected-repro:**
  ```
  let b = a + Float64(1.0)    // broadcast add scalar to all elements
  let c = a * Float64(2.0)    // broadcast multiply
  ```
  Without operator overloading or math-block lowering that detects scalar
  broadcasting, user code must write an explicit element loop, which in the
  interpreter is O(n²) if it re-allocates the result array per iteration.
- **Current-cost:** unknown — measure during impl.
- **Proposed-sugar:** Operator overloading on `NDArray<T>` for `+`, `*`, `-`, `/`
  with `T`-typed RHS; lowered to a single `rt_ndarray_broadcast_add` extern that
  runs the operation C-side. The math-block lowerer should additionally detect
  `A + scalar` patterns and emit the broadcast extern rather than an element loop.
- **Notes:** NumPy broadcasting is one of its most-used ergonomic features.
  Without it, the Simple surface is significantly more verbose than NumPy.

---

### PERF-SUGAR-010 — No in-place mutation sugar for NDArray (+=, *=); forces copy-assign

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P2
- **Status:** anticipated
- **Expected-repro:**
  ```
  a += Float64(1.0)    // expected: in-place mutate, no alloc
  ```
  Without augmented-assign lowering for `NDArray`, `a += x` desugars to
  `a = a + x` which allocates a full result copy. In-place numeric mutation
  is required for iterative algorithms (gradient descent, power iteration).
- **Current-cost:** unknown — measure during impl. bitfield augmented assigns
  were added in B4-sugar (commits aff5c9f49f, df1ea290fd) showing the pattern
  is feasible but not yet generalized to user-defined types.
- **Proposed-sugar:** Extend augmented-assign sugar (`+=`, `-=`, `*=`, `/=`) to
  call a user-defined `fn iadd(self, rhs: T)` method when the LHS is not a
  primitive, lowering to in-place extern (`rt_ndarray_iadd`) rather than
  copy-assign. Matches the B4-sugar bitfield pattern.
- **Notes:** Feasibility confirmed by B4-sugar Phase 2 (aff5c9f49f). Needs
  generalization to trait-backed `__iadd__` protocol.

---

### PERF-SUGAR-011 — Wrapper-type construction overhead: Float64(x) allocates per-element

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P2
- **Status:** anticipated
- **Expected-repro:**
  ```
  NDArray.from_list([Float64(1.0), Float64(2.0), ... 1M items ...])
  ```
  Each `Float64(x)` wrapper construction may allocate a heap object in the
  interpreter if wrapper structs are not value-inlined. For a 1M-element
  array construction this is 1M allocations before any array work begins.
- **Current-cost:** unknown — measure during impl.
- **Proposed-sugar:** Compiler: value-inline single-field numeric wrapper structs
  (structs containing exactly one `f64`/`i64`/etc field) so they are passed
  in registers and not heap-allocated. This is the "newtype optimization" — the
  wrapper has zero cost over the raw primitive at the ABI level while preserving
  the no-primitive-in-public-API rule.
- **Notes:** Without this optimization the no-primitive rule imposes a 1M-alloc
  tax on every large array literal. The optimization is a prerequisite for the
  no-primitive design being practical at scale.

---

### PERF-SUGAR-012 — Interpreter-mode compile-mode false greens: linalg tests invisible

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P1
- **Status:** anticipated
- **Expected-repro:**
  ```
  bin/simple test src/lib/linalg/gemm_spec.spl --mode=native
  # → PASSED (stub-generated, not actually run)
  ```
  `--mode=native` stub-generation no-ops unresolved `std.spec` calls;
  `--mode=smf` swallows runtime errors. Both report PASSED even when the
  test body never executed (feedback_compile_mode_false_greens).
- **Current-cost:** Silent false greens — the risk is undetected failures, not
  wall-clock time.
- **Proposed-sugar:** AC-7 mandates interpreter mode; this entry is a reminder
  that all scilib specs must run under `bin/simple test` (interpreter mode)
  and any attempt to switch to `--mode=native` for speed is a cover-up.
  Long-term fix: a test-runner flag `--assert-ran` that fails the suite if
  any `it` block body was stub-skipped.
- **Notes:** Tracked here as a process wedge, not a perf wedge, because it
  will recur whenever a sibling agent tries to speed up CI by switching modes.

---

### PERF-SUGAR-013 — No for-loop fusion / autovectorization for element-wise array ops

- **Filed-on:** 2026-04-27
- **Filed-by:** scilib-port research agent
- **Priority:** P1
- **Status:** anticipated
- **Expected-repro:**
  ```
  for i in 0..n:
      c[i] = a[i] + b[i]    // element-wise add, no SIMD, no fusion
  for i in 0..n:
      c[i] = c[i] * alpha   // second pass, could be fused with first
  ```
  Plain `for i in 0..n` loops over array indices are not recognised as
  vectorizable or fusable by the interpreter or Cranelift backend. Each loop
  is a separate interpreter-dispatch pass; two adjacent element-wise loops
  cannot be merged into one. Hardware SIMD (AVX2/AVX-512) is never emitted
  from Simple source.
- **Current-cost:** unknown — measure during impl. Conservative estimate: 2–8×
  slower than equivalent numpy/numba for element-wise ops on large arrays
  (no SIMD, no loop fusion).
- **Proposed-sugar:** (a) Compiler: recognise `for i in 0..n: c[i] = f(a[i], b[i])`
  patterns and lower to a single `rt_array_map2_f64` extern (C-side SIMD loop).
  (b) Longer-term: a `vectorize { ... }` block or `#[simd]` annotation that
  signals the compiler to emit SIMD code for the body via Cranelift's SIMD
  instruction set. (c) Loop fusion pass: merge two adjacent loops with the same
  bounds and no aliasing into one. None of these exist yet.
- **Notes:** Analogous to the `for x in s.chars()` → `for x in s` desugar
  (commit b88b8aa6c7) which eliminated per-character dispatch overhead. The
  ndarray analogue is per-element-index dispatch. Without this, all user-written
  element-wise loops are scalar and single-threaded; for large arrays this is
  the dominant runtime cost after buffer allocation is fixed (PERF-SUGAR-001).

---

### PERF-SUGAR-014 — Extern registration sites: prefix-dispatch precedent vs explicit-table assumption

- **Title:** runtime extern dispatch path uses prefix-pattern matching, not an explicit symbol table
- **Filed-on:** 2026-04-27
- **Filed-by:** observed during T-PERFSUGAR-01 implementation
- **Priority:** P2 (documentation / contributor onboarding)
- **Status:** observed (not a wedge — clarifies prior assumption)
- **Expected-repro:**
  ```
  # Adding a new rt_* extern. Plan said: 3 sites — runtime fn,
  # registration in runtime_symbols.rs, interpreter-dispatch arm.
  grep -rn 'rt_bytes_alloc' src/compiler_rust/common/src/runtime_symbols.rs
  # → empty: rt_bytes_alloc is NOT registered in runtime_symbols.rs.
  ```
  The "registration table" model (assumed in `scilib_port_perf_sugar.md`
  T-PERFSUGAR-01..05) does not match reality for the `rt_*` extern family.
  `runtime_symbols.rs` uses prefix-based dispatch (e.g. anything starting
  with `rt_` is recognised); only the interpreter-extern dispatch in
  `interpreter_extern/mod.rs` needs an explicit arm.
- **Current-cost:** zero runtime cost; only contributor-confusion cost.
  An agent following the plan literally will look for a registration site
  that does not exist, then either invent one (buggy), grep for siblings
  and discover the absence (10 min of confusion), or escalate.
- **Proposed-sugar:** (a) Update `scilib_port_perf_sugar.md` T-PERFSUGAR-01..05
  to describe 2 sites (decl + dispatch), not 3. (b) Optional: add a one-line
  comment near the prefix-dispatch in `runtime_symbols.rs` saying "rt_* is
  prefix-matched here; per-symbol registration NOT required". (c) Same
  observation likely applies to `xtra_*`, `__rt_*`, and any other prefix-
  matched extern family.
- **Notes:** Surfaced by T-PERFSUGAR-01 implementation (committed in
  `4dba2d4f4b`). The agent's "if the precedent is structurally different,
  STOP and report" rule worked: instead of inventing a registration site,
  the agent surfaced the discrepancy. Lesson for future task plans:
  cross-check assumed file lists against actual `grep` output for the
  precedent symbol before blessing the plan.
