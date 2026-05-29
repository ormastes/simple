# Scilib Port — Perf and Ergonomic Wedges Research

**Scope:** Compiler and interpreter performance wedges that will affect
`std.ndarray`, `std.linalg`, and `std.df` implementation. This file is
disjoint from the Fortran/CUDA ABI, Python inventory, math-block spec,
naming harmony, and Codex risk sibling research files.

**Tracking file:** `doc/08_tracking/feature_request/scilib_perf_sugar.md`
(append new entries there as they are observed during implementation).

---

## 1. Background: How Wedges Are Identified in This Codebase

The Simple compiler currently operates in two primary modes:

1. **Interpreter mode** — the tree-walking interpreter used for all `bin/simple test` runs. Required by AC-7 and by the `feedback_compile_mode_false_greens` constraint: both `--mode=native` and `--mode=smf` produce false-green test results, so interpreter mode is the only trustworthy verification path during development.

2. **Cranelift (compiled) mode** — the self-hosted codegen backend. Used for production builds and bootstrap. The recent Cranelift right-shift bug (FR-DRIVER-0002b, fixed 2026-04-18) shows that the Cranelift path is still maturing.

Historical perf work in this codebase establishes a clear pattern: the dominant wedge class is **O(n²) allocation inside loops** — the String concat-in-loop problem that drove the `StringBuilder` migration across rich_text, report, office, browser_engine, and UI modules (commits de423c7957, d70015731a, 0100347c06, cd33847ae5, 3626c8c73e, 96f240adb9). For scientific computing, the analogous problem is **O(n²) numeric buffer construction** and **per-expression intermediate allocation in hot math expressions**. The `rt_bytes_alloc` extern added in B2 (2026-04-25) is the direct precedent: replacing an interpreter-dispatch push loop with a single C-side allocation reduced 32 MiB construction from "never completes" to 1.5 s.

---

## 2. Wedge Catalogue

Twelve wedges are seeded in `scilib_perf_sugar.md`. They divide into three
tiers by implementation phase impact.

### 2.1 P0 — Block v1 without these

**PERF-SUGAR-001: Typed numeric buffer ctor is O(n²) in interpreter**

`NDArray.zeros(Shape(1024, 1024))` must not construct its backing buffer with
a push loop. The `[u8]` analogue was catastrophic (>30 s for 32 MiB); `[f64]`
will be no better. No `rt_f64_array_alloc` or `rt_typed_array_alloc` extern
exists yet. Without it, every ndarray constructor is unusable in interpreter
mode for any matrix larger than a few hundred elements. This is the most
immediate blocker for the ndarray implementation phase.

**PERF-SUGAR-002: math{} block allocates an intermediate Block per operator**

The `math{}` DSL spec states each block is "a self-contained DSL expression
that returns a Block value." If `A @ B + v` lowers to (matmul → Block₁, add
→ Block₂), the hot linalg expression `C = alpha * A @ B + beta * C` (the
BLAS dgemm pattern) allocates four intermediate Block values per call. This
is the exact O(n) allocation-per-concat pattern the StringBuilder migration
fixed for text. The fix for linalg is kernel fusion: detect `A @ B + v`
patterns in the math-block lowerer and emit a single `rt_gemm_add` extern
call. Without this, math-block-expressed linalg is slower than hand-written
extern calls — undermining the math-block ergonomic goal.

**PERF-SUGAR-003: Generic <T> dispatch is erased in interpreter**

`NDArray<Float64>` and `fn dot<T>` are the foundation of the entire scilib
API surface. In interpreter mode, generic instantiation goes through erased
dynamic dispatch (value boxing) rather than type-specialised monomorphs. This
means every element access in a tight numeric loop pays a boxing/unboxing
overhead. The Cranelift backend specialises generics, but Cranelift mode
produces false-green test results for unresolved spec symbols. The practical
consequence: scilib in interpreter mode will be materially slower than
necessary, and AC-7 requires interpreter mode. A monomorphization cache in
the interpreter (keyed by concrete type-id) or hand-written `Float64`/`Float32`
specialisations in the stdlib are the two mitigation paths.

### 2.2 P1 — Significant friction if unaddressed

**PERF-SUGAR-004: FFI extern call overhead per BLAS operation**

BLAS level-1 operations (dot, axpy, scal) are typically called in inner loops
over many small vectors — common in DataFrame column operations and iterative
solvers. Each `extern fn` crossing in the interpreter pays dispatch and
marshalling overhead. The text encoding SIMD crossover study (text_encoding_engine.md
OQ-1) estimates FFI call overhead at 50–200 ns, with a crossover threshold
around 64–512 bytes. For 128-element float vectors this means FFI overhead
can dominate compute. A batch-call mechanism (`rt_blas_axpy_batch`) or a
compiler desugaring that coalesces `extern fn` calls inside a `for` loop body
would address this.

**PERF-SUGAR-005: No stride-aware typed slice view**

NumPy slicing is O(1) through strides. Simple's current slice (`lo..hi`) is
contiguous and carries no stride. NDArray column slices (`A[.., j]`),
transposed views, and sub-matrix windows all require non-unit strides. Without
a `StridedView<T>` type, every column slice is an O(n) copy. This blocks
efficient DataFrame column implementation (a DataFrame is column-oriented by
definition) and any algorithm that operates on matrix rows and columns
separately (LU decomposition, QR, iterative refinement).

**PERF-SUGAR-006: String column names in DataFrame have no intern table**

DataFrame `select`, `groupby`, and `join` operations identify columns by
string names. Without an interning mechanism, equality checks are O(len) heap
string compares rather than O(1) pointer compares. At 100+ column DataFrames
with repeated groupby queries this accumulates. A `Symbol` type (backed by
`rt_intern_symbol`) or a per-DataFrame `SymbolTable` is needed. The stdlib
`std.common.text` module does not currently provide this.

**PERF-SUGAR-007: Iterator protocol materializes full groups in groupby**

If `df.groupby("region")` yields sub-DataFrames via a generator/yield protocol,
the interpreter will materialize a full copy of each group. For 10M rows / 1000
groups that is 1000 full allocations before the first aggregation runs. The
correct design is a lazy iterator of `(key, RowRange)` — the aggregation
function then operates on a range-backed view into the original column buffers.
This is an architectural decision for the DataFrame design phase, not a
compiler fix; it is recorded here so the design phase picks the lazy-range
path from the start. The precedent is the `for x in s.chars()` → `for x in s`
desugar (commit b88b8aa6c7), which eliminated materialization for character
iteration.

**PERF-SUGAR-012: Interpreter false-greens as a process wedge**

Not a runtime-performance issue but a testing correctness wedge that will
recur throughout the scilib implementation: any attempt to switch tests to
`--mode=native` for speed is a cover-up (feedback_compile_mode_false_greens).
A future `--assert-ran` test-runner flag that fails if any `it` block body
was stub-skipped would close this permanently.

### 2.3 P2 — Important for polish and pure-Simple backend

**PERF-SUGAR-008** (FMA sugar), **PERF-SUGAR-009** (broadcast sugar),
**PERF-SUGAR-010** (in-place `+=` for NDArray), and **PERF-SUGAR-011**
(newtype/wrapper-type zero-cost construction) are deferred to P2. They are
not blocking for a first working implementation but will determine whether
the Simple scilib surface is ergonomically competitive with NumPy and whether
the eventual pure-Simple backend can achieve native-speed arithmetic.

PERF-SUGAR-011 in particular is architecturally important: if `Float64(x)`
allocates a heap object in the interpreter, then the no-primitive-in-public-API
rule imposes a 1M-alloc tax on every large array literal. The newtype
optimization (value-inline single-field numeric wrapper structs) is a
prerequisite for the no-primitive design being practical at scale.

---

## 3. Relationship to Recent Compiler Work

The five most recent perf commits (de423c7957 through 0100347c06) all follow
the same pattern: identify an O(n²) allocation loop, replace it with a
linear-time primitive (StringBuilder). The scilib port will require the same
discipline applied to numeric buffers and math-block intermediate values.

The `mimalloc` port (03bab53646, bf6195a4da) reduces allocation cost in the
interpreter for small objects but does not eliminate O(n²) dispatch-loop
allocations; it changes the constant factor, not the asymptotic class.

The B4-sugar bitfield augmented-assign work (aff5c9f49f, df1ea290fd) is the
direct precedent for PERF-SUGAR-010 (NDArray `+=`): the compiler already
knows how to lower augmented assigns to in-place mutation for bitfield fields.
Generalizing this to trait-backed `__iadd__` is incremental work.

---

## 4. Top-3 Wedges Likely to Block v1

Based on the analysis above, the three wedges most likely to block a working
v1 if not addressed before or during the implementation phase are:

1. **PERF-SUGAR-001 (typed numeric buffer ctor)** — Without `rt_f64_array_alloc`
   or equivalent, no NDArray larger than a few hundred elements can be
   constructed in interpreter mode. Every spec in AC-4 will time out. This
   needs to land before ndarray skeleton work begins.

2. **PERF-SUGAR-003 (generic <T> erased dispatch)** — The entire scilib public
   API is built on `NDArray<T>`, `Series<T>`, and `fn dot<T>`. If generic
   instantiation in the interpreter is uniformly erased/boxed, the interpreter-
   mode performance will be too slow to run spec suites. This either requires
   an interpreter monomorphization cache or a deliberate decision to ship
   non-generic `_f64`/`_f32` specializations alongside generic facades for v1.

3. **PERF-SUGAR-002 (math{} intermediate Block allocation)** — If the
   math-block lowering strategy allocates one Block per operator, the ergonomic
   `math { A @ B + v }` syntax will be slower than writing the extern calls by
   hand. This undermines the core design constraint (math-block cooperation) and
   will force workarounds that conflict with AC-7's no-cover-up rule.

---

## 5. Scope Notes

This file covers compiler and interpreter wedges only. The following topics are
handled in sibling research files and must not be duplicated here:

- Fortran/CUDA Fortran ABI and binding strategy
- Python (NumPy / pandas / sklearn) surface inventory
- math-block grammar and spec details
- naming harmony and namespace conflict audit
- Codex risk assessment
