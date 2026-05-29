# Compiler Optimization Research — Pure Simple vs. C Runtime Parity

**Date:** 2026-05-18
**Scope:** Identify actionable compiler/JIT optimizations to close the performance gap between
pure Simple and C for string processing, math/hashing, and memory operations.
**Method:** Pipeline audit + existing benchmark evidence + reverted-attempt audit.

---

## 1. Compiler Pipeline Overview

### Compilation layers
```
Simple source (.spl)
  → HIR (high-level IR)  [src/compiler_rust/compiler/src/hir/]
  → MIR (mid-level IR)   [src/compiler_rust/compiler/src/mir/]
      MIR optimizer runs here (self-hosted .spl + Rust driver passes)
  → Cranelift backend    [src/compiler_rust/compiler/src/codegen/cranelift.rs]
       or LLVM backend   [src/compiler_rust/compiler/src/codegen/llvm_jit.rs]
  → Object file → linked binary (mold)
```

### Active MIR optimization inventory (`optimizations/mod.rs`)
| Group | Description |
|-------|-------------|
| Constant folding | Fold constants, simplify arithmetic identities |
| Copy propagation | Propagate copies to expose more cleanup |
| Dead code elimination | Remove unused instructions and dead paths |
| CSE | Eliminate redundant computations across basic blocks |
| Local redundancy | Remove repeated local computations |
| Loop transforms | **Inlining, LICM, loop transforms, outlining, SIMD lowering** (inventory entry — see §3.1 below) |

### MIR inliner (`codegen/mir_inline.rs`) — current limits
- Candidate criteria: `≤ 8 blocks`, `≤ 48 instructions`, **no back-edges**, no generators, no async, not `rt_*`
- Only inlines at single tail-call position in a block
- Supports: ConstInt, ConstBool, Copy, BinOp, Call, MethodCallStatic, LocalAddr, Load, Store, Drop, EndScope

### Cranelift opt levels
- `NativeOptimizationLevel::None` → `"none"`
- `NativeOptimizationLevel::Basic` → `"speed_and_size"`
- `NativeOptimizationLevel::Standard | Aggressive` → `"speed"`
- CPU features flow through `BackendSettings`: x86-64-v3 enables AVX2/BMI1 etc.

---

## 2. Benchmark Evidence — Current Gaps (Phase 6D, open as of 2026-05-13/14)

### Port algorithms harness (`test/perf/port_algorithms/`)
| Algorithm | vs C | vs Rust | Status |
|-----------|------|---------|--------|
| XXHash64  | 0.57x | 0.97x | **Below C — open** |
| CRC32     | 0.88x | 0.88x | Near parity |
| Adler-32  | 0.94x | 0.93x | Near parity |
| ChaCha20  | 1.17x | 1.04x | **Beats both** |

### Collection benchmark (`build/perf/collections/`)
| Operation | vs C | vs Rust | Status |
|-----------|------|---------|--------|
| list_traverse  | 1.52x | 1.29x | Beats both |
| list_push      | 1.32x | 4.50x | Beats both |
| set_contains   | 1.83x | 0.83x | **Below Rust — open** |
| hashset_contains | 0.61x | 1.04x | **Below C — open** |
| hashset_insert   | 0.24x | 1.59x | **Far below C — open** |

**Key observation:** `hashset_insert` is the largest absolute gap (0.24x C). The C reference uses
a fixed-table insert; Simple must close the open-addressed slot scan and fill overhead.

---

## 3. Already Attempted and Reverted — Do Not Re-Propose

The following have been tested and reverted due to benchmark regression:

| Attempt | Outcome |
|---------|---------|
| Raise MIR inliner limits to 16 blocks / 96 instructions + allow returning loop callees | Reverted — `list_traverse` regressed to 0.90x C / 0.73x Rust |
| Allow MIR inliner to inline back-edge callees (without LICM gate) | Reverted — broke `does_not_inline_loop_callees_without_licm` test; call not removed |
| Type-directed `text == text` inline byte-equality in Cranelift codegen | Reverted — `hashset_contains` regressed to 0.55x C |
| Expand `rt_numeric_xor_sum_u64` from 2→4 eight-element chunks per loop | Reverted — `list_traverse` regressed to 0.51x Rust |
| Fold non-float `x == x` / `x != x` in Cranelift codegen | Reverted — did not remove `rt_native_eq(length, length)` guard; `hashset_contains` regressed to 0.59x C |
| Simplify `rt_native_eq` to `!=` tests for string kind | Reverted — `list_push` regressed below C (0.90x) |
| Unroll `rt_array_repeat` store loop by 8 | Reverted — `hashset_insert` ~0.72x Rust, `hashset_contains` ~0.47x C |

---

## 4. Top 5 Actionable Optimization Opportunities

### 4.1 MIR LICM (Loop-Invariant Code Motion) — Highest Leverage for Loop Callees

**Layer:** MIR pass (before Cranelift/LLVM)

**Problem:** The MIR inliner correctly refuses to inline callees that have back-edges without
a LICM gate (see the `does_not_inline_loop_callees_without_licm` test). The optimization
inventory description for "Loop transforms" lists LICM as a group member, but the `mir_inline.rs`
`is_inline_candidate` filter uses `has_back_edge()` as a hard reject. There is no LICM pass that
would hoist invariant values out of loops before the inliner runs, which is what would enable the
loop-callee inlining path without breaking correctness.

**Opportunity:** Implement a true MIR LICM pass that identifies loop-invariant computations
(operands defined outside the loop, no aliased stores) and hoists them into a loop-preheader block.
This would:
1. Enable re-attempting loop-callee inlining for callees whose only loop use is on invariant paths
2. Reduce redundant recomputation in tight traversal loops (relevant for `set_contains`, `list_traverse`)
3. Match what Cranelift's own optimizer cannot do without semantically typed loop structure

**Evidence the pass is missing:** `grep` of `src/compiler_rust/compiler/src/optimizations/mod.rs`
confirms the group is listed by name but the MIR pipeline does not have a dedicated LICM transform
file (unlike `mir_inline.rs` which has its own module).

**Effort estimate:** Medium. Requires dominator tree + natural loop detection on MIR CFG + purity
analysis for hoistable instructions. The dominator tree is likely already available for the CSE pass.

---

### 4.2 Induction-Variable Bounds-Check Elimination — Broader Than Length-Alias

**Layer:** MIR lowering / HIR type analysis

**Problem:** The 2026-05-15 HIR length-alias SIMD guard fix eliminated the specific case where
`array.len().to_u64()` was aliased to a local and used as a `while i < length` bound. The broader
case — where an induction variable `i` is verifiably bounded by `array.len()` via an in-scope
`while i < array.len()` guard — is not yet handled. Every array index `array[i]` inside such a
loop still emits a bounds check at the Cranelift level.

**Opportunity:** Add range/interval analysis at MIR level. Track induction variables whose range
is provably `[0, array.len())` and mark `rt_index_get` / `rt_array_get` calls at those sites as
`trusted` (no-bounds-check path). This directly reduces call overhead in traversal loops.

**Evidence gap:** `set_contains` is still at 0.83x Rust. Its inner loop indexes an array with
a known-bounded induction variable. Cranelift cannot eliminate the bounds check because it does not
see the interval constraint — it only sees an opaque `rt_array_get` call.

**Effort estimate:** Medium-high. Needs interval lattice per VReg, integration with the existing
CSE pass infrastructure, and a new `trusted` annotation on MIR call nodes.

---

### 4.3 `rt_string_eq` Length-Mismatch Fast Path — MIR-Level Short-Circuit

**Layer:** MIR semantic rewrite (not Cranelift codegen — that was reverted)

**Problem:** The 2026-05-15 text array load type fix made `HashSet.insert/contains` call
`rt_string_eq` instead of the generic `rt_native_eq`. However, `rt_string_eq` itself still does a
full-length + memcmp path even for unequal-length strings. The common case in a hash table probe
is string mismatch (different lengths or different first byte).

**Opportunity:** At MIR level (not codegen), rewrite `a == b` where both operands are typed `text`
into a two-step sequence:
1. Emit `rt_str_len(a) != rt_str_len(b)` → branch to `false`
2. Emit `rt_string_eq(a, b)` on the equal-length fallthrough

This is different from the reverted codegen byte-equality fold. It preserves the `rt_string_eq`
call for actual comparison but avoids the call entirely for the common mismatch case. The length
values are already available in the tagged heap layout.

**Impact:** `hashset_contains` probe chain performance — each probe that misses due to length
difference avoids a full string comparison dispatch.

**Effort estimate:** Low-medium. MIR rewrite rule on typed `text == text` BinOp nodes, with a
guard that the rewrite only fires when both operands are heap string VRegs (not literal constants).

---

### 4.4 Tagged-Value Unboxing Within Function Scope for Hot Dispatch

**Layer:** MIR pass — value lifetime analysis

**Problem:** The `rt_native_eq`, `rt_index_get`, and `rt_array_get` runtime calls all accept and
return `Value` (a tagged union). Every call requires re-tagging the return and re-checking the tag
on input. In a tight loop that repeatedly indexes an `Array<text>` or `Array<u64>`, the tag is
constant across all iterations — it is established once from the array's element type and never
changes within the loop body.

**Opportunity:** Add a MIR unboxing pass that, for values with a statically known type in a
bounded scope, replaces the tagged-value `rt_*` dispatch with direct typed calls (e.g.,
`rt_array_get_u64`, `rt_array_get_text`). The typed variants bypass the tag check and can be
emitted as direct loads in Cranelift.

**Evidence:** The 2026-05-15 text array store inline fix replaced `rt_index_set` with `rt_array_set`
for `Array<text>` stores — showing the pattern is effective when the type is known. The unboxing
pass generalizes this to all typed array indexing without requiring per-call-site manual annotation.

**Impact:** `hashset_insert` (0.24x C) — the slot-fill path does `rt_index_set` for each new slot.
`hashset_contains` (0.61x C) — the probe path does `rt_index_get` per probe step.

**Effort estimate:** Medium. Requires type propagation from array declaration site to use sites
within a function. Can reuse MIR type annotation infrastructure from the text-array-store work.

---

### 4.5 XXHash64 — Fixed-Size Byte Buffer Fast Path (No-Bounds u64 Splat)

**Layer:** MIR lowering + Cranelift backend

**Problem:** XXHash64 at 0.57x C is the largest gap in the algorithm harness. Disassembly from
Phase 6C shows the C and Rust compilers inline the entire algorithm into the benchmark `main`
at `-O3`, making the "standalone symbol" comparison point invisible. The Simple version has the
algorithm in a separate function with call overhead and per-byte bounds checks on the 32-byte
working buffer.

**Opportunity:** Two-part fix:
1. **Typed empty `[u8]` capacity heuristic** (partially landed: 1024-byte initial capacity for
   typed `[u8]` locals) — verify this applies to the XXHash64 working buffer and that no realloc
   occurs during the algorithm.
2. **Trusted `[u8]` little-endian read**: the `rt_typed_bytes_u8_at` inline lowering (Phase 6C)
   eliminated explicit unchecked externs. Verify in disassembly that the 8-byte LE u64 read in
   the XXHash inner loop emits a single `mov` + `bswap` (or native LE load) with no bounds check
   — not an `rt_array_get` call. If the bounds check is still present, add an interval annotation
   for the fixed 32-byte working buffer.

**Effort estimate:** Low (verification + targeted annotation) if the typed-bytes lowering is already
landing correctly. Medium if a new fixed-size buffer interval annotation is needed.

---

## 5. Recommended Implementation Order

| Priority | Optimization | Layer | Expected Impact |
|----------|-------------|-------|-----------------|
| 1 | `rt_string_eq` length-mismatch short-circuit (§4.3) | MIR rewrite | hashset_contains, set_contains |
| 2 | Tagged-value unboxing for typed arrays (§4.4) | MIR pass | hashset_insert, hashset_contains |
| 3 | XXHash64 typed-buffer verification (§4.5) | Cranelift verify | XXHash64 |
| 4 | Induction-variable bounds-check elimination (§4.2) | MIR interval analysis | set_contains, list_traverse |
| 5 | MIR LICM pass (§4.1) | MIR pass | Unlocks loop-callee inlining |

Items 1 and 2 are independent and can run in parallel. Item 5 (LICM) is the prerequisite for
eventually re-enabling loop-callee inlining — it is listed last because it is the largest
structural investment and the previous attempt at inlining without it was correctly reverted.

---

## 6. Benchmark Coverage Gap — Base64, Formatting, String Indexing

The user prompt lists base64, formatting, and string indexing as concerns, but **there is no
current microbenchmark for these operations** in `test/perf/`. The collections harness and
algorithm harness (`port_algorithms`) are the only active perf workloads.

Recommendation: Before optimizing these areas, add a string microbench covering:
- Base64 encode/decode (byte scan + lookup table)
- `text` format with mixed types (integer + float + string interpolation)
- UTF-8 string indexing by code point vs. byte

Without a benchmark, optimization changes in these areas risk silent regressions on the active
harnesses without confirming improvement in the target area.

---

## 7. Infrastructure Notes

- **SIMD auto-vectorization:** Cranelift does not have a loop vectorizer. LLVM backend can
  auto-vectorize at `-O3`. For Cranelift builds, SIMD must be emitted explicitly via MIR SIMD
  lowering (the HIR SIMD guard work and `rt_numeric_xor_sum_u64` callsite lowering are the current
  mechanism). The auto-vectorize survey (`doc/01_research/auto_vectorize_survey_2026-05-02.md`)
  covers LLVM LV + SLP + polyhedral — these apply only to the LLVM backend path.
- **Hot optimizer rules stay built-in:** Per `compiler_optimization_infra_refactor_2026-05-13.md`,
  correctness-critical lowering and hot-path semantic rewrites should remain statically linked in
  the release driver, not loaded as dynamic plugins.
- **Benchmark command:** `SIMPLE_NATIVE_CPU=native SIMPLE_BIN=... test/perf/port_algorithms/run_port_algorithm_benchmarks.shs`
  and `test/perf/collections/` (3–5 samples for reliable medians).
