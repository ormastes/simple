# SIMD Auto-Vectorization Pass — Design Document

**Wave:** K3
**Date:** 2026-05-02
**Status:** Skeleton shipped; MIR rewriter deferred to Wave L+
**Scope:** `60.mir_opt/mir_opt/auto_vectorize.spl` (K3 additions) + `mod.spl` dispatch arm
**Research inputs:** J1 (`auto_vectorize_survey_2026-05-02.md`), J2 (`cipher_simd_patterns_2026-05-02.md`),
  J3 (`compress_simd_patterns_2026-05-02.md`), J4 (`loop_vectorize_targets_2026-05-02.md`)

---

## §1 Motivation

J1–J4 together make the case that automatic SIMD vectorization is the single highest-leverage
compiler investment for Simple's current workloads.

**From J1 (survey):** Every production compiler — LLVM, GCC, icc, Rust via LLVM — achieves
2–8× throughput improvements on numeric code by transforming scalar loops into SIMD loops at
compile time.  The key insight (J1 §9.3) is that Simple's borrow checker provides aliasing
proofs that LLVM must compute expensively at runtime; this makes Simple's vectorizer cheaper
to build and safer to apply than C/C++ equivalents.

**From J2 (cipher patterns):** The pure-Simple AES and SHA paths are entirely scalar despite the
SIMD round primitive (`simd_aes_round` in `simd.spl:521-543`) existing and being unused.
ChaCha20 XOR loops are byte-by-byte.  An auto-vectorizer that recognises XOR-elementwise and
byte-copy loops immediately benefits all cipher code without source changes.

**From J3 (compression patterns):** CRC32 (in `gzip/crc.spl`), the DEFLATE LZ77 hash step,
and the zstd ANS/FSE normalisation loops are all straight-line arithmetic on contiguous byte
arrays — canonical elementwise and reduction targets.  Vectorizing them would shorten
hot-path compression latency by 2–4×.

**From J4 (loop targets):** The audit identifies 20 high-impact loops across `src/lib/`.
The top 5 by expected speedup are:
- T01 `saxpy` (`y[i] += alpha * x[i]`) — elementwise, 4–8× potential
- T02 dot-product accumulation (`acc += x[i] * y[i]`) — reduction, 4× potential
- T03 `batch_norm_forward` normalize pass (`normalized = (x - mean) * inv_std`) — elementwise
- T04 LU factorization inner update (`lu[i][j] -= lu[i][k] * lu[k][j]`) — elementwise row sweep
- T05 Cholesky inner k-loop (`sum += L[i][k] * L[j][k]`) — reduction

All five are structurally simple (stride-1, no aliasing, no cross-iteration dependencies
other than the induction variable) and are exactly what the K3 pattern matchers target.

---

## §2 Pass Architecture

### 2.1 Existing five-file decomposition (pre-K3 scaffold)

Before K3, the auto-vectorization scaffold comprised five files:

| File | Role |
|------|------|
| `auto_vectorize_types.spl` | Shared types (`LoopInfo`, `ArrayAccess`) — no deps on other AV modules |
| `auto_vectorize_analysis.spl` | Phase 1: def-use chains, dependency detection, array aliasing |
| `auto_vectorize_validate.spl` | Phase 2: vectorizability checks (function calls, control flow, trip count) |
| `auto_vectorize_cost.spl` | Phase 3: cost model (`CostEstimate`), speedup estimation |
| `auto_vectorize_codegen.spl` | Phase 4: vector code generation (`VectorizeContext`, `VectorizedLoop`) |
| `auto_vectorize.spl` | Coordinator: imports all phases, `run_auto_vectorization` entry point |

The existing `run_auto_vectorization` function wires all four phases together but produces
partial/placeholder results because the loop bounds detection (`detect_loop_bounds`) returns
`nil` for all inputs in the current scaffold.

### 2.2 K3 additions

K3 adds to `auto_vectorize.spl`:

- **`VectorRecipe`** struct — the handoff record between pattern recognition and the future
  rewriter.  Contains: `kind`, `header_block`, `induction_var`, `trip_count`, `element_type`,
  `vector_width`, `op_name`, `note`.
- **`VectorRecipeKind`** enum — `Elementwise` | `Reduction`.
- **`mir_pattern_match_elementwise_loop(block) -> VectorRecipe?`** — structural matcher.
- **`mir_pattern_match_reduction(block) -> VectorRecipe?`** — structural matcher.
- **`run_auto_vectorize(module) -> MirModule`** — new entry point (SKELETON: logs recipes,
  returns module UNCHANGED).

K3 also adds the `"auto_vectorize"` dispatch arm to `mod.spl` (after `"predicate_promote"`)
and re-exports the new symbols from `__init__.spl`.

### 2.3 Pipeline position

```
50.mir  (MIR construction)
  ↓
55.borrow  (borrow checker — produces noalias proofs on MirFunction)
  ↓
60.mir_opt:
  dead_code_elimination
  constant_folding
  copy_propagation
  loop_invariant_motion
  predicate_promote          ← M2 / Wave F
  auto_vectorize             ← K3 skeleton; Wave L rewriter
  simd_lowering              ← existing
  ...
```

`auto_vectorize` must run **after** `predicate_promote` (so that zero-fill mask ops have
already been promoted to undef where safe) and **before** `simd_lowering` (which lowers
explicit `FixedVec` / `ScalableVec` MIR ops to backend SIMD — auto-vectorize must emit
those same ops so lowering can handle them uniformly).

`auto_vectorize` must also run **after** the borrow-checker pass (`55.borrow`) has annotated
`MirFunction` with noalias information (see §3.1).  In K3 this is not yet consumed (the
pattern matchers are purely structural), but Wave L must insert the alias oracle call here.

---

## §3 Dependence Analysis

J1 §2 surveys three dependence tests used by production compilers:

- **ZIV** (Zero Induction Variable): neither reference involves the loop index → always or
  never alias, statically decidable.
- **SIV** (Single Induction Variable): one reference moves with the loop index → stride and
  direction are checkable.
- **MIV** (Multiple Induction Variables): both references involve the index → requires
  Banerjee/omega-test reasoning.

Simple needs ZIV + SIV for the loops in J4's top-20.  MIV appears only in matrix operations
with complex subscripts (targets T04, T18, T19) and can be deferred to Wave M+.

### 3.1 Borrow-to-noalias propagation — Simple's free win

J1 §9.3 identifies this as Simple's most important structural advantage:

> **Simple's borrow checker (`55.borrow`) provides a SCEV-equivalent aliasing oracle for free.**

When the borrow checker certifies that two references cannot alias (because they are distinct
owned values or non-overlapping borrows), the auto-vectorizer can skip the ZIV/SIV tests
entirely and proceed directly to vectorization.  LLVM must reconstruct this information via
expensive inter-procedural alias analysis or insert runtime alias checks (loop versioning);
Simple has it at compile time.

**What Wave L must do:** The `55.borrow` pass must be extended to attach a `noalias_pairs`
annotation to each `MirFunction` (or to each pair of `MirLocal` entries).  `auto_vectorize`
reads this annotation during the vectorizability check phase, replacing the conservative
`check_array_aliasing` heuristic in `auto_vectorize_analysis.spl`.

Until Wave L lands, K3's structural matchers conservatively accept loops where the array
bases are different locals (different `LocalId` values for each GEP base).  This is sound
(never vectorizes aliased accesses) but incomplete (misses some safe cases where the alias
proof would enable vectorization).

### 3.2 Loop-carried dependency check

The existing `has_loop_carried_deps` in `auto_vectorize_analysis.spl` performs def-use chain
analysis and conservatively marks any backward dependency as loop-carried.  For stride-1
elementwise loops this correctly identifies zero loop-carried deps (the only carried dep is
the induction variable itself, which is explicitly excluded).

For reduction loops, the accumulator `s` carries a dependency across iterations — this is the
**intended** dependence that the vectorizer exploits via a vector partial-sum tree.  The
reduction matcher in K3 identifies this shape (no stores in body, single accumulating BinOp)
but does not yet verify the carried-value cycle in SSA.  Wave L must add a cycle-check via
def-use chaining.

---

## §4 Cost Model

J1 §3 surveys LLVM's `TargetTransformInfo` (TTI) cost model.  Simple's equivalent is in
`auto_vectorize_cost.spl` (`CostEstimate` struct, `estimate_vectorization_cost`).

### 4.1 VF selection

Candidate vector factors (VF) are powers of two: 1, 2, 4, 8, 16.  The upper bound is
`register_bit_width / element_size_bits`, where `register_bit_width` is queried from
`simd_capabilities.spl` via `SimdFeatureSet`.

The current implementation in `auto_vectorize.spl::get_simd_width` uses a fixed heuristic
(AVX2 = 256-bit registers):
- `f32` → VF = 8
- `f64` → VF = 4
- `i32` → VF = 8
- fallback → VF = 4

Wave L should replace this with a `SimdFeatureSet` query:
```
val features = detect_simd_features()
val reg_bits = if features.has_avx512f: 512
               elif features.has_avx2: 256
               elif features.has_neon: 128
               else: 0
val vf = if reg_bits > 0: reg_bits / element_bits else: 1
```

### 4.2 Trip-count threshold

Per J1 §3 and §7.6, vectorization is not profitable for very short loops.  The threshold is
approximately `2 * VF` iterations.  A loop known at compile time to execute < VF iterations
cannot even fill one vector register and must be left scalar.

The existing `estimate_trip_count` in `auto_vectorize_validate.spl` uses a fixed estimate.
Wave L must integrate SCEV-equivalent trip count analysis (see §3).

### 4.3 Register pressure heuristic

J1 §3 (LLVM TTI): vectorization at VF=8 for `f32` requires 3 vector registers per loop
body iteration (two inputs + one output), plus additional registers for the induction variable
and loop bounds.  On x86-64 with AVX2 (16 YMM registers), this is comfortably within budget
for simple loops.  Complex loops with many temporaries may spill.

Simple's current cost model does not model register pressure.  A simple heuristic for Wave L:
count the number of distinct live vector values at any point in the vectorized loop body.
If the count exceeds `num_vector_regs(features) - 2` (2 reserved for index/bounds), decline
to vectorize or reduce VF.

---

## §5 Idiom Recognition

J1 §5 identifies three idiom classes relevant to Simple's top-20 targets.

### 5.1 Trivial elementwise

Pattern: `out[i] = f(a[i], b[i])` where f ∈ {+, -, *, /, &, |, ^}.

J4 targets: T01 (saxpy), T03 (batch_norm normalize), T04 (LU update), T18 (LU update).
J2 targets: AES AddRoundKey (XOR of 16-byte state with round key).
J3 targets: CRC32 byte loop, zstd/ANS normalisation.

MIR shape (after scalar-to-SSA lowering):
```
GEP(a, i) → Load → %va
GEP(b, i) → Load → %vb
BinOp(op, %va, %vb) → %vc
GEP(out, i) → Store(%vc)
Add(i, 1) → %i_next
```
K3 matcher: `mir_pattern_match_elementwise_loop` detects ≥2 Loads, ≥1 Store, ≥1 non-increment
BinOp, ≥1 Add-with-const (induction increment), no Call.

### 5.2 Reduction (sum / product / max / min)

Pattern: `var s = init; for i: s = s op a[i]`

J4 targets: T02 (dot product), T05 (Cholesky), T17 (Gauss-Seidel), T19 (Cholesky).

MIR shape:
```
GEP(a, i) → Load → %va
BinOp(op, %s_carried, %va) → %s_next  # no Store
Add(i, 1) → %i_next
```
K3 matcher: `mir_pattern_match_reduction` detects exactly 1 non-increment BinOp, ≥1 Load,
0 Stores, ≥1 Add-with-const, no Call.

**FP reduction safety:** As noted in J1 §7.5, FP addition is not associative.  The
reduction rewriter (Wave L) must default to refusing FP reductions unless a `fast_math`
annotation is present on the function.  Integer reductions (sum, product, max, min over
integer types) are safe to reorder.  K3's matcher does not distinguish FP from integer —
the recipe carries `element_type` which Wave L's rewriter checks.

### 5.3 Saturating operations

Pattern: `min(max(a + b, lo), hi)` — maps to `@llvm.sadd.sat` / NEON `vqadd` / SSE2
`paddus` (per J1 §5.2).

J2 targets: image pixel blend, AES S-box boundary clamp.

This idiom is not yet handled by K3.  Wave M should add a `mir_pattern_match_saturating`
matcher that recognises the `min(max(...))` tree and emits a `SimdSatBinOp` recipe kind.

---

## §6 Predication and Tail Handling

J1 §4 surveys three strategies for loop tails (when `n % VF != 0`).

### 6.1 Scalar epilogue (K3 default, Wave L implementation)

The vectorized loop processes `floor(n / VF) * VF` elements.  A scalar cleanup loop
handles the remaining `n % VF` elements.

```
// Vector body
while i + VF <= n:
    simd_load(a, i); simd_load(b, i)
    simd_binop(...)
    simd_store(out, i)
    i = i + VF
// Scalar epilogue
while i < n:
    out[i] = a[i] op b[i]
    i = i + 1
```

This is what `auto_vectorize.spl:13-18` already sketches (per J1 §4.1).  K3's `VectorRecipe`
carries a `trip_count` field so Wave L's rewriter can decide whether to emit the epilogue as
an unrolled scalar block (when `n % VF` is small and known) or a counted loop.

### 6.2 Masked tail (deferred to Wave M, SVE/RVV targets)

Per J1 §4.3, ARM SVE and RISC-V RVV natively support predicated execution.  On these
targets, the rewriter can emit a single masked loop body that handles all iterations including
the tail, using `svld1` / `svst1` with a predicate register.

This is deferred because:
1. K3 does not emit SIMD ops at all.
2. The predicate_promote pass (M2) must land first.
3. `SimdFeatureSet.has_sve` / `.has_riscv_v` must be checked.

### 6.3 Alignment peeling (deferred to Wave M)

Per J1 §4 (LLVM strategy), a prologue scalar loop peels iterations until the first
array pointer is naturally aligned to the vector width.  This improves memory throughput
on non-AVX-512 targets.  Deferred — Wave L uses unaligned loads first; Wave M adds alignment
peeling if performance measurements justify it.

---

## §7 Capability Gating

J1 §9.2 (options matrix row: "Capability gating") and J1 §3 (cost model) both recommend
gating vectorization on `SimdFeatureSet` queries.

`simd_capabilities.spl` exposes `SimdFeatureSet` with fields:
- `has_neon`, `has_neon_fp16`, `has_bf16`, `has_sve`, `has_sve2`, `sve_vector_length`
- `has_avx2`, `has_avx512f`, `has_avx512bw`, `has_avx512vl`
- `has_riscv_v`, `riscv_vlen`
- `is_apple_m` (SVE guard — never set `has_sve` on Apple M, per C1 §6-H)

Wave L's rewriter calls `detect_simd_features()` at vectorization time and:
1. Picks VF based on register width (§4.1).
2. Refuses to vectorize if no SIMD extension is available (`reg_bits == 0`).
3. Chooses between scalar epilogue (SSE2/NEON) and masked tail (SVE/RVV).

**Function multiversioning** (emitting both a vectorized and a scalar version of a function,
selected at runtime by CPUID) is deferred as future work.  It requires a code-size analysis
and a dispatcher stub, and is not needed until the first deployment on heterogeneous fleets.
See J1 §9.2, row "Runtime alias checks / versioning".

---

## §8 Failure Modes

Per J1 §7, the following conditions cause the pass to refuse vectorization.  For each, the
MIR shape that signals the refusal is noted.

| # | Condition | MIR signal | Matcher response |
|---|-----------|-----------|-----------------|
| F1 | **Function call in loop body** | `MirInstKind.Call` or `CallIndirect` present | `call_count > 0` → return `nil` |
| F2 | **Indirect load (gather)** | `GEP` whose base is a `Load` result (index array derefs) | Not yet detected in K3 structural matcher; Wave L must add base-is-load check |
| F3 | **FP reduction without fast-math** | `element_type` is `f32` or `f64` in a `Reduction` recipe | Wave L rewriter checks `element_type` + `has_fast_math` attribute; refuses FP reduction by default |
| F4 | **Recursion / indirect call** | `CallIndirect` | Same as F1 — `call_count > 0` → return `nil` |
| F5 | **Short trip count** | `trip_count < 2 * vector_width` (once SCEV lands) | Wave L: cost check before rewrite; K3: `trip_count == -1` defers to Wave L |
| F6 | **Non-stride-1 access** | GEP with non-unit stride (e.g. `a[2*i]`) | Not yet detected; conservative: K3 accepts all GEPs |
| F7 | **Loop-carried dependency (non-induction)** | Def-use chain crossing iteration boundary | `analyze_loop_dependencies` in `auto_vectorize_analysis.spl`; `dep_result.vectorizable == false` |
| F8 | **No induction variable detected** | No `BinOp(Add, _, Const)` in block | `induction_local == nil` → return `nil` |

K3 enforces F1, F4, and F8 structurally.  F2, F3, F5, F6 are documented here and deferred
to Wave L.  F7 is enforced by the existing `analyze_loop_dependencies` call in
`run_auto_vectorization` (the pre-K3 entry point); Wave L must connect K3's matchers to the
same analysis.

---

## §9 Test Plan

Full regression test corpus: `test/unit/compiler/mir_opt/auto_vectorize_spec.spl`

### Positive cases (pattern returns Some)

| Test | Pattern | J4 target |
|------|---------|-----------|
| `recognises add elementwise loop` | Elementwise / Add | T01 saxpy shape |
| `recognises mul elementwise loop` | Elementwise / Mul | T03 batch_norm multiply |
| `recognised sub elementwise loop` | Elementwise / Sub | T04 LU update (subtract form) |
| `recipe kind is Elementwise for add block` | Kind field check | — |
| `recipe op_name contains add for add block` | op_name field check | — |
| `recognises sum reduction loop` | Reduction / Add | T02 dot-product accumulator |
| `recognises product reduction loop` | Reduction / Mul | T05 Cholesky inner loop |
| `recipe kind is Reduction for sum block` | Kind field check | — |
| `recipe op_name contains add for sum block` | op_name field check | — |
| `recipe vector_width is positive for sum block` | Coherence check | — |

### Negative cases (§8 failure modes → nil)

| Test | §8 code | Failure mode |
|------|---------|--------------|
| `function call in body inhibits elementwise match` | F1 | Call present |
| `function call in body inhibits reduction match` | F1 | Call present |
| `no induction variable inhibits elementwise match` | F8 | No Add-with-const |
| `no array loads inhibits elementwise match` | F2 (partial) | No Load instructions |
| `store in loop body inhibits reduction match` | — | Store → not a register reduction |

### No-op / skeleton safety

| Test | What it checks |
|------|---------------|
| `returns module unchanged on empty module` | Module name preserved |
| `module function count unchanged after pass` | No function added/removed |

### Extended test corpus (Wave L additions — not yet written)

Wave L should add tests for:
- Vectorized output MIR contains `SimdLoad`/`SimdBinOp`/`SimdStore` instructions.
- Scalar epilogue block is present when `n % VF != 0`.
- FP sum reduction is refused without `fast_math` annotation.
- Integer sum reduction is accepted.
- Pass correctly recognises top-5 J4 patterns in compiled mode (verified by `bin/simple desugar`).
- Trip count < 2*VF causes refusal.
- Aliased arrays (same `LocalId` base) cause refusal.

---

## §10 Phased Rollout

### Wave K3 (this wave) — Skeleton

Shipped:
- `VectorRecipe` struct + `VectorRecipeKind` enum in `auto_vectorize.spl`
- `mir_pattern_match_elementwise_loop` (structural, conservative)
- `mir_pattern_match_reduction` (structural, conservative)
- `run_auto_vectorize` entry point — pattern-matches + logs; **returns module UNCHANGED**
- `"auto_vectorize"` dispatch arm in `mod.spl` (after `"predicate_promote"`)
- `__init__.spl` re-exports for `VectorRecipe`, `VectorRecipeKind`, `run_auto_vectorize`
- ≥12 unit tests in `test/unit/compiler/mir_opt/auto_vectorize_spec.spl`

### Wave L (next) — MIR Rewriter

Prerequisites:
1. SCEV-equivalent trip-count analysis (extend `auto_vectorize_analysis.spl`).
2. Alias oracle propagation from `55.borrow` into `60.mir_opt` (see §3.1).
3. `SimdLoad`/`SimdStore`/`SimdBinOp` MIR op variants confirmed in `mir_data.spl`.

Scope:
- `_rewrite_elementwise_loop(func, recipe) -> MirFunction` — emit vector loop + scalar epilogue.
- `_rewrite_reduction_loop(func, recipe) -> MirFunction` — emit vector partial-sum + horizontal reduce.
- FP reduction gate: check `element_type` ∈ {`f32`, `f64`} + `has_fast_math` on `MirFunction`.
- Connect to `SimdFeatureSet` for VF selection (§4.1).
- Enable `run_auto_vectorize` to return a modified module (currently hardcoded no-op).

### Wave M (deferred)

- Saturating-ops idiom recognition (§5.3).
- Masked tail on SVE/RVV targets (§6.2).
- Alignment peeling prologue (§6.3).
- SLP (superword-level parallelism / basic-block vectorization) — J1 §9.2.
- Function multiversioning for heterogeneous CPU fleets (§7).

### MIR Walker Limitation Note

The K3 structural matchers (`mir_pattern_match_elementwise_loop`,
`mir_pattern_match_reduction`) are single-pass instruction counters.  They do NOT:
- Chase def-use chains (required for cycle detection in reductions).
- Verify that GEP bases are distinct (alias check).
- Confirm that the load operands of the data BinOp come from GEPs within the same block.

These limitations are intentional for the skeleton wave.  Wave L must add proper SSA
def-use traversal, which requires either a visitor pattern or a pre-built def-use map.
The existing `build_def_use_chains` in `auto_vectorize_analysis.spl` provides the latter;
Wave L should call it inside the matchers before accepting a recipe.
