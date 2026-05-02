# Auto-Vectorization in Production Compilers: A Survey

**Wave J — J1 research document**
**Date:** 2026-05-02
**Scope:** How production compilers automatically apply SIMD; option space for Simple's MIR pipeline.

---

## Table of Contents

1. [§1 Taxonomy](#1-taxonomy)
2. [§2 Dependence Analysis](#2-dependence-analysis)
3. [§3 Cost Model](#3-cost-model)
4. [§4 Predication and Tail Handling](#4-predication-and-tail-handling)
5. [§5 Idiom Recognition](#5-idiom-recognition)
6. [§6 ISA Capability Detection and Function Multiversioning](#6-isa-capability-detection-and-function-multiversioning)
7. [§7 Failure Modes](#7-failure-modes)
8. [§8 Pure-Functional and Value-Semantics Languages](#8-pure-functional-and-value-semantics-languages)
9. [§9 Option Space for Simple's MIR](#9-option-space-for-simples-mir)

---

## §1 Taxonomy

Auto-vectorization is not a single technique; production compilers employ at least five structurally distinct approaches. Understanding the taxonomy is prerequisite to evaluating applicability.

### 1.1 Loop-Level Vectorization (LV)

Loop-level vectorization widens scalar loop iterations across SIMD lanes. A loop body that processes one element per iteration is transformed to process `VF` (vectorization factor) elements per iteration using a single vector instruction.

**LLVM Loop Vectorizer (LV):** LLVM's primary vectorizer. Enabled by default at `-O2` and above in Clang. It operates on the LLVM IR after the loop canonicalization and scalar evolution (SCEV) passes have run.
- Entry point: `LoopVectorizationPass` (source: `llvm-project/llvm/lib/Transforms/Vectorize/LoopVectorize.cpp`).
- The vectorizer operates in two phases: (a) legality analysis — determine whether the loop *can* be vectorized (alias, trip count, induction variable structure, supported operations); (b) profitability analysis via cost model — determine whether vectorization is *beneficial* at each candidate VF.
- Source reference: LLVM Documentation, "Auto-Vectorization in LLVM," https://llvm.org/docs/Vectorizers.html

**GCC Tree-SSA Vectorizer:** GCC's vectorizer was implemented as a tree-SSA pass starting with GCC 4.1. Enabled by `-ftree-vectorize`, active by default at `-O3`. Uses `cfgloop.c` / `cfgloopanal.c` for loop CFG analysis and the `tree-ssa-loop-vect.c` pass for the actual transformation.
- Activation flags: `-ftree-vectorize` (explicit), or `-O3` (implicit). Target-dependent flags also required: `-msse2` on x86, `-maltivec` on PowerPC.
- Source reference: GCC Project, "Auto-vectorization in GCC," https://gcc.gnu.org/projects/tree-ssa/vectorization.html
- Floating-point reductions additionally require `-ffast-math` or `-fassociative-math` to reorder FP additions legally. This is a design decision that matters for Simple (see §7).

### 1.2 SLP (Superword-Level Parallelism) / Basic-Block Vectorizer

SLP vectorization identifies independent scalar operations *within a basic block* that operate on adjacent memory and can be combined into a single vector instruction. This is complementary to loop-level vectorization: LV widens iterations, SLP widens isomorphic instruction groups within one iteration.

**LLVM SLP Vectorizer:** Processes code bottom-up, across basic blocks, searching for scalars to combine. The canonical example is `A[0] = a1*(a1+b1); A[1] = a2*(a2+b2)` — two structurally identical expressions operating on adjacent data, combinable into a vector multiply-add.
- The SLP vectorizer is enabled by default; can be disabled with `-fno-slp-vectorize`.
- Works in conjunction with LV; often fires on code that LV's loop analysis misses (e.g., short fixed-size loops unrolled by the front end, struct-of-arrays vs. array-of-structs patterns).
- Source reference: LLVM Documentation, "The SLP Vectorizer" section, https://llvm.org/docs/Vectorizers.html#slp-vectorizer

**GCC Basic-Block SLP (BB SLP):** Added to GCC in 2009. Enabled by `-ftree-slp-vectorize`, also enabled by default at `-O3`. The implementation in `tree-ssa-slp.c` performs the same bottom-up matching.
- Supports vectorization of reduction cycles in SLP (2011 addition per the GCC vectorization history page).
- Source reference: GCC Project, "Auto-vectorization in GCC — Basic Block SLP," https://gcc.gnu.org/projects/tree-ssa/vectorization.html#slp

### 1.3 VPlan IR (LLVM)

VPlan is LLVM's intermediate representation layer *within* the loop vectorizer, introduced to make vectorization candidates explicit and comparable. Before VPlan, LLVM's LV constructed candidate VF/UF configurations by directly mutating IR speculatively; VPlan makes these candidates explicit data structures that can be analyzed and compared without IR mutation.

**VPlan components** (source: https://llvm.org/docs/VectorizationPlan.html):
- `LoopVectorizationPlanner`: Constructs, optimizes, and evaluates one or more `VPlan` instances, each representing a distinct vectorization candidate (different VF, different UF, scalar fallback).
- `VPlan`: A model of one candidate. Uses a Hierarchical CFG where nodes are `VPBasicBlock` or `VPRegionBlock` instances. Carries a graph of `VPRecipe` nodes encoding what IR to emit.
- `VPRecipe`: A recipe for producing output IR instructions. Examples: `VPWidenRecipe` (widens a scalar instruction), `VPReductionPHIRecipe` (reduction phi node), `VPInterleaveRecipe` (interleaved load/store group).
- Cost estimation operates on the VPlan graph before any IR is emitted, allowing the cost model to compare candidates cleanly.
- Current status (LLVM 23.0.0git): VPlan now drives code generation entirely for LV; VPlan-based analyses are used for transformations including redundant-recipe removal and active-lane-mask introduction.
- Source reference: LLVM Documentation, "Vectorization Plan," https://llvm.org/docs/VectorizationPlan.html

### 1.4 Polyhedral Vectorization (Polly / GCC GraphIte)

Polyhedral vectorization operates at a higher level of abstraction than SSA-based LV. The polyhedral model represents loop nests as integer polyhedra and uses integer linear programming (ILP) to find optimal loop transformations including tiling, fusion, and vectorization.

**Polly (LLVM-based):** An LLVM pass plugin. Its pipeline:
1. `polly-canonicalize`: Prepare IR for SCoP (Static Control Part) detection.
2. `polly-detect`: Identify regions of the CFG that form valid SCoPs (affine loop bounds, affine array subscripts, no function calls, no irregular control flow).
3. `polly-scops`: Build the polyhedral model using the `isl` (Integer Set Library) library.
4. `polly-dependences`: Compute exact dependences in the SCoP.
5. `polly-opt-isl`: Optimize using Pluto-style algorithms for loop tiling and outer-loop vectorization.
6. `polly-codegen`: Emit LLVM IR from the polyhedral schedule.
- Source reference: Polly LLVM Project, "The available LLVM passes," https://polly.llvm.org/documentation/passes.html

**Key distinction from LV:** Polly handles *outer-loop* and *loop-nest* vectorization, tile shapes, and data locality simultaneously. LLVM's LV handles *inner-loop* vectorization of individual loops. The two are complementary; Polly can emit code that LLVM's LV then further vectorizes.

**When polyhedral is needed:** When the loops have complex iteration-space transformations required for access pattern regularity (e.g., transposed matrix multiply, stencil computation with shifting access). Polly requires SCoP qualification — loops with data-dependent bounds or irregular control flow will be rejected by `polly-detect`.

### 1.5 Idiom Recognition

A separate class of optimization: recognizing entire loop nests as known idioms and replacing them with optimized library calls or specialized instructions. This fires *before* and *independently of* LV/SLP.

Examples (LLVM `lib/Transforms/Scalar/LoopIdiomRecognize.cpp`):
- `memset`, `memcpy`, `memmove` idiom recognition: loops that write a constant or copy consecutive bytes → replaced by runtime calls which themselves may be SIMD-optimized.
- `strlen` idiom: loop over bytes until zero → replaced by a call or inline SIMD sequence.
- Popcount idiom: loop that counts set bits → replaced by `llvm.ctpop`.
- Right-shift + and pattern → recognized as byte-reverse or byte-select operations on some targets.

GCC has an equivalent: `vect_recog_*` functions in `tree-ssa-loop-vect.c` recognize patterns like `WIDEN_SUM`, `DOT_PROD`, `SAD` (sum of absolute differences), `WIDEN_MULT`, and widening shifts — all mapped to specialized target instructions when available.

### 1.6 LLVM Sandbox Vectorizer (Experimental)

LLVM 18+ includes the Sandbox Vectorizer, an experimental framework for building modular vectorization pipelines on top of Sandbox IR — a transactional layer over LLVM IR that enables rollback of transformations.

The key design innovations over the classical LV:
- **Transactional IR:** Each internal pass can commit its state to IR directly. Rollback is cheap. This enables end-to-end profitability decisions across multiple transformation passes without the "commit early, find it unprofitable later" problem of the legacy LV.
- **Modular internal pass pipeline:** Each vectorization transformation (e.g., bottom-up SLP, interleave group formation) is an independent internal pass testable in isolation with lit-tests.
- **Callback interface:** The IR modification system fires callbacks on changes, eliminating manual bookkeeping across the pipeline.

Current status: Not enabled by default. Must be invoked explicitly via `opt -p=sandbox-vectorizer file.ll`. Default pipeline implements a simple SLP-style bottom-up vectorization.
- Source reference: LLVM Documentation, "The Sandbox Vectorizer," https://llvm.org/docs/SandboxVectorizer.html

This experimental design is relevant as a reference architecture: it explicitly solves the "commit-then-regret" problem that makes classical vectorizers complex to maintain and extend. Simple's four-file split (`analysis` / `validate` / `cost` / `codegen`) has a similar modular intent but without transactional rollback.

---

## §2 Dependence Analysis

Correctness of vectorization depends entirely on proving (or assuming) the absence of loop-carried dependences on loop-variant data. This is the hardest part of auto-vectorization in practice.

### 2.1 Scalar Evolution (SCEV) — LLVM

LLVM's `ScalarEvolutionAnalysis` (`-scalar-evolution` pass) is the foundation for loop analysis in LV. SCEV represents loop-variant values as closed-form mathematical expressions over the loop induction variable, parameterized by symbolic loop-invariant values.

- SCEV recognizes patterns: `{start, +, step}` (affine recurrence), `{start, +, step, ...}` (polynomial), and special cases like `AddRec` nodes for phi nodes.
- Trip count computation: Given loop bounds and step, SCEV can compute the trip count as a SCEV expression, which may or may not be a compile-time constant.
- Alias analysis integration: `scev-aa` (`ScalarEvolution`-based alias analysis) tests whether two pointer expressions with known SCEV forms can alias. It is *more complete* than `BasicAliasAnalysis` for pointer arithmetic because it can reason about stride-1 vs stride-N accesses.
- Source reference: LLVM pass documentation, "`scalar-evolution`: Scalar Evolution Analysis," https://llvm.org/docs/Passes.html#scalar-evolution

**What production does:** Even with SCEV, many alias relationships cannot be proven statically because pointers are function arguments. The LV falls back to **runtime checks** (see §2.3).

### 2.2 GCC Dependence Testing

GCC uses the `ddg` (data dependence graph) infrastructure built in `tree-data-ref.c` and `tree-affine.c`. For each pair of memory references in the loop, GCC applies:
1. **ZIV test** (Zero Induction Variable test): If neither reference involves the loop induction variable, they either always alias or never alias.
2. **SIV test** (Single Induction Variable): One reference moves with the loop; statically checkable for stride and direction of dependence.
3. **MIV test** (Multiple Induction Variables): Both references involve the induction variable; requires full Banerjee/omega-test reasoning.

When a dependence *cannot be disproven statically*, GCC either (a) inserts runtime loop versioning (two copies of the loop, one with vectorized path guarded by a runtime alias check), or (b) refuses to vectorize.
- Source reference: GCC Project, "Auto-vectorization in GCC," https://gcc.gnu.org/projects/tree-ssa/vectorization.html (loop versioning added 2007-08-16)

### 2.3 Runtime Guards (Loop Versioning)

Both LLVM and GCC use *loop versioning* as the primary safety mechanism for statically-unresolvable aliasing:

```
// Generated structure (pseudo-code):
if (/* overlap check: do [a, a+n) and [b, b+n) overlap? */) {
    // scalar fallback
    for i in 0..n: c[i] = a[i] + b[i];
} else {
    // vectorized path (no aliasing guaranteed)
    for i in 0..n step VF: ...
}
```

LLVM's LV generates these overlap checks as `llvm.noalias.decl` + `llvm.assume` or direct pointer arithmetic comparisons. The cost model accounts for the overhead of these checks — if the loop body is very short, the guard overhead may dominate.

**LLVM `__restrict__` / `noalias`:** When the programmer annotates pointers with `__restrict__` (C99) or the IR carries `noalias` attributes, LLVM elides the runtime checks and proceeds directly to vectorization. This is the difference between "vectorizes at `-O3`" and "vectorizes at `-O2`" for many real loops.

### 2.4 Pointer Aliasing Assumptions

Intel ICC/oneAPI's classical behavior (documented in the "Vectorization Essentials" guide) aggressively assumes non-aliasing for arguments absent explicit restrict, more aggressively than GCC or Clang/LLVM in older versions. This is what `#pragma ivdep` (ignore vector dependences) makes explicit: it is an *assertion by the programmer* that no cross-iteration dependencies exist. Incorrect use of `ivdep` is undefined behavior.

Modern Clang equivalent: `#pragma clang loop vectorize(assume_safety)` or `__builtin_assume(!...)`.
- Source reference: LLVM Documentation, "Pragma loop hint directives," https://llvm.org/docs/Vectorizers.html#pragma-loop-hint-directives

### 2.5 Interleaved Access Groups

A special case in dependence analysis: consecutive accesses from multiple loop iterations may be loaded simultaneously using a strided vector load. GCC detects strided accesses (the `STRIDED` access classification in `tree-data-ref.c`) and can use ARM NEON `vldN`/`vstN` interleaving instructions where the stride matches the instruction's built-in interleave factor.

LLVM's LV builds `InterleaveGroup` objects for memory accesses whose addresses form an arithmetic sequence. An interleaved group of 4 accesses at stride 4 can be loaded with a single `VLD4` (NEON) or equivalent, obtaining the AoS → SoA transform for free at the hardware level.

**Practical reality:** Interleaved access vectorization is hardware-specific. `VLD2`/`VLD4` on NEON and `VPERM2F128` + `VSHUFPS` sequences on AVX2 require careful cost modelling. The LV TTI interface has `getInterleavedMemoryOpCost(Opcode, VecTy, Factor, Indices, Alignment, AS)` to evaluate whether the interleaved form is profitable.
- Source reference: LLVM Documentation, "Auto-Vectorization in LLVM — Interleaved memory accesses," https://llvm.org/docs/Vectorizers.html

### 2.6 Dependency Distance and Safe Vectorization Width

When a loop-carried dependence *does* exist but has a known distance `d` (e.g., `a[i] = a[i-2] + b[i]` has distance 2), vectorization is still legal if the vector width `VF <= d`. The dependence distance acts as an upper bound on VF.

LLVM's SCEV can compute dependence distances for affine array subscripts. GCC's `compute_data_dependence_in_loop` function returns dependences classified by distance. When distance is known and `VF <= d`, both compilers will vectorize at that constrained VF.

This case is important for signal-processing filters (FIR/IIR) where small distances (2–8) are common. A VF of 2 on SSE2 (128-bit / 2 doubles) is often profitable despite the distance constraint.

---

## §3 Cost Model

The decision to vectorize is not binary. Production compilers use multi-factor cost models to determine the *vectorization factor* (VF), the *unroll/interleave factor* (UF), and whether to vectorize at all.

### 3.1 LLVM Cost Model

LLVM's `TargetTransformInfo` (TTI) interface provides the cost model abstraction. Key factors queried:

| Factor | TTI query | Notes |
|--------|-----------|-------|
| Vector instruction cost | `getInstructionCost(Inst, VectorTy)` | Returns a numeric cost in "target recip throughput units" |
| Register pressure | `getNumberOfRegisters(ClassID)` | How many vector regs available without spilling |
| VF feasibility | `isLegalToVectorizeLoadChain` / `isLegalToVectorizeStoreChain` | Whether memory ops at this width are legal |
| Interleave groups | `getInterleavedMemoryOpCost` | Cost of gather/scatter vs stride-1 load |
| Scalarization cost | `getScalarizationOverhead` | Cost to extract scalars from a vector |

The LV iterates over candidate VF values (powers of two from 1 to `getRegisterBitWidth()/element_size`) and picks the VF with the lowest estimated cost per element.

**Trip count threshold:** LLVM's cost model will refuse vectorization if the estimated trip count is below a minimum threshold. The threshold is computed as approximately `2 * VF` iterations to amortize the overhead of vectorization (loop versioning checks, scalar prologue/epilogue). With very short loops (< 8 iterations known at compile time), LV typically declines.
- Source reference: LLVM Documentation, "The Loop Vectorizer — Cost Model," https://llvm.org/docs/Vectorizers.html

**Partial unrolling (interleaving):** The LV separately optimizes the interleave factor (UF). Even at VF=4, using UF=2 means the loop body processes 8 elements per iteration, exposing more ILP for the CPU's multiple execution units. The cost model weighs register pressure against ILP gain.
- Source reference: LLVM Documentation, "Partial unrolling during vectorization," https://llvm.org/docs/Vectorizers.html#partial-unrolling

### 3.2 GCC Cost Model

GCC added its cost model infrastructure in mid-2007 (`tree-vect-loop.c`). The GCC cost model:
- Uses target hooks: `TARGET_VECTORIZE_BUILTIN_VECTORIZATION_COST(type_of_cost, vectype, misalign)` — returns cost of scalar/vector statements including memory-access misalignment penalty.
- `TARGET_VECTORIZE_PREFERRED_VECTOR_ALIGNMENT(type)` — preferred alignment for a vector of this type; may differ from ABI alignment.
- Chooses VF based on the preferred SIMD width: `UNITS_PER_SIMD_WORD / element_size`.
- Source reference: GCC Internals, "Vectorization," https://gcc.gnu.org/onlinedocs/gccint/Vectorization.html

### 3.3 Register Pressure vs. Vector Width

Wider vectors (AVX-512: 512-bit) have higher throughput per instruction but create more register pressure and may cause frequency throttling on Intel Skylake/Ice Lake due to AVX-512 power limits. Production compilers know this:

- LLVM's TTI for `x86_64` will sometimes prefer AVX2 (256-bit) over AVX-512 for loops with high register pressure or when the target CPU has known throttling behavior (e.g., `-mcpu=skylake-avx512` vs `-mcpu=icelake-server`).
- GCC applies similar target-specific cost corrections in `config/i386/i386.c`.

This is distinct from legality: *legally*, AVX-512 could be used; *profitably*, AVX2 may produce faster code for certain loop shapes.

### 3.4 VF Selection Algorithm in Practice

The VF selection loop in LLVM's LV (from `LoopVectorize.cpp`) works approximately as follows:

```
for VF in [1, 2, 4, 8, 16, ...] up to max_legal_VF:
    if not TTI.isLegalToVectorize(VF, loop): continue
    cost_VF = estimate_vector_cost(loop, VF) / VF   // cost per element
    if cost_VF < best_cost:
        best_VF = VF
        best_cost = cost_VF

if best_VF == 1 and no_epilogue_needed:
    skip vectorization  // not profitable
```

The division by VF normalizes to "cost per scalar equivalent element" — this is how LV compares VF=4 vs VF=8 fairly. A VF that requires expensive scalarization of some operations may have higher per-element cost than a lower VF despite processing more elements per iteration.

**Scalable vectors (SVE, RVV):** For ISAs with variable-length SIMD (ARM SVE, RISC-V RVV), VF is not a compile-time constant. LLVM represents this as `vscale * N` (a symbolic multiple of the hardware-determined vector length). The cost model must reason about expected `vscale` based on target hints. GCC similarly uses `poly_uint64` for vector widths in its SVE/RVV codegen to handle the symbolic scaling.
- Source reference: LLVM Documentation, "Vectorization Plan — VF and UF handling," https://llvm.org/docs/VectorizationPlan.html

### 3.5 Cranelift Baseline

Cranelift (used by Wasmtime, and optionally by `rustc` as an experimental backend) has **no documented auto-vectorization pass**. Its IR supports vector types (e.g., `i32x4`, `f32x4`) as first-class types for explicit use by frontends — notably WebAssembly SIMD128 (`wasm32` target) — but the compiler does not auto-vectorize scalar loops.

This is an explicit design choice consistent with Cranelift's goals: fast compilation (JIT use case), correctness, and security over aggressive optimization. Cranelift has been measured at ~2% slower than V8 (TurboFan) and ~14% slower than LLVM on common benchmarks, partly due to the absence of aggressive loop optimizations.
- Source reference: Cranelift main page, https://cranelift.dev/; Cranelift IR Reference, https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/docs/ir.md

---

## §4 Predication and Tail Handling

When loop trip counts are not multiples of VF, the compiler must handle the *tail* — the remaining elements after the last full-width vector iteration. Three strategies exist:

### 4.1 Scalar Epilogue (Most Common)

The vectorized loop processes `floor(n / VF) * VF` elements. A scalar cleanup loop handles the remaining `n % VF` elements. This is what LLVM LV does by default and what Simple's `auto_vectorize.spl:13-18` sketches:

```
while i + 8 <= n:    // vector body
    ...
while i < n:          // scalar remainder
    c[i] = a[i] + b[i]
```

Cost: Two loops, a conditional branch. Small tail (< VF elements) is usually acceptable overhead.

### 4.2 Loop Peeling / Prologue

Peel the first `k` iterations to align the primary pointer (where `k = (align - base % align) % align`). Used when alignment is important and the hardware penalizes unaligned loads. GCC's vectorizer generates peeling code for alignment when `TARGET_VECTORIZE_VECTOR_ALIGNMENT_REACHABLE` returns true.
- Source reference: GCC Internals, "Vectorization — `TARGET_VECTORIZE_BUILTIN_MASK_FOR_LOAD`," https://gcc.gnu.org/onlinedocs/gccint/Vectorization.html (the `REALIGN_LOAD` mechanism).

### 4.3 Predicated (Masked) Execution

Rather than a scalar epilogue, the tail iteration runs in masked vector mode. Active lanes are determined by a mask:

```
mask = (i + [0..VF-1]) < n    // which lanes are active
masked_load  a[i..i+VF]  under mask
masked_store c[i..i+VF]  under mask
```

This enables a *single loop body* that handles all iterations including the tail.

**LLVM VP (Vector Predication) Intrinsics:** LLVM 15+ introduced the `@llvm.vp.*` family of intrinsics and the `llvm.get.active.lane.mask` intrinsic specifically for this purpose:

```
declare <4 x i1> @llvm.get.active.lane.mask.v4i1.i32(i32 %base, i32 %n)
```

Semantics: `m[i] = (base + i) < n`. Used by the LV to create active-lane masks for tail iterations and for scalable vector targets (SVE, RVV) where VF is not a compile-time constant.
- Source reference: LLVM Language Reference, "'`llvm.get.active.lane.mask.*`' Intrinsics," https://llvm.org/docs/LangRef.html#llvm-get-active-lane-mask-intrinsics

**ARM SVE / RISC-V RVV:** These ISAs natively support predicated execution with hardware predicates/masks. On SVE targets, LLVM's LV prefers the masked single-loop form over scalar epilogues because the hardware handles tail masking at zero cost.

**Trade-off:** Masked execution requires masked load/store instructions (e.g., `vpmaskmov` on AVX-512, `svld1` on SVE). On platforms without hardware masking (SSE2, NEON baseline), masked execution degenerates to scalar scalarization overhead, making the scalar epilogue cheaper.

---

## §5 Idiom Recognition

### 5.1 Reduction Patterns

Reductions (sum, min, max, product, logical AND/OR across array) are a critical vectorization target because they appear in essentially every numeric workload.

**Challenge:** A naive reduction `sum += a[i]` has a loop-carried dependence on `sum`. It cannot be vectorized as-is without *changing the associativity of floating-point addition*, which alters the numerical result.

**LLVM approach:**
- Integer reductions: Always safe to vectorize (integer addition is associative). LLVM generates `VF` partial sums into a vector register, then uses `llvm.vector.reduce.add` intrinsic to horizontally reduce at the end.
- FP reductions: Require `-ffast-math` or the `llvm.experimental.vector.reduce.fadd` intrinsic with `reassoc` fast-math flag. LLVM 14+ introduced explicit FP reduction intrinsics: `llvm.vector.reduce.fadd`, `llvm.vector.reduce.fmax`, `llvm.vector.reduce.fmin`.
- Source reference: LLVM LangRef, "Vector Reduction Intrinsics," https://llvm.org/docs/LangRef.html (search `llvm.vector.reduce`)

**GCC approach:** Added reduction support in GCC 4.1 (sum, min/max). Extended to double-reduction (two nested loops) in 2009. `-fassociative-math` enables FP sum reductions.
- Source reference: GCC Vectorization Project history, https://gcc.gnu.org/projects/tree-ssa/vectorization.html

### 5.2 Saturating Operations

Many image processing operations require saturating arithmetic (clamp to 0..255 rather than wrapping). SSE2/NEON have native `paddus` / `vqadd` instructions.

LLVM recognizes the idiom `min(max(a + b, 0), 255)` and maps it to `@llvm.sadd.sat` / `@llvm.uadd.sat` intrinsics, which lower to native saturating instructions where available. GCC similarly recognizes saturating patterns via optab matching.

### 5.3 Popcount

`__builtin_popcount(x)` in GCC and `llvm.ctpop` in LLVM IR are single intrinsics that lower to `POPCNT` (SSE4.2) or a Hamming-weight computation sequence. The loop pattern `for i: sum += bit_i(x)` may or may not be recognized as a popcount depending on the compiler.

GCC's `vect_recog_popcount_pattern` (added in GCC 5) explicitly recognizes the loop idiom and maps it to `POPCOUNT` or a vectorized bit-count sequence.

### 5.4 Byte Shuffle and Permute

`vpshufb` (SSSE3), `vtbl` (NEON), `vperm` (AltiVec) perform byte-level permutation with a table vector. These are critical for LUT-based operations (e.g., AES S-box, base64 encoding).

LLVM recognizes `shufflevector` IR nodes and maps them to target-specific permute instructions. The SLP vectorizer can sometimes combine individual byte extractions into a single shuffle.

### 5.5 Gather and Scatter

Indirect indexed loads `a[idx[i]]` require gather instructions (`vgatherdps` on AVX2). These are only beneficial when the stride is irregular; regular strided access should still use strided loads.

LLVM's LV detects indirect loads and checks `isLegalMaskedGather` (TTI). If gather is legal and the cost model judges it profitable (typically only with AVX2/AVX-512; NEON has no native gather), it emits gather instructions. Otherwise, the loop is scalarized at the indirect load.

GCC added gather/scatter support via `STRIDED` access classification in `tree-data-ref.c`, using NEON `vldN`/`vstN` for strided but regular patterns.

### 5.6 SAD (Sum of Absolute Differences)

Critical for video encoding (motion estimation). SSE2 has `psadbw`. GCC's `vect_recog_sad_pattern` recognizes:
```
for i: sum += abs(a[i] - b[i])
```
and maps to `PSADBW` (unsigned 8-bit) when types match.
- Source reference: GCC Vectorization history, "widening-summation, dot-product, SAD" patterns, https://gcc.gnu.org/projects/tree-ssa/vectorization.html

### 5.7 Dot Product and Widening Multiply

`WIDEN_MULT` (multiply narrower type to wider result) and `DOT_PROD` (multiply-accumulate across lanes) are recognized by GCC's pattern detection. ARM NEON `vmlal` and x86 `pmaddwd` implement these natively.
- Source reference: GCC Vectorization history, "vectorization of idioms that involve type conversion," https://gcc.gnu.org/projects/tree-ssa/vectorization.html

---

## §6 ISA Capability Detection and Function Multiversioning

### 6.1 Compile-Time Target Selection

The simplest approach: the compiler targets a fixed ISA baseline at compile time (`-march=x86-64-v3` = AVX2; `-march=x86-64-v4` = AVX-512). All vectorization is for that baseline. Portable binaries must use the lowest common denominator.

Clang/GCC support `-march=native` to auto-detect the compilation host's ISA features. Useful for single-machine builds; unsuitable for distributed software.

### 6.2 Function Multiversioning (FMV)

GCC and Clang support `__attribute__((target_clones("avx512f", "avx2", "default")))` to generate multiple versions of a function, one per ISA variant, with a resolver that selects the correct version at load time using `CPUID`-derived capabilities stored by `glibc`'s `ifunc` mechanism.

Example (from GCC/Clang):
```c
__attribute__((target_clones("avx512f+avx512vl", "avx2", "sse4.2", "default")))
void process_array(float *a, int n) { ... }
```
The linker generates an IFUNC resolver; at program startup, `glibc`'s ELF dynamic linker evaluates CPU features and patches the PLT entry to point to the appropriate version.

**ARM ACLE FMV:** ARM's Architecture Compatibility Layer Extensions define `__attribute__((target_version("sve2")))` and `__attribute__((target_clones(...)))` for AArch64, following the same IFUNC pattern.
- Source reference: ARM ACLE Specification, "Function Multi Versioning," https://arm-software.github.io/acle/main/acle.html (cited in Simple's ISA survey)

### 6.3 Intel ICC / oneAPI Auto-Dispatch

Intel's classic ICC (now `icx` in the oneAPI toolkit) provides:
- `#pragma ivdep`: Assert no cross-iteration dependences. Compiler proceeds to vectorize without runtime alias checks.
- `#pragma vector aligned`: Assert all pointer accesses in the loop body are aligned to the natural vector width. Eliminates misalignment peeling.
- `#pragma omp simd`: OpenMP 4.0+ SIMD directive, standardized cross-vendor way to assert loop vectorizability and optionally specify vector length, linear variables, and reduction clauses. Supported by ICC, GCC, and Clang.
- Source reference: OpenMP 5.2 Specification, "2.11.4 simd Construct," https://www.openmp.org/spec-html/omp-4.5/openmp-4.5-html.html (public standard)

ICC also performs *automatic* CPU dispatch using profile-directed feedback (PGO) and static analysis of the CPU family at target time. The Intel Vectorization Advisor (part of oneAPI VTune) can annotate why loops were or were not vectorized.

The OpenMP `simd` construct (standardized in OpenMP 4.0, extended through 5.2) provides a cross-vendor portable way to annotate loops for vectorization:

```c
#pragma omp simd reduction(+:sum) safelen(8)
for (int i = 0; i < n; i++) {
    sum += a[i] * b[i];
}
```

Key clauses:
- `safelen(N)`: Declares that there are no loop-carried dependences shorter than N iterations — equivalent to asserting `VF <= N` is safe.
- `simdlen(N)`: Requests a specific vector length (may be ignored by compiler).
- `linear(v:step)`: Declares variable `v` increments by `step` each iteration (induction variable hint).
- `reduction(op:var)`: Declares a reduction variable and its associative operator.
- Source reference: OpenMP 5.2 Specification, §2.11.4, https://www.openmp.org/wp-content/uploads/OpenMP-API-Specification-5-2.pdf

### 6.4 Runtime CPUID Detection Pattern

The typical portable pattern (without IFUNC):
```c
// At startup:
cpuid features = read_cpuid();
fn_ptr = features.avx512f ? impl_avx512 : features.avx2 ? impl_avx2 : impl_scalar;
// At call site:
fn_ptr(args);
```

This is what `System.Numerics.Vector<T>` in .NET uses: `Vector.IsHardwareAccelerated` is a runtime boolean that RyuJIT specializes on at JIT time (not load time).

### 6.5 .NET RyuJIT and System.Numerics.Vector\<T\>

.NET's JIT compiler (RyuJIT) performs vectorization at JIT-compile time, which has a key advantage over AOT: the JIT *knows* the exact CPU it is running on and can select the best ISA without IFUNC overhead.

`System.Numerics.Vector<T>` is a hardware-width vector: `Vector<T>.Count` is determined at JIT time based on SIMD register width (4 for `float` on SSE2, 8 for `float` on AVX2). Code that uses `Vector<T>` gets optimal instructions for the runtime CPU.

.NET 9 additions (source: https://learn.microsoft.com/en-us/dotnet/core/whats-new/dotnet-9/runtime):
- Arm64 multi-register load/store vectorization for `EncodeToUtf8` (reduces execution time by >50% on ARM64).
- Expanded intrinsics coverage for AVX-512 (`Vector512<T>` operations in `System.Runtime.Intrinsics.X86`).
- RyuJIT now emits explicit `vpternlogd` (AVX-512 ternary logic) in cases where three-input boolean operations appear.

`System.Runtime.Intrinsics.X86` namespace provides direct ISA intrinsics (`Avx2.Gather`, `Sse42.Crc32`, etc.), analogous to `<immintrin.h>` in C.
- Source reference: Microsoft Learn, "Use SIMD-accelerated numeric types," https://learn.microsoft.com/en-us/dotnet/standard/simd

**RyuJIT auto-vectorization vs. explicit SIMD:** RyuJIT does perform some loop auto-vectorization (especially in .NET 8+) for simple patterns over `Span<T>`. However, the primary production path for SIMD in .NET is explicit: library code in `System.Private.CoreLib` manually uses `Vector<T>`, `Vector128<T>`, or `Vector256<T>` for hot paths (string operations, array search, cryptography). The JIT's auto-vectorizer is present but less relied upon compared to LLVM's LV, because the JIT compile time budget is tighter.

This represents an interesting design choice that parallels Simple's current state: explicit SIMD via intrinsic types (`FixedVec<T,N>`) may deliver earlier results than full auto-vectorization because the analysis cost is zero — the programmer has already expressed vector intent.

---

## §7 Failure Modes

Auto-vectorization famously fails to trigger. The most common inhibitors follow. This section distinguishes what *production systems document* vs. what is merely *good advice from blogs*.

### 7.1 Unknown Pointer Aliasing (Most Common)

**What production does:** LLVM inserts a runtime alias check if the alias relation is unknown. If the cost model determines the check overhead exceeds the vectorization benefit (very short loops), it skips vectorization. GCC behaves similarly.

**Real failure:** When pointer arguments have no `noalias`/`__restrict__` annotation AND the loop body is short, the combined cost of runtime check + scalar path + vectorized path *exceeds* the scalar-only cost. The LV then declines.

GCC diagnostic (with `-ftree-vectorizer-verbose=2`):
```
vect-1.c:82: note: not vectorized, possible dependence between data-refs a[i] and a[i]
```
- Source reference: GCC Project, "Auto-vectorization in GCC — Using the Vectorizer," https://gcc.gnu.org/projects/tree-ssa/vectorization.html

### 7.2 Complex or Irreducible Control Flow

Loops with multiple exit conditions, mid-loop `break` statements, or loops where the control flow is not reducible to a simple preheader/latch structure fail loop detection.

LLVM's `LoopSimplify` pass normalizes many common patterns (multiple exits, non-canonical induction), but irreducible CFG or exception-handling paths in the loop body will cause LV to decline.

GCC's `cfgloop.c` handles similar normalization but has the same structural limitations.

### 7.3 Indirect Loads Without Gather Support

`a[idx[i]]` — an indirect load with a dynamically computed index — cannot be vectorized as a strided load. It requires either:
(a) A hardware gather instruction (AVX2 `vgatherdps`, AVX-512 `vgatherdps`), or
(b) Scalarization (each element extracted individually), which is usually slower than scalar.

On targets without gather (SSE2, most NEON), the LV detects `isLegalMaskedGather = false` from TTI and declines to vectorize the loop.

### 7.4 Function Calls in Loop Body

Any call to an opaque function (not inlined) in the loop body prevents loop vectorization because:
- The function may read/write memory (unknown alias effects).
- The function may have side effects that must occur in scalar order.
- The vector equivalents of the function may not exist.

Exception: Known *vectorizable function calls* — math intrinsics (`sin`, `exp`, `log`) can be replaced by their SVML (Short Vector Math Library, Intel) or libmvec (GCC) vector equivalents when the compiler can prove the vector math library is available. This is an explicit extra step; it does not happen automatically unless `-fveclib=SVML` or equivalent is specified.

### 7.5 Mixed Precision / Type Promotion

A loop that mixes `int32` loads with `float64` computation requires widening conversions. While GCC and LLVM support type promotion in vectorization (`VEC_UNPACK_HI/LO`), the combined cost of the conversion operations often makes vectorization unprofitable, especially if VF has to drop to accommodate the wider type.

GCC added type conversion vectorization in 2005 (GCC 4.1) but the cost model frequently declines when element widths mix.
- Source reference: GCC Vectorization history, "Vectorization of loops that operate on multiple data-types," https://gcc.gnu.org/projects/tree-ssa/vectorization.html

### 7.6 Short Trip Count

A loop known at compile time to execute ≤ VF iterations will not be vectorized. The vectorized prologue + epilogue overhead exceeds the benefit. LLVM's cost model applies a minimum profitable trip count threshold (configurable via `-vectorizer-min-trip-count`, default 1 in LLVM but effectively higher due to the cost model).

### 7.7 Loop-Carried Floating-Point Reductions Without Fast-Math

As noted in §5.1, FP reductions are not legal to vectorize without `-ffast-math` / `-fassociative-math` because IEEE 754 mandates strict left-to-right evaluation order for sequential programs. Production compilers respect this: they do not vectorize FP sums by default.

**Production reality vs. documentation:** GCC's documentation says FP reductions need `-fassociative-math`. LLVM's documentation says fast-math flags are needed. In practice, benchmarks show that neither compiler vectorizes simple `for (sum += a[i])` loops at default settings on FP data. This is correct behavior per the standard but surprises users.

### 7.8 Struct-of-Arrays vs. Array-of-Structs

`AoS` layout (`Point p[N]` where `Point = {x, y, z}`) interleaves data: memory is `x0 y0 z0 x1 y1 z1 ...`. A loop computing `p[i].x * 2` would need to load every 3rd float, requiring a gather or complex shuffle. This pattern is rarely vectorized.

`SoA` layout (`float x[N]; float y[N]; float z[N]`) has all x-values consecutive: trivially vectorizable.

Production compilers do not automatically transform AoS to SoA. This is a data layout decision that must be made by the programmer (or a polyhedral transformation tool).

### 7.9 Reductions on Custom Types

If the reduction accumulator is a user-defined struct (e.g., a complex number, a statistics accumulator), no production auto-vectorizer handles it automatically. The accumulator must be decomposable into scalar operations with known SIMD equivalents.

### 7.10 Volatile and Atomic Memory Accesses

Any memory access marked `volatile` or using C11/C++11 atomic operations in the loop body prevents vectorization entirely. Volatile requires each access to observe the exact number of hardware reads/writes — merging 4 volatile loads into one 4-wide vector load would change observable behavior. Atomics similarly cannot be widened.

This is a documented hard limit in both LLVM and GCC with no workaround. A loop body containing `std::atomic<int>` reads will not vectorize.

### 7.11 Non-Unit Stride Access Without Hardware Support

A loop `for i: a[i*stride] = b[i]` with a runtime non-unit stride that isn't known to equal a hardware-natural stride (2, 4, 8) will not vectorize profitably without scatter/gather. If the stride is a compile-time constant and the target has stride-specific load instructions (e.g., ARM NEON `VLD2` for stride 2), vectorization may fire. For unknown or large strides, both LLVM and GCC emit scalar code.

GCC specifically detects stride-1 ("unit stride") as the primary vectorizable pattern. The `-ftree-vectorizer-verbose` diagnostic distinguishes "not vectorized: not a simple loop" (structural) from "possible dependence between data-refs" (aliasing) from "not vectorized: unsupported use in stmt" (non-vectorizable operation) — three distinct failure classes.
- Source reference: GCC Project, "Auto-vectorization in GCC — Using the Vectorizer," example diagnostic output, https://gcc.gnu.org/projects/tree-ssa/vectorization.html

---

## §8 Pure-Functional and Value-Semantics Languages

Languages without mutable aliasing *structurally eliminate* many of the obstacles in §7.

### 8.1 Rust Auto-Vectorization via LLVM

Rust compiles to LLVM IR. In principle, the LLVM LV and SLP vectorizer operate on Rust-generated IR exactly as they do on Clang-generated IR. The key difference: Rust's ownership/borrow system enforces that *at the IR level*, two mutable references cannot alias. This means:
- No `noalias` annotation needed: the Rust compiler emits `noalias` attributes on function parameters by the borrow checker's guarantee.
- Rust slices carry an implicit `noalias` because Rust's type system ensures no two `&mut` references to overlapping memory exist simultaneously.

**Practical consequence:** Rust loops over slices often vectorize where equivalent C loops would not, because the `noalias` attribute is present automatically.

**`std::simd` (portable SIMD, nightly):** A Rust nightly feature (`portable_simd`, tracking issue #86656) that provides `Simd<T, N>` — a portable vector type that compiles to the best available SIMD instructions. Unlike `std::arch` (which exposes raw hardware intrinsics), `std::simd` provides consistent cross-target semantics.
- `Simd<T, N>` can be thought of as a parallelized `[T; N]` — operations are applied elementwise with defined cross-target semantics.
- On targets without SIMD, operations fall back to scalar code.
- Source reference: Rust Documentation, `std::simd`, https://doc.rust-lang.org/std/simd/index.html

### 8.2 Halide: Explicit Schedule-Directed Vectorization

Halide is not auto-vectorizing in the traditional sense: vectorization is specified in the *schedule*, not inferred by analysis. The algorithm (what to compute) is separated from the schedule (how to compute it: tile size, vector width, parallelism level).

```cpp
// Algorithm:
Func blur_x, blur_y;
blur_x(x, y) = (input(x-1, y) + input(x, y) + input(x+1, y)) / 3;
blur_y(x, y) = (blur_x(x, y-1) + blur_x(x, y) + blur_x(x, y+1)) / 3;

// Schedule:
blur_y.vectorize(x, 8);  // process 8 x-values per vector instruction
```
- Source reference: Halide Tutorial Lesson 5, "Vectorize, parallelize, unroll and tile your code," https://halide-lang.org/tutorials/tutorial_lesson_05_scheduling_1.html

**Auto-Scheduler:** Halide's auto-scheduler (Adams et al., "Learning to Optimize Halide with Tree Search and Random Programs," PLDI 2019, https://dl.acm.org/doi/10.1145/3314221.3314595) uses a tree-search ML approach to select tile sizes and vectorization widths automatically. It directly outputs a schedule including `.vectorize()` calls. This bypasses the need for full loop dependence analysis because Halide's pure-functional semantics guarantee no loop-carried dependences.

**Key insight for §8:** Halide's purely functional "algorithm" description means *all dependencies are explicit in the dataflow graph*. There are no pointer aliasing ambiguities; every producer-consumer relationship is statically known. The auto-scheduler needs only to optimize for cache locality and ILP, not to prove correctness.

### 8.3 Futhark: Flattening for GPU Parallelism

Futhark is a purely functional data-parallel language targeting GPU execution. Its key transformation is *incremental flattening* of nested data parallelism (Henriksen et al., PPoPP 2019, https://futhark-lang.org/publications/ppopp19.pdf).

The relevant observation for CPU auto-vectorization: Futhark's pure semantics eliminate all aliasing. The compiler knows *exactly* which arrays each operation reads and writes. No alias analysis is needed; the question is purely how to schedule parallel operations efficiently. Futhark generates CUDA/OpenCL but the same structural insight applies to CPU SIMD: pure arrays with no mutation remove the hardest obstacle in traditional auto-vectorization.

### 8.4 MLIR Vector Dialect

MLIR's `vector` dialect provides multi-dimensional vector types and operations that sit *above* hardware SIMD but *below* algorithm-level abstractions. The lowering pipeline:

1. Linalg / Affine dialect (algorithm-level structured ops) → `vector` dialect (MLIR n-D vectors)
2. `vector` dialect → flattened 1-D `vector` dialect (for LLVM's 1-D vector model)
3. 1-D `vector` dialect → LLVM IR `<N x T>` vector types → target SIMD instructions

The key design principle (source: https://mlir.llvm.org/docs/Dialects/Vector/): MLIR n-D vectors carry semantic information useful for transformations. Operations on `vector<4x4xf32>` can be unrolled-and-jammed to match hardware register width without relying on LLVM to infer this structure from scalar IR. This enables patterns "across multiple HW vectors" that pure 1-D LLVM vector lowering misses.

MLIR does not perform auto-vectorization in the traditional sense (it does not start from scalar code). It provides a *structured path* for code that already expresses vector semantics at the algorithm level (e.g., MLIR's Linalg matmul op, which can be directly lowered to vector operations).

---

## §9 Option Space for Simple's MIR

This section maps each surveyed technique to Simple's existing compiler pipeline. It is an *options matrix*, not a recommendation — that is J5's scope.

### 9.1 Current Simple SIMD Infrastructure

Simple's compiler already has vectorization scaffolding at `src/compiler/60.mir_opt/mir_opt/`:
- `auto_vectorize.spl` — entry point (`run_auto_vectorization`), coordinator
- `auto_vectorize_analysis.spl` — Phase 1: dependency analysis
- `auto_vectorize_validate.spl` — Phase 2: vectorizability validation
- `auto_vectorize_cost.spl` — Phase 3: cost model + decision
- `auto_vectorize_codegen.spl` — Phase 4: vector code generation
- `auto_vectorize_types.spl` — shared types (`LoopInfo`, `ArrayAccess`)
- `simd_lowering.spl` — MIR → SIMD instruction lowering

The `auto_vectorize.spl` header comment explicitly documents this as "a simplified implementation showing the structure." The `LoopInfo` struct captures `induction_var`, `start_value`, `end_value`, `step` — exactly the information SCEV would produce.

The four-file split already mirrors LLVM's LV pipeline:
- `_analysis` ↔ LLVM legality check + SCEV
- `_validate` ↔ LLVM legality check + alias analysis
- `_cost` ↔ LLVM TTI cost model
- `_codegen` ↔ LLVM VPlan → IR emit

Additional SIMD-aware files:
- `src/compiler/30.types/simd_capabilities.spl` — ISA capability detection
- `src/compiler/35.semantics/simd_check.spl` — semantic validation for SIMD types
- `src/compiler/70.backend/backend/native/x86_64_simd.spl` — x86_64 SIMD codegen

### 9.2 Options Matrix

The following table maps each surveyed technique to Simple's pipeline, noting the target phase, prerequisites, and deferral rationale.

| Technique | Target Phase | Prerequisite Analysis | Fits Existing Scaffold? | Defer? | Rationale |
|-----------|-------------|----------------------|------------------------|--------|-----------|
| **Loop-level vectorization (LV)** | `60.mir_opt` (`auto_vectorize_*`) | Loop detection, induction var, stride analysis | Yes — `LoopInfo` struct already exists | No — scaffold ready | Core technique; all other loop-level work builds on this |
| **SCEV-equivalent induction analysis** | `60.mir_opt` (`auto_vectorize_analysis`) | MIR loop structure (available in `50.mir`) | Partial — `start_value`/`end_value` fields exist but complex SCEV missing | No | Trip count estimation needed for cost model |
| **SLP / basic-block vectorization** | `60.mir_opt` (new pass) | Def-use chains within MIR blocks | Not in current scaffold | Defer (M3+) | Requires bottom-up isomorphism search; independent of loop vectorizer |
| **Runtime alias checks (loop versioning)** | `60.mir_opt` (`auto_vectorize_validate`) | Pointer provenance through MIR | Partially addressed in `_validate.spl` | No — needed for correctness | Without this, vectorizer is only safe for proven-noalias cases |
| **Cost model (TTI-equivalent)** | `60.mir_opt` (`auto_vectorize_cost`) | `simd_capabilities.spl` (already exists) | Yes — `CostEstimate` type exists | No | Populate with real throughput data per ISA |
| **Predicated tail (scalar epilogue)** | `60.mir_opt` (`auto_vectorize_codegen`) | Loop trip count (SCEV) | Sketched in `auto_vectorize.spl:13-18` | No | Default tail strategy; implement before anything else |
| **Active-lane-mask predication** | `60.mir_opt` (`auto_vectorize_codegen`) | Scalable VF (RVV/SVE), mask codegen in backend | Not present | Defer (RVV/SVE targets, M3+) | Only profitable with SVE/RVV hardware masking |
| **Idiom recognition (reduction)** | `60.mir_opt` (new recognition pass) or `35.semantics` | Reduction PHI pattern in MIR | Not present | No — high impact | FP sum, int sum, min/max are high-frequency; add to `_analysis` |
| **Idiom recognition (memcpy/memset)** | `35.semantics` or `60.mir_opt` | Consecutive-write pattern detection | Not present | No — high impact | Replace with `rt_memcpy` before vectorizer sees the loop |
| **Polyhedral (Polly-equivalent)** | Between `60.mir_opt` and `70.backend` (new layer) | SCoP detection, affine subscript analysis (ISL equivalent) | Not present | Defer (post-M4) | High implementation cost; payoff only on dense loop nests |
| **FMV (function multiversioning)** | `70.backend` + linker (`70.backend/linker`) | ISA variant selection, IFUNC-equivalent | `simd_capabilities.spl` partial | Defer (M5+) | Requires linker/loader support; large scope |
| **Gather/scatter** | `70.backend` (`x86_64_simd.spl`) | Indirect index pattern detection in MIR | Backend partially ready | Defer (post AVX2 baseline) | Only profitable on AVX2+; adds analysis complexity |
| **MLIR vector dialect (bridge)** | New: between `60.mir_opt` and `70.backend` | MLIR lowering infrastructure | Not present | Defer (long-term) | Requires MLIR dependency or reimplementation |
| **Rust-style noalias from ownership** | `50.mir` / `55.borrow` | Simple's borrow checker output | Borrow checker exists at `55.borrow` | No — free win | Simple's borrow checker already proves aliasing; plumb `noalias` from `55.borrow` into `60.mir_opt` |

### 9.3 Key Structural Insight for Simple

**Simple's borrow checker (`55.borrow`) provides a SCEV-equivalent aliasing oracle for free.** LLVM must run costly inter-procedural alias analysis and insert runtime checks because C/C++ allow arbitrary pointer aliasing. Simple's borrow checker statically proves (at compile time) whether two references may alias. This eliminates the most expensive source of vectorization refusals in §7.1.

The pipeline ordering is:
```
55.borrow (aliasing proof) → 60.mir_opt/auto_vectorize_validate (no-alias guaranteed) → no runtime checks needed
```

This structural advantage is analogous to what Rust gains from `noalias` — but for Simple it is deeper because Simple's borrow system applies to all references, not just function parameters.

**What must be built vs. what exists:**
- *Exists:* Loop detection, induction variable extraction, SIMD capability queries, scalar epilogue structure, basic cost skeleton, x86_64 SIMD backend, borrow-checker aliasing proofs.
- *Missing:* Real SCEV-equivalent trip-count analysis (needed for cost threshold), alias-info propagation from `55.borrow` into `60.mir_opt`, FP reduction handling with associativity decision, and idiom recognition for reductions.

### 9.4 Technique Priority by MIR Fit

Three techniques with highest fit to Simple's existing MIR (not recommendations — purely structural observations):

1. **Borrow-to-noalias propagation** (`55.borrow` → `60.mir_opt/auto_vectorize_validate`): Zero new analysis required; thread existing borrow checker output into the vectorizer's alias check. Eliminates the most common vectorization blocker.

2. **Trip-count-aware cost model** (`60.mir_opt/auto_vectorize_cost`): The `CostEstimate` struct exists; populate it with trip count from `LoopInfo` and per-instruction costs from `simd_capabilities`. This directly enables the VF selection loop from §3.1.

3. **Reduction idiom recognition** (`60.mir_opt/auto_vectorize_analysis`): MIR phi nodes from reduction loops are structurally identifiable. Mapping integer reductions to `rt_simd_reduce_*` intrinsics is a small pattern-match addition to `_analysis.spl`.

### 9.5 Techniques to Defer

The following are production-grade features in LLVM/GCC but have high implementation cost relative to Simple's current stage:
- **SLP/BB vectorization**: Independent of loop structure; needs a full def-use isomorphism search engine.
- **Polyhedral analysis**: Only beneficial for dense loop nests (BLAS-level); not general-purpose.
- **Function multiversioning**: Requires linker/loader IFUNC support; adds binary size.
- **MLIR vector dialect integration**: Would require either linking MLIR or reimplementing its n-D vector lowering.
- **Active-lane-mask predication**: Valuable for RVV/SVE; premature until those backends are mature (per the Wave J SIMD rollout plan).

---

## References

| Ref | Source |
|-----|--------|
| [LLVM-VEC] | LLVM Project, "Auto-Vectorization in LLVM," LLVM 23.0.0git, https://llvm.org/docs/Vectorizers.html |
| [LLVM-VPLAN] | LLVM Project, "Vectorization Plan," LLVM 23.0.0git, https://llvm.org/docs/VectorizationPlan.html |
| [LLVM-SANDBOX] | LLVM Project, "The Sandbox Vectorizer," LLVM 23.0.0git, https://llvm.org/docs/SandboxVectorizer.html |
| [LLVM-PASSES] | LLVM Project, "LLVM's Analysis and Transform Passes," LLVM 23.0.0git, https://llvm.org/docs/Passes.html |
| [LLVM-LANGREF] | LLVM Project, "LLVM Language Reference Manual," LLVM 23.0.0git, https://llvm.org/docs/LangRef.html |
| [GCC-VEC] | GCC Project, "Auto-vectorization in GCC," https://gcc.gnu.org/projects/tree-ssa/vectorization.html |
| [GCC-INT-VEC] | GCC Internals, "Vectorization," https://gcc.gnu.org/onlinedocs/gccint/Vectorization.html |
| [GCC-OPT] | GCC Manual, "Options That Control Optimization," https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html |
| [CRANELIFT-SITE] | Bytecode Alliance, "Cranelift," https://cranelift.dev/ |
| [CRANELIFT-IR] | Bytecode Alliance, "Cranelift IR Reference," https://github.com/bytecodealliance/wasmtime/blob/main/cranelift/docs/ir.md |
| [MLIR-VEC] | MLIR Project, "'vector' Dialect," https://mlir.llvm.org/docs/Dialects/Vector/ |
| [POLLY-PASSES] | Polly LLVM, "The available LLVM passes," https://polly.llvm.org/documentation/passes.html |
| [HALIDE-TUT5] | Halide Project, "Vectorize, parallelize, unroll and tile your code," https://halide-lang.org/tutorials/tutorial_lesson_05_scheduling_1.html |
| [HALIDE-PLDI19] | Adams et al., "Learning to Optimize Halide with Tree Search and Random Programs," PLDI 2019, https://dl.acm.org/doi/10.1145/3314221.3314595 |
| [DOTNET-SIMD] | Microsoft Learn, "Use SIMD-accelerated numeric types," https://learn.microsoft.com/en-us/dotnet/standard/simd |
| [DOTNET9-RT] | Microsoft Learn, "What's new in the .NET 9 runtime," https://learn.microsoft.com/en-us/dotnet/core/whats-new/dotnet-9/runtime |
| [RUST-SIMD] | Rust Documentation, `std::simd` (nightly), https://doc.rust-lang.org/std/simd/index.html |
| [FUTHARK-PPOPP19] | Henriksen et al., "Incremental flattening for nested data parallelism on the GPU," PPoPP 2019, https://futhark-lang.org/publications/ppopp19.pdf |
| [OMP-SIMD] | OpenMP Architecture Review Board, "OpenMP Application Programming Interface 5.2," §2.11.4 simd Construct, https://www.openmp.org/wp-content/uploads/OpenMP-API-Specification-5-2.pdf |
| [ARM-ACLE-FMV] | ARM Ltd., "ACLE — Function Multi Versioning," https://arm-software.github.io/acle/main/acle.html |
| [SIMPLE-AV] | Simple Language Compiler, `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl`, internal |
| [SIMPLE-ISA] | Simple Language Compiler, `doc/01_research/simd_isa_survey_2026-05-02.md`, internal |
