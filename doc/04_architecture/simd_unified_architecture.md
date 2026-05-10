<!-- claude-arch -->
# Architecture: Unified SIMD (FixedVec + ScalableVec)

This document defines the unified SIMD architecture for the Simple compiler. The design bridges seven
target ISAs — NEON, SSE/AVX/AVX2/AVX-512, SVE/SVE2, RVV 1.0, PTX, and SPIR-V — through a two-type
model (`FixedVec<T, const N>` for fixed-width targets and `ScalableVec<T>` for length-agnostic targets)
plus a first-class `Mask<V>` associated type. LMUL is a backend lowering knob hidden from the user type
system. The existing `Vec2f/Vec4f/Vec8f/Vec2d/Vec4d` hardcoded scalar structs are deprecated in favour
of `FixedVec<T, N>` type aliases. This document supersedes `doc/04_architecture/portable_simd_fp_modules.md`
(46 lines), which modeled the boundary between target presets and backend FP modules; all concepts from
that document are absorbed into sections 6 and 3 here.

---

## Table of Contents

1. [Goals & Non-goals](#1-goals--non-goals)
2. [Type-System Surface](#2-type-system-surface)
3. [Lowering Pipeline](#3-lowering-pipeline)
4. [Mask Semantics & Predication](#4-mask-semantics--predication)
5. [Auto-Vectorization Contract](#5-auto-vectorization-contract)
6. [Capability Detection](#6-capability-detection)
7. [GPU / CUDA Integration](#7-gpu--cuda-integration)
8. [Anti-Pattern Callouts & Migration](#8-anti-pattern-callouts--migration)
9. [Open Questions](#9-open-questions)

---

## 1. Goals & Non-goals

### Goals

- **Single abstract `Vector` trait** covering elementwise arithmetic, memory, lane ops, reductions, and
  masked variants — so user code is portable across NEON / SSE / AVX / AVX-512 / SVE2 / RVV / PTX /
  SPIR-V without `#if` branching.
- **`FixedVec<T, const N>`**: monomorphizes at compile time; maps to XMM/YMM/ZMM, Q-regs, or explicit
  CUDA `.v4` packed loads.
- **`ScalableVec<T>`**: VL-agnostic at the type level; lowers to `<vscale x K x T>` for SVE2 / RVV with
  strip-mining loop automatically inserted by the compiler.
- **First-class `Mask<V>`**: an associated type on `Vector`. Each backend lowers it correctly:
  AVX-512 k-registers, SVE2 p-registers, RVV v0-mask, NEON sign-bit-wide BSL blend vectors.
- **LMUL hidden from user**: the backend MIR optimisation pass widens LMUL for throughput; users never
  write LMUL.
- **Default predication = zero-fill** (`_z` semantics on SVE2; masked-zero on AVX-512 via `_maskz_`
  variants; RVV agnostic tail policy).
- **`warp-as-vector` GPU model**: explicit warp-scoped ops (shfl, vote, reduce) via the `WarpVec<T>`
  extension of `Vector` for CUDA/PTX; SPIR-V uses subgroup ops.
- **Capability-bitmask detection**: replace the current single-level `SimdPlatform` enum with a
  bitmask flags struct that can represent `has_avx2 AND has_avx512bw` simultaneously.
- **MDSOC+ default**: the SIMD library lives in `src/lib/nogc_sync_mut/simd/` (currently a single
  `simd.spl` flat file at `src/lib/nogc_sync_mut/simd.spl`) — no GC allocation, no async. Kernel /
  driver code stays MDSOC-only and calls `FixedVec` only through inline lowering.

### Non-goals

- **Exposing LMUL to user code.** LMUL is a micro-architectural throughput knob; exposing it would
  create unportable code. (A2 §7 confirms no user-visible LMUL today; this policy locks that in.)
- **Sparse or ragged vector.** `select`/`masked_load`/`masked_store` cover the predicated use cases;
  general sparse storage is out of scope.
- **BLAS/LAPACK-level matrix API.** Higher-level linear algebra (`vector_ops.spl` in
  `src/lib/common/linear_algebra/`) continues to exist as a separate layer built *on top of* the `Vector`
  trait; it is not merged here.
- **Geometry math (`Vec3`, `Vec4` as positional)**: `src/lib/nogc_sync_mut/engine/render/vector.spl`
  and `src/lib/common/linear_algebra/vector_ops.spl` cover geometric semantics; those types coexist
  with `FixedVec` but are not replaced by it. Geometry code uses explicit aliases (see §8).
- **Phase milestones.** See B3 rollout plan (`doc/05_design/simd_rollout_plan.md`).

---

## 2. Type-System Surface

All type signatures below are pseudocode in Simple syntax. No implementation body is included.

### 2.1 `Vector` trait

```
trait Vector:
    # Associated types
    type Elem                                   # element scalar type (f32, f64, i32, u8, ...)
    type Mask                                   # per-lane boolean mask (target-specific width)

    # Lane count: compile-time constant for FixedVec, runtime query for ScalableVec
    fn lanes(self) -> usize

    # Construction
    fn splat(x: Self.Elem) -> Self              # broadcast scalar to all lanes
    fn from_array(arr: [Self.Elem]) -> Self     # load from slice (length must equal lanes)
    fn to_array(self) -> [Self.Elem]            # store to heap slice

    # Elementwise arithmetic  (cross-ISA: all N; see A1 §4)
    fn add(self, other: Self) -> Self
    fn sub(self, other: Self) -> Self
    fn mul(self, other: Self) -> Self
    fn div(self, other: Self) -> Self
    fn fma(self, b: Self, c: Self) -> Self      # self*b + c
    fn neg(self) -> Self
    fn abs(self) -> Self
    fn min(self, other: Self) -> Self           # elementwise min
    fn max(self, other: Self) -> Self           # elementwise max

    # Integer-specific bitwise ops (Elem must be integer)
    fn bit_and(self, other: Self) -> Self
    fn bit_or(self, other: Self) -> Self
    fn bit_xor(self, other: Self) -> Self
    fn bit_not(self) -> Self
    fn shl(self, count: u32) -> Self            # left shift each lane
    fn shr(self, count: u32) -> Self            # logical right shift each lane

    # Comparisons → Mask  (cross-ISA: all N for f32; see A1 §4 rows eq/lt/gt)
    fn eq(self, other: Self) -> Self.Mask
    fn ne(self, other: Self) -> Self.Mask
    fn lt(self, other: Self) -> Self.Mask
    fn le(self, other: Self) -> Self.Mask
    fn gt(self, other: Self) -> Self.Mask
    fn ge(self, other: Self) -> Self.Mask

    # Memory
    fn load(ptr: *Self.Elem) -> Self
    fn store(self, ptr: *mut Self.Elem)
    fn load_aligned(ptr: *Self.Elem) -> Self    # ptr must be vector-width aligned
    fn store_aligned(self, ptr: *mut Self.Elem)
    fn masked_load(mask: Self.Mask, ptr: *Self.Elem, fallback: Self) -> Self
    fn masked_store(self, mask: Self.Mask, ptr: *mut Self.Elem)
    fn gather(base: *Self.Elem, idx: FixedVec<i32, N>) -> Self   # N = Self.lanes
    fn scatter(self, base: *mut Self.Elem, idx: FixedVec<i32, N>)

    # Lane manipulation
    fn extract(self, lane: usize) -> Self.Elem  # runtime index
    fn insert(self, lane: usize, val: Self.Elem) -> Self
    fn broadcast(val: Self.Elem) -> Self        # alias of splat
    fn permute(self, idx: Self) -> Self         # intra-vector permute (NEON: E, AVX2: N, A1 §4)
    fn shuffle(a: Self, b: Self, idx: FixedVec<u32, N>) -> Self  # cross-vector select

    # Reductions  (partial native coverage; see A1 §4 reduction rows)
    fn reduce_sum(self) -> Self.Elem
    fn reduce_min(self) -> Self.Elem
    fn reduce_max(self) -> Self.Elem
    fn reduce_and(self) -> Self.Elem            # integer only
    fn reduce_or(self) -> Self.Elem             # integer only
    fn reduce_xor(self) -> Self.Elem            # integer only

    # Mask-driven select
    fn select(mask: Self.Mask, t: Self, f: Self) -> Self

    # Type conversion
    fn cast<U>(self) -> FixedVec<U, N>          # element type reinterpret/convert (same N)
    fn widen(self) -> (Self, Self)              # widen element type, double-width pair
    fn narrow(a: Self, b: Self) -> Self         # narrow element type, pack two to one
    fn saturate_narrow(a: Self, b: Self) -> Self
```

Notes on cross-ISA coverage (A1 §4):
- `gather`: NEON emulates via scalar loop; AVX2, AVX-512, SVE2, RVV all native.
- `scatter`: NEON and AVX2 emulate via scalar loop; AVX-512, SVE2, RVV native.
- `reduce_sum`: NEON emulates via `vaddvq_f32`; AVX/AVX2 emulate via `hadd` tree; AVX-512 native;
  SVE2/RVV native; PTX emulates via `shfl.sync` tree.
- `permute`/`shuffle`: NEON emulates via `vqtbl1q_u8`; AVX2 native; all others native or partial.

### 2.2 `Mask` trait

```
trait Mask:
    type Vec                                    # the Vector type this mask belongs to

    fn and(self, other: Self) -> Self
    fn or(self, other: Self) -> Self
    fn xor(self, other: Self) -> Self
    fn not(self) -> Self
    fn all(self) -> bool                        # all active lanes set
    fn any(self) -> bool                        # at least one active lane set
    fn none(self) -> bool
    fn popcount(self) -> usize                  # count of set lanes
    fn lane_get(self, i: usize) -> bool
    fn lane_set(self, i: usize, val: bool) -> Self
    fn from_bools(arr: [bool]) -> Self
```

### 2.3 `FixedVec<T, const N>`

```
class FixedVec<T, const N: usize>:
    # Opaque storage; compiler lowers to register or stack slot of N*sizeof(T) bytes.
    # No user-visible fields.

    type Elem = T
    type Mask = FixedMask<N>

impl<T, const N: usize> Vector for FixedVec<T, N>:
    # All Vector methods implemented via compiler intrinsics (rt_simd_* lowering path)
    # or auto-vectorizer promotion. No scalar fallback in the impl bodies.
```

`FixedMask<N>` stores N bits. On AVX-512 it lowers to a k-register. On AVX2/NEON it lowers to a
full-width vector where the sign bit of each lane represents the boolean. On SVE2 / RVV it lowers
to a p-register or v0-mask slice of width N.

### 2.4 `ScalableVec<T>`

```
class ScalableVec<T>:
    # Opaque; compiler lowers to SVE2 Z-register or RVV V-register.
    # `lanes()` is runtime-determined (svcntw() / csrr vlenb).

    type Elem = T
    type Mask = ScalableMask

impl<T> Vector for ScalableVec<T>:
    # Auto-inserts vsetvli/svcntw strip-mining when lowering loop bodies.
    # LMUL selection is a backend MIR optimisation pass decision.
```

`ScalableMask` lowers to an SVE2 p-register or to the RVV v0 data register (v0 is the only allowed
mask source per RVV §5).

### 2.5 Interop: `FixedVec<T,N>` ↔ `ScalableVec<T>`

There is **no implicit cast** between `FixedVec` and `ScalableVec`. The reason: `vscale` is
runtime-determined, so the compiler cannot prove at monomorphization time that a `ScalableVec<f32>`
contains exactly N elements. Providing an implicit coercion would create silent bugs when the runtime
VL differs from N.

Two explicit conversion functions are provided:

```
fn from_fixed<T, const N: usize>(fv: FixedVec<T, N>) -> ScalableVec<T>
    # Always succeeds. Pads extra lanes with zero (matches _z default predication).

fn try_to_fixed<T, const N: usize>(sv: ScalableVec<T>) -> Option<FixedVec<T, N>>
    # Returns Some(fv) if the runtime VL >= N; returns None otherwise.
    # Does NOT truncate silently — the caller must handle the None case.
```

This is consistent with the `_z` (zero-fill) default predication (§4): inactive lanes carry zero,
not undefined data.

### 2.6 `WarpVec<T>` — GPU extension

For CUDA/PTX targets only, `WarpVec<T>` extends `Vector` with warp-scoped ops:

```
trait WarpVec: Vector:
    fn shfl_up(self, delta: u32, mask: u32) -> Self
    fn shfl_down(self, delta: u32, mask: u32) -> Self
    fn shfl_bfly(self, lane_mask: u32, mask: u32) -> Self
    fn shfl_idx(self, src_lane: u32, mask: u32) -> Self
    fn warp_reduce_sum(self, mask: u32) -> Self.Elem
    fn warp_ballot(cond: bool, mask: u32) -> u32    # vote.sync
```

These methods have no CPU-SIMD lowering; calling them outside a kernel context is a compile-time
error (`35.semantics/gpu_checker.spl` enforces this).

---

## 3. Lowering Pipeline

### 3.1 Pipeline Overview

```
  source (.spl)
      |
      v
  [10.frontend]   parse → AST
      |
      v
  [20.hir]        typed AST; Vector method calls resolved to HIR nodes
                  FixedVec<T,N>::add → HIR::VectorBinOp(Add, T, N)
                  ScalableVec<T>::add → HIR::ScalarBinOp tagged scalable=true
      |
      v
  [25.traits]     trait dispatch — Vector impl selected; Mask associated type resolved
      |
      v
  [30.types]      simd_vector_types.spl: FixedVec<T,N> monomorphized type nodes;
                  old Vec4f etc. forwarded via type alias
      |
      v
  [35.semantics]  simd_check.spl: validates lane count, element type whitelist,
                  Mask type consistency, WarpVec kernel-only enforcement
      |
      v
  [40.mono]       FixedVec<f32,4>, FixedVec<f32,8>, FixedVec<i32,4> ... specialised;
                  ScalableVec<f32> remains generic (VL unknown at mono time)
      |
      v
  [50.mir]        HIR::VectorBinOp → MirInstKind::SimdAddF32x4 / SimdAddF32x8 / ...
                  HIR::ScalarBinOp(scalable) → MirInstKind::ScalableVecOp(Add, T)
                  Mask operations → MirInstKind::MaskOp(And/Or/..., N)     [NEW]
                  Gather/Scatter  → MirInstKind::SimdGather / SimdScatter   [NEW]
                  Permute/Shuffle → MirInstKind::SimdPermute / SimdShuffle  [NEW]
      |
      v
  [60.mir_opt]    a) simd_lowering.spl:93: rt_simd_* name-match → SimdXxx (existing)
                  b) auto_vectorize_*.spl: scalar loop → SimdXxx promotion (existing,
                     WIRE-UP GAP — call site unconfirmed; must be added to MIR opt driver)
                  c) lmul_widen.spl [NEW]: promotes LMUL 1→2→4 for RVV throughput
                  d) predicate_promote.spl [NEW]: _z → _x when inactive lanes dead
      |
      v
  [70.backend]    backend-strict-emit per target:
                  x86_64_simd.spl: SSE/AVX/AVX2 (exists); AVX-512 EVEX [NEW]
                  arm_neon.spl: NEON-128 (exists); no predicate regs
                  arm_sve2.spl [NEW]: SVE2 Z/P regs, _z default, vsetvl loop
                  riscv_v.spl [NEW]: vsetvli, v0 mask, LMUL from lmul_widen pass
                  cuda/ptx_builder.spl: scalar (exists); .v4 vector loads [NEW];
                                        shfl.sync warp ops [NEW]
                  vulkan/spirv_builder.spl: scalar+barrier (partial);
                                            SPIR-V vector ops + subgroup [NEW]
      |
      v
  machine code / PTX text / SPIR-V binary
```

### 3.2 Per-layer Change Summary

| Layer | File | Today | Change needed |
|-------|------|-------|---------------|
| 00.common | `simd_types.spl:1–19` (stub, 19L) | `SimdElementType` enum only | Extend: add `MaskKind` enum; remove duplicate `SimdElementType` (A2 §8 confirmed duplicate vs `simd_check.spl`) |
| 10.frontend | — | no SIMD surface | No change; frontend is ISA-agnostic |
| 20.hir | `hir/` — no SIMD nodes | All Vec4f calls are plain method calls | Add `HIR::VectorBinOp`, `HIR::VectorLoad`, `HIR::VectorMask` node variants |
| 25.traits | `25.traits/` | `Vector` trait not defined | Define `Vector`, `Mask`, `WarpVec` trait defs here |
| 30.types | `simd_vector_types.spl:12–440` (scalar structs) | 5 hardcoded scalar structs | Deprecate; add `FixedVec<T,N>` generic class + `FixedMask<N>` + `ScalableVec<T>` + `ScalableMask` |
| 30.types | `simd_platform.spl:1–387` | `SimdCapabilities` single-level | Replace with bitmask `SimdFeatureFlags` (§6); keep file, rename struct |
| 35.semantics | `simd_check.spl:1–544` (concrete) | Type-check existing vec ops; no Mask check | Extend: validate `Mask<V>` consistency; WarpVec kernel-only check; monomorphization bound check |
| 40.mono | no SIMD file | Monomorphizes concrete types | Add `FixedVec<T,N>` specialization registry; ScalableVec passes through unspecialized |
| 50.mir | `mir_types.spl:139–144` (fixed), `:170` (scalable stub) | Fixed types present; ScalableVec stub | Wire `ScalableVec` lowering; add `MaskOp`, `SimdGather`, `SimdScatter`, `SimdPermute`, `SimdShuffle` instruction variants |
| 50.mir | `mir_lowering_expr.spl:1238` | GPU intrinsics wired; SIMD not wired | Wire `FixedVec::method` → appropriate `SimdXxx` MIR (currently missing: A2 §2, `:116` is scalar) |
| 60.mir_opt | `simd_lowering.spl:93–149` | `rt_simd_*` name-match | Add new names for gather/scatter/permute/mask ops |
| 60.mir_opt | `auto_vectorize_codegen.spl:211` | Emits SimdXxx; **not wired to pipeline** | Add call site in MIR opt driver pass sequence |
| 60.mir_opt | (new) `lmul_widen.spl` | missing | RVV LMUL 1→2→4 promotion pass |
| 60.mir_opt | (new) `predicate_promote.spl` | missing | `_z` → `_x` when inactive lane values proven dead |
| 70.backend | `x86_64_simd.spl:152+` (SSE/AVX) | SSE, AVX, AVX2 emit; no AVX-512 | Add ZMM / EVEX encode path; sub-feature dispatch (BW/DQ/VL/VBMI) |
| 70.backend | `arm_neon.spl:71+` (NEON) | NEON-128 emit; no predicates | Extend BSL mask-blend path for `FixedMask<N>` |
| 70.backend | (new) `arm_sve2.spl` | missing | SVE2 Z/P register model; `_z` default; vsetvl strip loop |
| 70.backend | (new) `riscv_v.spl` | missing | `vsetvli`, `v0` mask, `LMUL` from `lmul_widen` pass output |
| 70.backend | `ptx_builder.spl:197+` | scalar PTX only | Add `.v4.f32` packed loads; `shfl.sync`/`vote.sync` warp ops |
| 70.backend | `spirv_builder.spl` | OpFAdd/OpIMul/OpLoad/OpStore | Add vector type declarations; subgroup ballot/shuffle/reduce ops |
| 70.backend | `portable_numeric_capabilities.spl:186` | AVX/AVX2/RVV bools; no NEON/SVE | Merge into new `SimdFeatureFlags` (§6); keep as thin delegate |

---

## 4. Mask Semantics & Predication

### 4.1 The Four Mask Models

| Backend | Mask representation | Width |
|---------|---------------------|-------|
| AVX-512 | k-register (k0–k7); 1 bit per lane | 8/16/32/64 bits |
| AVX/AVX2/NEON | Sign-bit of a full-width lane vector | N × sizeof(T) |
| SVE2 | P-register (p0–p15); VL/8 bits | runtime |
| RVV | v0 data register; 1 bit per element | ceil(VLEN/8) bytes |

`FixedMask<N>` lowers to:
- AVX-512: k-register — the backend encodes `_mask` prefix ops (e.g., `_mm512_maskz_add_ps`).
- AVX/AVX2/SSE: a `__m256i`/`__m128i` where each 32-bit lane is `0x00000000` or `0xFFFFFFFF`.
- NEON: a `uint32x4_t` where each lane is all-zeros or all-ones, consumed via BSL (`vbslq_f32`).

`ScalableMask` lowers to:
- SVE2: a p-register. The compiler allocates from p0–p15.
- RVV: v0. Only one mask register is available; the compiler serialises if multiple masks are live
  simultaneously (register spill strategy: store to memory, reload before use).

### 4.2 Predication Default: `_z` (zero-fill)

**Default**: inactive lanes receive zero in the output. This maps to:
- SVE2: `_z` suffix — `svadd_f32_z(pg, a, b)` — inactive lanes output 0.0.
- AVX-512: `_maskz_` prefix — `_mm512_maskz_add_ps(k, a, b)` — masked-off lanes output 0.
- RVV: `vta=mu` (tail agnostic) with explicit zeroing via `vmv.v.i vd, 0` before masked op.
- NEON: BSL blend with zero vector as the false-lane input.
- PTX: `@%p0 add.f32 %d, %a, %b` with `%d` pre-initialised to `0.0`.

### 4.3 Promotion to `_x` (don't-care)

The `predicate_promote.spl` MIR optimisation pass (§3.2) analyses liveness: if the output of a
masked operation is only consumed by a subsequent operation that covers all lanes unconditionally,
the inactive lane value is dead. In that case the backend may emit the `_x` variant:
- SVE2: `svadd_f32_x(pg, a, b)` — undefined inactive lanes, smaller code / better throughput.
- AVX-512: `_mm512_mask_add_ps(src, k, a, b)` using `src=a` (passthrough, not `_maskz_`).

The `_m` (merge) variant is not exposed at the IR level; it is only emitted by the backend when
the liveness analysis proves a specific merge-into-src pattern.

### 4.4 Materialisation Points

A mask **materialises** (allocates a physical register) at the point where a comparison produces
one or where a `Mask::from_bools` is called. Masks flow through logical ops without materialising
intermediate results on targets with dedicated registers (AVX-512, SVE2). On NEON / AVX2, every
mask op allocates a full-width vector register.

The `simd_check.spl` layer (35.semantics) validates that `Mask<V>` is the correct associated type
for the `Vector` type V at every `select`, `masked_load`, and `masked_store` call site.

---

## 5. Auto-Vectorization Contract

### 5.1 When the Compiler Vectorizes Automatically

The auto-vectorizer (`60.mir_opt/auto_vectorize_*.spl`, 5 files, ~1300 total lines) promotes scalar
loops to `FixedVec`-width SIMD MIR when **all** of the following hold:

1. The loop body contains only elementwise arithmetic on a single array (no cross-iteration dependence
   detected by `auto_vectorize_analysis.spl`).
2. The trip count is statically or conservatively known, or a `while` loop with an outer strip-mined
   remainder is acceptable (`auto_vectorize_validate.spl:245`).
3. No function calls inside the loop body that are not whitelisted as `@simd`-safe
   (`auto_vectorize_validate.spl` — function call check).
4. The cost model (`auto_vectorize_cost.spl`) estimates vector speedup > 1.5× over scalar
   (instruction-count based; concrete implementation exists).
5. The element type is in the vectorizable set: `f32`, `f64`, `i32`, `i64`, `u32`, `u16`, `u8`.

**Wire-up gap** (A2 §7 — call site unconfirmed): `auto_vectorize_codegen.spl` produces real
`SimdAddF32x4` / `SimdAddF32x8` etc. MIR instructions but the pass is not confirmed wired into the
MIR optimisation driver. Until wiring is verified, the auto-vectorizer is latent. The architecture
requires it to be called from the MIR opt pass sequence in `60.mir_opt/` after `simd_lowering.spl`.

### 5.2 Explicit `Vector` Use

When the user explicitly calls `FixedVec<f32, 8>::splat(x).add(y)` or uses a `ScalableVec<T>` value,
the HIR vectorisation path (§3.2, 20.hir layer) fires unconditionally. No cost check — user intent
is explicit.

**Current gap** (A2 §2): `Vec4f::add` at `30.types/simd_vector_types.spl:116` is implemented as
scalar field addition. Until the HIR layer intercept is added (§3.2), user explicit Vector ops still
execute as scalar code. The new `FixedVec<T,N>` generic class will have only intrinsic-backed
implementations, no scalar fallback.

### 5.3 Loops That Do NOT Qualify

- Loops with `break` or early exit (divergent control flow).
- Loops with function calls not annotated `@simd_safe`.
- Loops where array aliasing cannot be ruled out.
- Loops over `ScalableVec<T>` arrays on fixed-width targets (NEON/SSE): the compiler decomposes
  into `FixedVec<T, K>` strips with a scalar tail — this is NOT auto-vectorization, it is
  ScalableVec lowering (§3.2, 70.backend).

### 5.4 `@simd` Annotation

A future `@simd` loop annotation forces vectorisation and turns the cost check into a diagnostic
(error if not vectorizable). This is a no-op today; the architecture reserves the syntax.

---

## 6. Capability Detection

### 6.1 Motivation

`SimdCapabilities` in `30.types/simd_platform.spl` stores a single `SimdPlatform` enum value — the
highest detected level. This cannot represent `has_avx2 AND has_avx512bw AND NOT has_avx512vl` (A2
§4). `PortableNumericCapabilities` in `70.backend/portable_numeric_capabilities.spl:186` has individual
booleans but is missing NEON, SVE, SVE2 fields (A2 §4). Both are replaced by `SimdFeatureFlags`.

### 6.2 `SimdFeatureFlags` — New Bitmask Struct

```
class SimdFeatureFlags:
    # x86 fixed-width
    has_sse:         bool
    has_sse2:        bool
    has_sse4_1:      bool
    has_avx:         bool
    has_avx2:        bool
    has_fma:         bool
    has_avx512f:     bool    # Foundation; ZMM, basic float/int
    has_avx512bw:    bool    # Byte/word integer ops
    has_avx512dq:    bool    # Doubleword/quadword integer ops
    has_avx512vl:    bool    # 128/256-bit subsets of AVX-512 instructions
    has_avx512vbmi:  bool    # Vector byte manipulation
    has_avx512fp16:  bool    # FP16 native
    has_avxvnni:     bool    # INT8 dot product

    # ARM fixed-width
    has_neon:        bool    # AArch64 Advanced SIMD (128-bit)
    has_neon_fp16:   bool    # FP16 vector ops on NEON

    # ARM scalable
    has_sve:         bool    # SVE (first generation)
    has_sve2:        bool    # SVE2 (mandatory in Armv9)
    sve_vl_bits:     usize   # runtime vector length in bits (0 = unknown)

    # RISC-V scalable
    has_riscv_v:     bool    # RVV 1.0
    has_riscv_zvfh:  bool    # RVV FP16 extension
    riscv_vlenb:     usize   # bytes per vector register (0 = unknown)

    # FP16 / BF16 (any platform)
    has_fp16:        bool    # any native FP16 (derived: avx512fp16 OR neon_fp16 OR zvfh)
    has_bf16:        bool    # BF16 (AVX-512 BF16 / AMX / Arm BF16 extension)
```

### 6.3 Detection Mechanisms per Platform

| Platform | Primary probe | Fallback |
|----------|--------------|----------|
| x86 Linux | Parse `/proc/cpuinfo` flags: `sse`, `avx`, `avx2`, `avx512f`, `avx512bw`, `avx512dq`, `avx512vl` | On x86_64, `sse2` guaranteed; query CPUID leaf 7 at startup if `/proc/cpuinfo` absent |
| x86 non-Linux | CPUID leaf 1 (ECX/EDX) + leaf 7 (EBX/ECX/EDX) via `rt_cpuid` extern | Assume SSE2 only |
| ARM Linux | Parse `/proc/cpuinfo` features: `asimd`, `fphp`, `asimdhp`, `sve`, `sve2` | Architecture-level: AArch64 guarantees NEON |
| ARM SVE2 VL | Read `DCZID_EL0` is insufficient; use `svcntb()` → `sve_vl_bits = svcntb() * 8` at process start via `rt_sve_vl` extern | Default 128 if probe unavailable |
| RISC-V Linux | `csrr a0, vlenb` at startup via `rt_riscv_vlenb` extern; parse `/proc/cpuinfo` for `v` extension | Default `vlenb = 16` (VLEN=128) if unavailable |
| RISC-V non-Linux | ISA string parse from device-tree / environment | Default minimal |
| ARM macOS / iOS | `sysctlbyname("hw.optional.arm.FEAT_SVE")` → 1 if present | Parse `hw.cpufamily` |

The existing `/proc/cpuinfo` parsing in `simd_platform.spl` (detect_x86, detect_arm) is the
foundation; it is extended to populate `SimdFeatureFlags` fields rather than a single enum value.

### 6.4 `mrs ID_AA64ZFR0_EL1` for SVE2 Feature Sub-registers

On AArch64 bare-metal or privileged contexts, reading `ID_AA64ZFR0_EL1` reveals SVE feature bits
(BF16, I8MM, F32MM, F64MM). In userland, this is not directly accessible; the SVE feature detection
relies on `/proc/cpuinfo` `sve2` flag or `HWCAP2_SVE2` from `getauxval(AT_HWCAP2)`. The `rt_sve_vl`
extern path also queries `AT_HWCAP2` via the runtime.

---

## 7. GPU / CUDA Integration

### 7.1 Model: Warp-as-Vector

PTX uses **implicit SIMD**: the programmer writes scalar per-thread code; hardware schedules 32
threads simultaneously as a warp (A1 §3.1). `FixedVec<T, 32>` does NOT map to a single PTX register;
it maps to 32 independent scalar registers across 32 threads. The `WarpVec<T>` extension (§2.6)
exposes the warp-scoped communication that is unavailable in the CPU SIMD model.

`ScalableVec<T>` has **no direct PTX lowering**. Use `WarpVec<T>` instead for GPU kernels.

### 7.2 PTX Lowering

| Vector trait method | PTX lowering |
|--------------------|-------------|
| `splat(x)` | each thread holds `x` in a scalar register |
| `add(a, b)` | `add.f32 %d, %a, %b` per thread |
| `fma(a, b, c)` | `fma.rn.f32 %d, %a, %b, %c` per thread |
| `load(ptr)` | `ld.global.f32 %d, [%ptr]` (stride-1 → coalesced) |
| `gather(base, idx)` | scalar loop per thread — coalescing concern (A1 §3.3 §2) |
| `reduce_sum(v)` | `shfl.sync.bfly` tree over 5 steps |
| `select(mask, t, f)` | `@%p0 mov.f32 %d, %t; @!%p0 mov.f32 %d, %f` |
| `FixedVec<f32,4>::load` | `ld.global.v4.f32 {%d0,%d1,%d2,%d3}, [%ptr]` (packed) |

The existing `ptx_builder.spl:197–234` covers scalar arithmetic; `.v4` packed loads and `shfl.sync`
are the new additions required.

### 7.3 SPIR-V / Vulkan Compute

| Vector trait method | SPIR-V lowering |
|--------------------|----------------|
| `add(a, b)` | `OpFAdd` / `OpIAdd` |
| `mul(a, b)` | `OpFMul` / `OpIMul` |
| `fma(a, b, c)` | `OpExtInst GLSL.std.450 Fma` |
| `eq(a, b)` | `OpFOrdEqual` → `bool` per invocation |
| `reduce_sum(v)` | `OpGroupNonUniformFAdd` (subgroup scope) |
| `select(mask, t, f)` | `OpSelect` |
| `shfl_idx (WarpVec)` | `OpGroupNonUniformShuffle` |
| `warp_ballot` | `OpGroupNonUniformBallot` |

`FixedVec<f32, 4>` maps to SPIR-V `OpTypeVector float32 4`. The existing `spirv_builder.spl` has
`OpFAdd`, `OpIMul`, `OpLoad`, `OpStore`, and barrier ops; vector type declarations and subgroup ops
are the new additions.

### 7.4 Warp-as-Vector Abstraction Leaks (A1 §3.3)

These four leaks are **by design** — they reflect hardware reality, not a design flaw:

1. **Warp divergence penalty**: CPU SIMD masks all lanes to the same instruction. GPU divergence
   serializes different instruction sequences. `Vector::select` generates zero divergence on CPU;
   it can serialize on GPU if different threads take different branches through a `select` chain.
   **Impact on trait**: `select` is correctly represented; performance semantics differ.

2. **Memory coalescing requirement**: `Vector::gather(base, idx)` is a native CPU instruction
   (AVX2, SVE2, RVV). On GPU, 32 threads with non-contiguous `idx` generate 32 separate memory
   transactions. **Impact**: `gather` over `WarpVec` emits a scalar loop; the backend should warn
   when gather is inside a hot kernel loop.

3. **Shared memory vs L1**: `Vector::load`/`store` assume flat address space. GPU smem (`__shared__`)
   must be explicitly allocated. **Impact**: the `Vector` trait does not model smem; kernel authors
   use raw pointers to shared allocations and then load into `WarpVec`.

4. **Subgroup size portability**: `WarpVec` hardcodes 32-lane warp for PTX. SPIR-V `SubgroupSize`
   is a built-in variable — AMD GPUs use 64, Intel GPUs use variable sizes. **Impact**: `WarpVec`
   ops on SPIR-V are subgroup-scoped, not warp-scoped; the exact `SubgroupSize` must be queried at
   runtime or fixed via `VkPipelineShaderStageRequiredSubgroupSizeCreateInfo`.

Full kernel code generation (grid/block launch, occupancy, smem allocation) is deferred to B3
rollout plan.

---

## 8. Anti-Pattern Callouts & Migration

### 8.1 Hardcoded Scalar Structs — Mark for Removal

The following five structs in `src/compiler/30.types/simd_vector_types.spl` are **deprecated**:

| Old type | Lines | Problem |
|----------|-------|---------|
| `struct Vec2f` | :12 | scalar field ops; no SIMD lowering |
| `struct Vec4f` | :57 | scalar field ops including `add` at :116 |
| `struct Vec8f` | :323 | scalar field ops |
| `struct Vec2d` | :395 | scalar field ops |
| `struct Vec4d` | :440 | scalar field ops |

All five implement arithmetic as element-wise scalar Simple code, NOT via `rt_simd_*` intrinsic
calls (A2 §8, confirmed anti-pattern). They therefore never produce `SimdAddF32x4` or any other
`SimdXxx` MIR instruction.

`SimdCapabilities` as a single-level enum (A2 §8 anti-pattern) is replaced by `SimdFeatureFlags`
(§6.2).

`SimdIntrinsics` in `simd_platform.spl` is a dead layer (A2 §8 confirmed); it is deleted when the
new `Vector` trait + backend intrinsics path is in place.

The duplicate `SimdElementType` definition (A2 §8 — in both `00.common/simd_types.spl` and
`35.semantics/simd_check.spl`) is consolidated to `00.common/simd_types.spl` only.

### 8.2 Migration Aliases

Callers of the old types receive **type aliases** in `30.types/simd_vector_types.spl` during the
migration window:

```
type Vec2f = FixedVec<f32, 2>
type Vec4f = FixedVec<f32, 4>
type Vec8f = FixedVec<f32, 8>
type Vec2d = FixedVec<f64, 2>
type Vec4d = FixedVec<f64, 4>
```

These aliases preserve call-site compatibility. Existing `Vec4f.x`, `.y`, `.z`, `.w` field
accesses must be migrated to `extract(0)`, `extract(1)`, `extract(2)`, `extract(3)` or to
named wrapper functions — the opaque `FixedVec<T,N>` storage has no user-visible fields.

**Geometry code** in `src/lib/nogc_sync_mut/engine/render/vector.spl` (positional Vec3/Vec4) and
`src/lib/common/linear_algebra/vector_ops.spl` (dot/cross/norm) retains its own named-field structs
(`x`, `y`, `z`, `w`) because positional semantics are distinct from SIMD lane semantics. These
files are NOT migrated to `FixedVec<T,N>`. They may optionally call `FixedVec` internally for
SIMD acceleration but that is an implementation detail.

### 8.3 Library Location

The user-facing SIMD library at `src/lib/nogc_sync_mut/simd.spl` is the current single-file surface.
It is expanded into a directory `src/lib/nogc_sync_mut/simd/` with the following modules:

```
src/lib/nogc_sync_mut/simd/
    __init__.spl       # re-exports Vector, Mask, FixedVec, ScalableVec, WarpVec
    fixed_vec.spl      # FixedVec<T,N> + FixedMask<N>
    scalable_vec.spl   # ScalableVec<T> + ScalableMask
    warp_vec.spl       # WarpVec<T> (GPU only)
    platform.spl       # SimdFeatureFlags + detect()
    compat.spl         # deprecated aliases: Vec4f, Vec8f, etc.
```

`use std.simd` resolves to `src/lib/nogc_sync_mut/simd/__init__.spl` (via the `nogc_sync_mut`
namespace; MDSOC outer layer, no GC, no async).

---

## 9. Open Questions

**OQ-1: Should `ScalableVec<T>` support a static lower-bound constraint?**

Example syntax: `ScalableVec<f32> where vscale_lanes >= 4`. This would allow the compiler to skip
strip-mining when the minimum VL is guaranteed. The risk: it creates unportable code (a program
compiled with `>= 4` fails on an SVE2 implementation with VL=128 bits / 4 f32 lanes only if the
loop count is not a multiple of 4). Recommendation: do NOT add the constraint to the type system
in the initial design. Instead, add a `@min_vl(N)` function annotation that the backend validates
against the runtime capability, emitting a runtime assertion.

**OQ-2: FP16 / BF16 fallback strategy.**

`SimdFeatureFlags.has_fp16` and `has_bf16` are detected (§6.2). When FP16 is not natively supported,
should the compiler auto-promote to f32 (expand each FP16 lane to f32, operate, narrow back) or
emit a compile-time error? Recommendation: auto-promote with a diagnostic warning for `FixedVec<f16, N>`.
The `narrow` / `widen` trait methods (§2.1) are the explicit user path. Note: a `f16` type is not
yet confirmed in Simple's type system; this is a dependency.

**OQ-3: Monomorphization budget for `FixedVec<T, N>`.**

Unconstrained `FixedVec<T, N>` could generate a combinatorial explosion of specializations. Practical
cap: N in {2, 4, 8, 16, 32, 64} and T in {u8, u16, u32, u64, i8, i16, i32, i64, f32, f64, f16,
bf16}. Combinations that have no hardware support on any target (e.g., `FixedVec<f64, 16>` on SSE
targets) fall back to scalar. Recommendation: reject unsupported N×T combinations at the `simd_check`
layer with a clear error, rather than silently scalarizing.

**OQ-4: Auto-vectorization opt-in vs opt-out.**

Currently auto-vec is implicitly attempted on any qualifying loop. Should it require an explicit
`@simd` annotation to avoid surprising performance cliffs? Recommendation: keep implicit-on for
simple elementwise loops (the 1.5× cost threshold in `auto_vectorize_cost.spl` is conservative);
require `@simd` for loops with scatter/gather or permute ops inside.

**OQ-5: Alignment guarantee for `load_aligned`/`store_aligned`.**

`FixedVec<f32,8>` requires 32-byte alignment for AVX2 `_mm256_load_ps`. Simple has no `align(N)`
attribute on stack allocations yet. Recommendation: add `@align(32)` annotation or wrap in an
`Aligned<V>` newtype that enforces alignment at the type level; `load` and `load_aligned` remain
distinct (caller's responsibility); the backend should emit `vmovups` not `vmovaps` when alignment
is unproven.

**OQ-6: Auto-vectorizer pipeline wiring.**

As noted in §5.1 and A2 §7, `auto_vectorize_codegen.spl` produces real `SimdXxx` MIR but the call
site in the MIR optimisation driver is unconfirmed. Before the new architecture is declared
functionally complete, this wiring must be verified and, if absent, added. This is the highest-risk
gap in the current code.

---

## Cross-References

- Wave A1 ISA Survey: `doc/01_research/simd_isa_survey_2026-05-02.md`
  - §1.1–1.4: NEON, SSE, AVX, AVX-512 register models and op tables
  - §2.1–2.2: SVE2 and RVV vscale / LMUL model
  - §3.3: Warp-as-vector abstraction leaks (four leaks enumerated in §7.4 here)
  - §4: Cross-ISA op coverage matrix (primary input for §2.1 trait method list)
  - §5: Predication model recommendations (input for §4 here)
  - §6: vscale/LMUL type system recommendation (basis for locked decision: LMUL hidden)
- Wave A2 Internal State: `doc/01_research/simd_internal_state_2026-05-02.md`
  - §1b: Vec4f scalar impl anti-pattern → §8.1 here
  - §2: Lowering pipeline today (dead Vec4f::add path) → §3.2 50.mir row
  - §4: Platform detection gaps → §6.1 here
  - §6: Auto-vectorizer state → §5 here
  - §7: Gap map (35-row) → §3.2 change summary
  - §8: Anti-pattern flags → §8.1 here
- Existing architecture: `doc/04_architecture/portable_simd_fp_modules.md` — superseded by this doc
- GPU acceleration: `doc/04_architecture/gpu_acceleration_plan.md`
- B2 strict-emit op tables: `doc/04_architecture/simd_backend_strict_emit.md`
- B3 rollout plan: `doc/05_design/simd_rollout_plan.md`
