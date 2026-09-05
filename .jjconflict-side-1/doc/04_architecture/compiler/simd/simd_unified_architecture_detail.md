<!-- claude-arch -->
# Architecture: Unified SIMD — Detail (Round 2)

**TL;DR:** Round 2 specifies every trait method signature, exact diagnostic codes,
monomorphization decision tables, `ScalableVec<T>` vscale ABI, Mask semantics, WarpVec
extension catalog, interpreter-mode parity rules, the new MIR opcodes required, frontend
syntax additions, and the `src/lib/nogc_sync_mut/simd/` file layout. It is the
IDE-tooltip / ABI-spec companion to Round-1 `simd_unified_architecture.md` (B1). Do not
implement from Round 1 alone; all compiler contracts are specified here.

---

## §0 Reading Order

| Section | Audience |
|---------|----------|
| §1 Trait method catalog | Implementors of `vector.spl`, `fixed.spl`, `scalable.spl`, `mask.spl`, `warp.spl` |
| §2 Type-system rules | Implementors of `35.semantics/simd_check.spl`, `40.mono/` |
| §3 Monomorphization rules | Implementors of `40.mono/`, `50.mir/mir_lowering_expr.spl` |
| §4 ScalableVec semantics | Implementors of `scalable.spl`, `50.mir/`, `60.mir_opt/lmul_widen.spl` |
| §5 Mask semantics | Implementors of `mask.spl`, `60.mir_opt/predicate_promote.spl` |
| §6 WarpVec extension | Implementors of `warp.spl`, `35.semantics/gpu_checker.spl` |
| §7 Interpreter parity | Implementors of `interp/` evaluation layer |
| §8 MIR opcodes | Implementors of `50.mir/`, `60.mir_opt/` |
| §9 Diagnostic catalog | All — error/warning handling |
| §10 Frontend syntax | Implementors of `00.parse/`, `10.lex/` |
| §11 Stdlib landing zone | Implementors of `src/lib/nogc_sync_mut/simd/` |
| §12 Open questions | Architects — unresolved; requires design decisions |

Cross-references to Round-1 use prefix **B1** (architecture) or **B2** (strict-emit).
Cross-references to C1 research docs use **C1-ISA** (survey) or **C1-DEEP** (ISA deep).

---

## §1 Complete Trait Method Catalog

### §1.0 T and N Constraints (shared conventions)

| Symbol | Meaning |
|--------|---------|
| `T: Numeric` | Any numeric scalar: `u8 u16 u32 u64 i8 i16 i32 i64 f32 f64` (and `f16`/`bf16` once confirmed in Simple's type system — see §12 OQ-F) |
| `T: Float` | Float subset of Numeric: `f32 f64` (and `f16`/`bf16`) |
| `T: Integer` | Integer subset: `u8 u16 u32 u64 i8 i16 i32 i64` |
| `T: SignedInt` | Signed integer: `i8 i16 i32 i64` |
| `N: Pow2` | N ∈ {2, 4, 8, 16, 32, 64} — compile-time const, power-of-two |
| `N: TargetValid` | N is Pow2 AND (T,N) pair has at least one backend lowering (see §3 decision table) |

N=0, N=1, and non-power-of-two values emit **`E_SIMD_BAD_LANES`** at the type-check phase.
See §2 and §9 for full validation rules.

---

### §1.1 `Vector` Trait — Core Abstract Operations

The `Vector` trait is the shared contract for all SIMD vector types. It has NO
constructors — those live on the concrete type (`FixedVec`, `ScalableVec`). Associated
types must be declared by each implementor.

```
trait Vector:
    type Elem        # element scalar type
    type Mask        # associated mask type — Mask<Self>

    # — Arithmetic —
    fn add(self, rhs: Self) -> Self
    fn sub(self, rhs: Self) -> Self
    fn mul(self, rhs: Self) -> Self
    fn fma(self, b: Self, c: Self) -> Self     # self*b + c
    fn fnmadd(self, b: Self, c: Self) -> Self  # -(self*b) + c
    fn abs(self) -> Self                        # T: Float only
    fn neg(self) -> Self
    fn min(self, rhs: Self) -> Self
    fn max(self, rhs: Self) -> Self

    # — Bitwise (T: Integer only) —
    fn and(self, rhs: Self) -> Self
    fn or(self, rhs: Self) -> Self
    fn xor(self, rhs: Self) -> Self
    fn andnot(self, rhs: Self) -> Self         # ~self & rhs
    fn shl(self, count: u32) -> Self
    fn shr_logical(self, count: u32) -> Self   # zero-fill
    fn shr_arith(self, count: u32) -> Self     # T: SignedInt

    # — Comparison → Mask —
    fn cmp_eq(self, rhs: Self) -> Self.Mask
    fn cmp_ne(self, rhs: Self) -> Self.Mask
    fn cmp_lt(self, rhs: Self) -> Self.Mask
    fn cmp_le(self, rhs: Self) -> Self.Mask
    fn cmp_gt(self, rhs: Self) -> Self.Mask
    fn cmp_ge(self, rhs: Self) -> Self.Mask

    # — Selection / blend —
    fn mask_select(mask: Self.Mask, t: Self, f: Self) -> Self

    # — Reduction → scalar —
    fn reduce_sum(self) -> Self.Elem
    fn reduce_min(self) -> Self.Elem
    fn reduce_max(self) -> Self.Elem
    fn reduce_and(self) -> Self.Elem           # T: Integer
    fn reduce_or(self) -> Self.Elem            # T: Integer

    # — Permutation / shuffle —
    fn shuffle(self, indices: Self) -> Self    # indices are integer lanes
    fn permute(self, ctrl: Self) -> Self       # same as shuffle but compile-time ctrl
    fn broadcast_lane(self, lane: u32) -> Self
    fn interleave_lo(self, rhs: Self) -> Self
    fn interleave_hi(self, rhs: Self) -> Self

    # — Load / store —
    static fn load_aligned(ptr: *T) -> Self
    static fn load_unaligned(ptr: *T) -> Self
    fn store_aligned(self, ptr: *T)
    fn store_unaligned(self, ptr: *T)

    # — Gather / scatter —
    static fn gather(base: *T, indices: Self) -> Self   # indices T: Integer
    fn scatter(self, base: *T, indices: Self)            # indices T: Integer

    # — Lane count —
    fn lanes(self) -> usize       # runtime for ScalableVec; const for FixedVec
    fn len(self) -> usize         # alias for lanes()

    # — Lane access — (see §10 for indexing syntax)
    fn lane(self, i: usize) -> Self.Elem       # bounds-check in interp; UB if i>=lanes() in compiled
    fn set_lane(self, i: usize, v: Self.Elem) -> Self

    # — Debug —
    fn fmt(self) -> text
    fn to_string(self) -> text    # alias for fmt()

    # — Iteration —
    fn iter(self) -> LaneIter<Self.Elem>    # yields elements in lane order
```

**Table 1.1-A — `Vector` trait method constraints and diagnostics**

| Method | T constraint | N constraint | Pre-conditions | Diagnostic on violation |
|--------|-------------|-------------|----------------|------------------------|
| `add` `sub` `mul` | Numeric | — | — | `E_SIMD_TYPE_MISMATCH` |
| `fma` `fnmadd` | Float | — | — | `E_SIMD_FLOAT_ONLY` |
| `abs` | Float | — | — | `E_SIMD_FLOAT_ONLY` |
| `neg` | Numeric | — | — | — |
| `min` `max` | Numeric | — | — | — |
| `and` `or` `xor` `andnot` | Integer | — | — | `E_SIMD_INT_ONLY` |
| `shl` `shr_logical` | Integer | — | count < elem_bits | `E_SIMD_SHIFT_OOB` |
| `shr_arith` | SignedInt | — | count < elem_bits | `E_SIMD_INT_ONLY` + `E_SIMD_SHIFT_OOB` |
| `cmp_*` | Numeric | — | — | `E_SIMD_TYPE_MISMATCH` |
| `mask_select` | Numeric | — | mask lane count == vector lane count | `E_SIMD_LANE_MISMATCH` |
| `reduce_*` | Numeric | — | — | `E_SIMD_TYPE_MISMATCH` |
| `reduce_and` `reduce_or` | Integer | — | — | `E_SIMD_INT_ONLY` |
| `shuffle` | Numeric | — | indices must be integer T | `E_SIMD_TYPE_MISMATCH` |
| `permute` | Numeric | — | ctrl must be compile-time const | `E_SIMD_CONST_REQUIRED` |
| `broadcast_lane` | Numeric | — | lane < lanes() | `E_SIMD_LANE_OOB` |
| `load_aligned` `store_aligned` | Numeric | — | ptr aligned to N*sizeof(T) | — (UB if violated; no runtime check in compiled) |
| `gather` `scatter` | Numeric | — | indices T: Integer | `E_SIMD_TYPE_MISMATCH` |
| `lane` `set_lane` | Numeric | — | i < lanes() | `E_SIMD_LANE_OOB` (interp only; see §7) |

---

### §1.2 `FixedVec<T, const N>` — Additional Methods

`FixedVec<T,N>` implements `Vector` and adds compile-time-constant ops:

```
class FixedVec<T, const N: usize>:
    type Elem = T
    type Mask = Mask<FixedVec<T, N>>

impl<T: Numeric, const N: usize> FixedVec<T, N>:

    # — Construction —
    static fn splat(val: T) -> Self
    static fn zero() -> Self                              # splat(0)
    static fn from_array(arr: [T]) -> Self                # arr.len() must == N
    static fn from_slice(s: &[T]) -> Self                 # s.len() must >= N
    fn to_array(self) -> [T; N]
    fn to_slice(self, out: &mut [T])                      # out.len() must >= N

    # — Type conversion —
    fn cast<U: Numeric>(self) -> FixedVec<U, N>           # element-wise numeric cast
    fn widen(self) -> FixedVec<U, N> where U is 2x-width of T   # e.g. i16→i32
    fn narrow(self) -> FixedVec<U, N> where U is half-width of T # with saturation

    # — ScalableVec interop —
    fn to_scalable(self) -> ScalableVec<T>                # always valid; pads if needed
    static fn try_from_scalable(v: ScalableVec<T>) -> Option<FixedVec<T, N>>  # runtime check

    # — Compile-time lane metadata —
    const fn lane_count() -> usize                        # always N
    const fn byte_width() -> usize                        # N * sizeof(T)

    # — Zip / spread —
    fn zip_lo(self, rhs: Self) -> Self                    # = interleave_lo
    fn zip_hi(self, rhs: Self) -> Self                    # = interleave_hi
    fn unzip_even(self) -> FixedVec<T, N/2>
    fn unzip_odd(self) -> FixedVec<T, N/2>

    # — Preferred-lane hint (const) —
    static const fn preferred_lanes_for_target() -> usize  # see §3.3
```

**Table 1.2-A — `FixedVec<T,N>` construction / conversion diagnostics**

| Method | Constraint | Diagnostic |
|--------|-----------|------------|
| `from_array(arr)` | `arr.len() == N` | `E_SIMD_ARRAY_LEN_MISMATCH` |
| `from_slice(s)` | `s.len() >= N` | `E_SIMD_SLICE_TOO_SHORT` |
| `cast<U>()` | U: Numeric | `E_SIMD_TYPE_MISMATCH` |
| `widen()` | T width × 2 must be valid Simple numeric type | `E_SIMD_NO_WIDEN_TYPE` |
| `narrow()` | T width / 2 must be valid Simple numeric type | `E_SIMD_NO_NARROW_TYPE` |
| `to_scalable()` | N <= min_lanes for target | `W_SIMD_FIXED_EXCEEDS_MIN_LANES` (warning, not error) |
| `try_from_scalable()` | runtime: `v.lanes() == N` | returns `Option.None` (no error) |
| `unzip_even()` `unzip_odd()` | N must be even (N >= 2) | `E_SIMD_BAD_LANES` |

---

### §1.3 `ScalableVec<T>` — Additional Methods

`ScalableVec<T>` implements `Vector` with runtime-determined lane count.

```
class ScalableVec<T>:
    type Elem = T
    type Mask = Mask<ScalableVec<T>>

impl<T: Numeric> ScalableVec<T>:

    # — Construction —
    static fn splat(val: T) -> Self                       # runtime lanes
    static fn splat_n(val: T, n: usize) -> Self           # explicit lane count
    static fn zero() -> Self

    # — Lane count (runtime) —
    fn lanes(self) -> usize                               # calls svcntw/vlenb ABI (see §4)
    fn len(self) -> usize                                 # alias
    static const fn min_lanes() -> usize                  # compile-time architectural minimum (see §4)

    # — Interop with FixedVec —
    static fn from_fixed<const N: usize>(v: FixedVec<T, N>) -> Self
        # N <= min_lanes() required; else E_SIMD_FIXED_OVERFLOWS_SCALABLE
    fn try_to_fixed<const N: usize>(self) -> Option<FixedVec<T, N>>
        # runtime check: self.lanes() == N

    # — Load / store (stride-aware) —
    static fn load_strided(ptr: *T, stride: usize, n: usize) -> Self
    fn store_strided(self, ptr: *T, stride: usize)

    # — PTX: not supported —
    # All ScalableVec methods emit E_SIMD_PTX_NO_SCALABLE if target is PTX/CUDA
```

**Table 1.3-A — `ScalableVec<T>` diagnostics**

| Method | Constraint | Diagnostic |
|--------|-----------|------------|
| `from_fixed(v)` | N <= `min_lanes()` | `E_SIMD_FIXED_OVERFLOWS_SCALABLE` |
| `try_to_fixed()` | runtime lanes == N | returns `None`; no error |
| Any method on PTX target | — | `E_SIMD_PTX_NO_SCALABLE` |
| `splat_n(val, n)` | n > 0 | `E_SIMD_BAD_LANES` |

---

### §1.4 `Mask<V>` — Full Method Catalog

`Mask<V>` is parameterized by the vector type `V` (not just lane count). This preserves
element-width information needed for SVE2 predicate granularity and RVV mask layout.
`Mask<FixedVec<f32,4>>` and `Mask<FixedVec<i32,4>>` are distinct types even though both
have 4 lanes; they carry different per-lane byte widths used in backend mask-register
allocation. See §5 for the materialization decision table.

```
trait Mask<V: Vector>:
    type Vec = V

impl<V: Vector> Mask<V>:

    # — Construction —
    static fn from_bits(bits: u64) -> Self
        # bits[i] == 1 means lane i is active; N bits used, rest ignored
        # For ScalableVec: bits must fit in runtime lanes count; else E_SIMD_MASK_BITS_OOB
    static fn all_ones() -> Self
    static fn all_zeros() -> Self
    static fn from_cmp(cmp_result: V.Mask) -> Self        # identity cast

    # — Logical operations —
    fn and(self, rhs: Self) -> Self
    fn or(self, rhs: Self) -> Self
    fn xor(self, rhs: Self) -> Self
    fn not(self) -> Self
    fn andnot(self, rhs: Self) -> Self    # ~self & rhs

    # — Queries —
    fn count_ones(self) -> usize
    fn any(self) -> bool
    fn all(self) -> bool
    fn none(self) -> bool
    fn lane_active(self, i: usize) -> bool   # single-lane test

    # — Conversion —
    fn to_bits(self) -> u64    # low N bits set per active lane; N must be <= 64
    fn to_bitmask_u32(self) -> u32   # for AVX-512 k-reg extraction (N <= 32)

    # — PTX predicate handle (compile-only) —
    fn ptx_preg_handle(self) -> u32   # E_SIMD_COMPILE_ONLY in interpreter (see §7)
```

**Table 1.4-A — `Mask<V>` diagnostics**

| Method | Constraint | Diagnostic |
|--------|-----------|------------|
| `from_bits(bits)` | For FixedVec<T,N>: N <= 64 | `E_SIMD_MASK_BITS_OOB` |
| `to_bits()` | lane count <= 64 | `E_SIMD_MASK_BITS_OOB` |
| `to_bitmask_u32()` | lane count <= 32 | `E_SIMD_MASK_BITS_OOB` |
| `ptx_preg_handle()` | compile mode only | `E_SIMD_COMPILE_ONLY` |
| `lane_active(i)` | i < lane count | `E_SIMD_LANE_OOB` |

---

### §1.5 `WarpVec<T>` — GPU-Only Extension Trait

`WarpVec<T>` extends `Vector` for CUDA/PTX and SPIR-V subgroup targets.
Calling any method outside a GPU kernel context is a compile-time error enforced by
`35.semantics/gpu_checker.spl`.

```
trait WarpVec<T: Numeric>: Vector:
    # — Shuffle within warp —
    fn shfl_up(self, delta: u32, mask: u32) -> Self
        # Shift value from lane (self_lane - delta); mask includes self; lane bound: delta < 32
    fn shfl_down(self, delta: u32, mask: u32) -> Self
        # Shift value from lane (self_lane + delta); mask includes self
    fn shfl_xor(self, lane_mask: u32, mask: u32) -> Self
        # XOR lane id with lane_mask to select source; shfl_bfly in B1
    fn shfl_idx(self, src_lane: u32, mask: u32) -> Self
        # Broadcast from specific src_lane; 0 <= src_lane < warp_size

    # — Warp reductions → scalar —
    fn warp_reduce_sum(self, mask: u32) -> T
    fn warp_reduce_min(self, mask: u32) -> T
    fn warp_reduce_max(self, mask: u32) -> T
    fn warp_reduce_any(self, mask: u32) -> bool    # T: Integer
    fn warp_reduce_all(self, mask: u32) -> bool    # T: Integer

    # — Ballot / vote —
    static fn warp_ballot(predicate: bool, mask: u32) -> u32
        # PTX: vote.sync.ballot.b32; SPIR-V: OpGroupNonUniformBallot
    static fn warp_active_mask() -> u32
        # PTX: activemask.b32; SPIR-V: OpSubgroupMask built-in

    # — Synchronization —
    static fn warp_sync(mask: u32)
        # PTX: bar.warp.sync; ensures all threads in mask reach this point
        # SPIR-V: OpControlBarrier(Subgroup, Subgroup, AcquireRelease)

    # — Subgroup size queries —
    static const fn target_warp_size_const() -> usize
        # Compile-time const: PTX → 32; SPIR-V/Vulkan → determined by pipeline specialization const
        # Returns E_WARP_SIZE_RUNTIME_ONLY if not known at compile time
    static fn target_warp_size_runtime() -> usize
        # Runtime value; PTX: reads warpSize; SPIR-V: reads gl_SubgroupSize built-in
    static fn subgroup_size_query() -> usize
        # Alias for target_warp_size_runtime(); preferred name for SPIR-V contexts
```

**Table 1.5-A — `WarpVec<T>` constraints and diagnostics**

| Method | T constraint | Pre-condition | Diagnostic |
|--------|-------------|---------------|------------|
| `shfl_up` `shfl_down` | Numeric | delta < warp_size, mask bit for self-lane is set | `E_WARP_DELTA_OOB`, `E_WARP_SELF_EXCLUDED` |
| `shfl_xor` | Numeric | mask bit for self-lane is set | `E_WARP_SELF_EXCLUDED` |
| `shfl_idx` | Numeric | 0 <= src_lane < warp_size | `E_WARP_LANE_OOB` |
| `warp_reduce_any` `warp_reduce_all` | Integer | — | `E_SIMD_INT_ONLY` |
| `warp_ballot` | — | predicate is bool | — |
| `warp_sync` | — | mask != 0 | `W_WARP_SYNC_EMPTY_MASK` |
| Any WarpVec method on CPU target | — | must be inside kernel fn | `E_WARP_NOT_IN_KERNEL` |
| Any WarpVec method on Apple M-series | — | — | `E_WARP_NO_APPLE_M` |

---

### §1.6 Method Count Summary

| Type | Core Vector methods | Type-specific methods | Total |
|------|--------------------|----------------------|-------|
| `Vector` (trait) | 39 | — | 39 |
| `FixedVec<T,N>` | (inherits 39) | 20 | 59 |
| `ScalableVec<T>` | (inherits 39) | 10 | 49 |
| `Mask<V>` | — | 18 | 18 |
| `WarpVec<T>` | (inherits 39) | 16 | 55 |
| **Total distinct rows** | | | **~131** |

---

## §2 Type-System Rules

### §2.1 Const-N Validity

Valid N values for `FixedVec<T, const N>`:

```
N ∈ {2, 4, 8, 16, 32, 64}
```

All other values (including 0, 1, 3, 5, 6, 7, etc.) emit `E_SIMD_BAD_LANES` at
the type-check phase (`35.semantics/simd_check.spl`). This cap enforces the
monomorphization budget from B1 §9 OQ-3.

**Preferred N per target and T** (citing C1-DEEP §4 latency tables):

| Target | T | Preferred N | Notes |
|--------|---|-------------|-------|
| x86-64 AVX-512 | f32 | 16 | Full ZMM register; C1-DEEP §4.1 |
| x86-64 AVX-512 | f64 | 8 | Full ZMM register |
| x86-64 AVX-512 | i32 | 16 | Full ZMM register |
| x86-64 AVX-512 | i64 | 8 | Full ZMM register |
| x86-64 AVX2 | f32 | 8 | Full YMM register |
| x86-64 AVX2 | f64 | 4 | Full YMM register |
| x86-64 AVX2 | i32 | 8 | Full YMM register |
| x86-64 SSE2 | f32 | 4 | Full XMM register |
| x86-64 SSE2 | f64 | 2 | Full XMM register |
| x86-64 SSE2 | i32 | 4 | Full XMM register |
| ARM NEON (AArch64) | f32 | 4 | Full Q-register; C1-ISA §1.1 |
| ARM NEON (AArch64) | f64 | 2 | Full Q-register |
| ARM NEON (AArch64) | i32 | 4 | Full Q-register |
| ARM SVE2 | f32 | 4 (min_lanes) | VL-agnostic; prefer ScalableVec; C1-ISA §2.1 |
| RISC-V RVV | f32 | 4 (at VLEN=128, LMUL=1) | VL-agnostic; prefer ScalableVec; C1-ISA §2.2 |
| PTX/CUDA | f32 | 1 per thread (32 threads = warp) | Use WarpVec for cross-lane; C1-ISA §3.1 |

Users can query at compile time:

```
val n = FixedVec<f32, 4>::preferred_lanes_for_target()
```

This returns a compile-time usize const derived from `SimdFeatureFlags` (B1 §6).

### §2.2 Auto-Coercion Rules

`FixedVec<T,N>` literals are **never auto-created**. The following rules apply:

1. `splat(0.0)` on `FixedVec<f32,4>` — valid; `T` inferred as `f32`, `N` inferred from context.
   - If context is ambiguous (no annotation and no expected type), emits `E_SIMD_TYPE_AMBIGUOUS`.
2. `splat(0)` — `T` defaults to `i32` if no annotation; `N` must be explicit or context-inferred.
3. `[1.0f32; lanes 4]` (vector literal syntax, §10) → `FixedVec<f32,4>` directly.
4. **No implicit cast** between `FixedVec<f32,4>` and `FixedVec<f64,4>` — use `.cast<f64>()`.
5. **No implicit cast** between `FixedVec<f32,4>` and `FixedVec<f32,8>` — these are different types.

### §2.3 Mask Type Identity Rules

`Mask<V>` is a distinct type for each `V`:

- `Mask<FixedVec<f32,4>>` ≠ `Mask<FixedVec<i32,4>>` — different types.
  - Rationale: SVE2 predicate registers are element-width-sensitive (bit-per-byte vs
    bit-per-element); RVV v0 layout depends on SEW. Separating them preserves exact
    backend semantics without coercion. C1-ISA §2.1, §2.2.
  - AVX-512 k-registers are bit-per-lane regardless of element width, so both types
    lower to k-regs but remain separately typed at the Simple level.
- `Mask<FixedVec<f32,4>>` ≠ `Mask<FixedVec<f32,8>>` — different lane count.
- `Mask<ScalableVec<f32>>` ≠ `Mask<ScalableVec<i32>>` — separate scalable masks.
- Comparing or blending masks of different V emits `E_SIMD_MASK_TYPE_MISMATCH`.

### §2.4 Generic Bounds Composition

`where T: Numeric` and `where N: Pow2` compose as AND constraints. Both must hold.

**Table 2.4-A — Accepted/Rejected Type Examples**

| Type | Status | Reason |
|------|--------|--------|
| `FixedVec<f32, 4>` | Accepted | T=f32 ∈ Numeric; N=4 ∈ Pow2; has backend lowering |
| `FixedVec<f64, 16>` | Accepted (with warning) | Valid types; no AVX-512-f64x16 exists — emits `W_SIMD_NO_NATIVE_LOWERING`, falls back to scalar or split |
| `FixedVec<bool, 4>` | Rejected | `bool` ∉ Numeric — emits `E_SIMD_TYPE_MISMATCH` |
| `FixedVec<f32, 3>` | Rejected | N=3 ∉ Pow2 — emits `E_SIMD_BAD_LANES` |
| `FixedVec<i32, 0>` | Rejected | N=0 — emits `E_SIMD_BAD_LANES` |
| `FixedVec<*T, 4>` | Rejected | pointer ∉ Numeric — emits `E_SIMD_TYPE_MISMATCH` |
| `ScalableVec<f32>` | Accepted | T=f32 ∈ Numeric; N is runtime |
| `Mask<FixedVec<f32,4>>` | Accepted | valid mask for 4-lane f32 vector |
| `FixedVec<i8, 64>` | Accepted | i8 ∈ Numeric; N=64 ∈ Pow2; maps to 512-bit AVX-512 |
| `FixedVec<f32, 1>` | Rejected | N=1 — emits `E_SIMD_BAD_LANES` |

### §2.5 Trait-Impl Visibility

`[T; N]` (plain Simple arrays) do **NOT** automatically implement `Vector`. The SIMD
types are opt-in; users explicitly use `FixedVec` or `ScalableVec`. The conversion path
is `FixedVec<T,N>::from_array(arr)` and `.to_array()`.

This avoids ambiguity between array ops and SIMD ops and prevents unintended SIMD
codegen on value types.

No blanket impl of `Vector` for any standard library type.

---

## §3 Monomorphization Rules

### §3.1 Decision Table: (target, T, N) → backend module

`FixedVec<T,N>` is fully monomorphized at the call site. The compiler selects the
backend lowering module using this priority order:

1. If target has native N-wide T register → emit native intrinsic.
2. If target has a larger register → split N lanes across multiple native-width ops
   (see §3.2 fallback chain).
3. If target has only smaller registers → tile/split into multiple ops.
4. If no SIMD support → scalar-fallback loop (see §3.2).

**Table 3.1-A — (target × T × N) → backend module**

| Target | T | N | Backend Module | Notes |
|--------|---|---|---------------|-------|
| x86-64 AVX-512 | f32 | 16 | `x86_64_avx512.spl::SimdAvx512F32x16` | native ZMM |
| x86-64 AVX-512 | f32 | 8 | `x86_64_avx512.spl::SimdAvx512F32x8` | YMM via VL |
| x86-64 AVX-512 | f32 | 4 | `x86_64_avx512.spl::SimdAvx512F32x4` | XMM via VL |
| x86-64 AVX-512 | f64 | 8 | `x86_64_avx512.spl::SimdAvx512F64x8` | native ZMM |
| x86-64 AVX-512 | f64 | 4 | `x86_64_avx512.spl::SimdAvx512F64x4` | YMM via VL |
| x86-64 AVX-512 | i32 | 16 | `x86_64_avx512.spl::SimdAvx512I32x16` | native ZMM BW |
| x86-64 AVX-512 | i64 | 8 | `x86_64_avx512.spl::SimdAvx512I64x8` | native ZMM |
| x86-64 AVX2 | f32 | 8 | `x86_64_simd.spl::SimdAvx2F32x8` | native YMM |
| x86-64 AVX2 | f32 | 4 | `x86_64_simd.spl::SimdAvx2F32x4` | XMM |
| x86-64 AVX2 | f64 | 4 | `x86_64_simd.spl::SimdAvx2F64x4` | native YMM |
| x86-64 AVX2 | i32 | 8 | `x86_64_simd.spl::SimdAvx2I32x8` | native YMM |
| x86-64 SSE2 | f32 | 4 | `x86_64_simd.spl::SimdSse2F32x4` | native XMM |
| x86-64 SSE2 | f64 | 2 | `x86_64_simd.spl::SimdSse2F64x2` | native XMM |
| x86-64 SSE2 | i32 | 4 | `x86_64_simd.spl::SimdSse2I32x4` | native XMM |
| ARM NEON | f32 | 4 | `arm_neon.spl::SimdNeonF32x4` | native Q-reg |
| ARM NEON | f64 | 2 | `arm_neon.spl::SimdNeonF64x2` | native Q-reg |
| ARM NEON | i32 | 4 | `arm_neon.spl::SimdNeonI32x4` | native Q-reg |
| ARM NEON | i32 | 8 | `arm_neon.spl::SimdNeonI32x4 × 2` | split |
| ARM SVE2 | f32 | 4 | `arm_sve2.spl::SimdSve2F32` | prefer ScalableVec; FixedVec uses NEON path on SVE2 targets |
| RISC-V RVV | f32 | 4 | `riscv_rvv.spl::SimdRvvF32` | prefer ScalableVec; FixedVec uses scalar fallback pending RVV ISel |
| PTX/CUDA | f32 | 1 | `ptx_builder.spl::SimdPtxScalar` | per-thread scalar; WarpVec for cross-lane |
| Scalar fallback | any T | any N | `scalar_fallback.spl::SimdScalarLoop` | O(N) loop; no SIMD |

### §3.2 Fallback Chain

When the target lacks a native instruction for the exact (T,N) pair, the compiler
applies this ordered policy in `60.mir_opt/simd_split_unsupported.spl`:

```
Phase 1 — native: emit native op if target register width == N * sizeof(T).

Phase 2 — split into sub-width: if N * sizeof(T) > target_register_width,
           split into ceil(N / native_N) ops of FixedVec<T, native_N>.
           Example: (x86-64 SSE2, f32, 16) → 4× FixedVec<f32, 4>

Phase 3 — widen to next available register: if N * sizeof(T) < target_register_width
           AND N is valid for the next larger register on target,
           prefer native_N even if overkill (e.g. 2× f32 on AVX2 → use 4× XMM).

Phase 4 — scalar fallback: if no SIMD support on target (or unsupported T),
           emit O(N) scalar loop in MIR. No SIMD instructions produced.
           Emits W_SIMD_SCALAR_FALLBACK warning.
```

**Example:** `(x86-64-sse2, f32, 16)`:
1. Native: SSE2 XMM = 128 bits = 4× f32 ≠ 16× f32. Skip.
2. Split: 16/4 = 4 ops of `FixedVec<f32,4>` → `SimdSse2F32x4`. Use this.
MIR: `MirSimdSplitOp(lanes=16, sub_lanes=4, op=SimdSse2F32x4)` (see §8).

**Example:** `(arm-neon-only, f64, 16)`:
1. Native: NEON Q-reg = 128 bits = 2× f64 ≠ 16× f64. Skip.
2. Split: 16/2 = 8 ops of `FixedVec<f64,2>`. Use this.
Emits `W_SIMD_NO_NATIVE_LOWERING` if user used `@simd` annotation (forced vectorization).

**Example:** `(arm-neon-only, f64, 16)` with `@simd(require_native)`:
→ Emits `E_SIMD_NO_LOWERING(arm-neon, f64, 16)` with fix-it: "Use N=2 (preferred for NEON-f64)".

### §3.3 `SimdLanesPreferred<T>(target)` Const Function

Users can query the preferred lane count at compile time:

```
# In src/lib/nogc_sync_mut/simd/platform.spl
static const fn simd_lanes_preferred<T: Numeric>() -> usize
    # Returns preferred N for T on the current compile target.
    # AVX-512: f32→16, f64→8, i32→16, i64→8
    # AVX2: f32→8, f64→4, i32→8
    # SSE2: f32→4, f64→2, i32→4
    # NEON: f32→4, f64→2, i32→4
    # SVE2: f32→4 (min_lanes; scalable preferred over fixed)
    # RVV: f32→4 (min_lanes at VLEN=128)
    # Scalar: 1
```

Usage:

```
const N = simd_lanes_preferred<f32>()
val v: FixedVec<f32, N> = FixedVec<f32, N>::splat(1.0)
```

### §3.4 Monomorphization Failure

If no lowering exists (including scalar fallback) for (target, T, N):

```
E_SIMD_NO_LOWERING(target: text, T: TypeId, N: usize)
```

Fix-it: suggests `N = simd_lanes_preferred<T>()` for the target.

Example bad source:

```
val v: FixedVec<f32, 64> = FixedVec<f32, 64>::splat(1.0)  # on x86-64-sse2-only target
```

→ `E_SIMD_NO_LOWERING(x86-64-sse2, f32, 64)`: No native lowering; split would require 16
   ops of size 4. Consider using N=4 or N=8, or rewrite with ScalableVec<f32>.

Note: `(x86-64-sse2, f32, 64)` does NOT fail — it uses the split fallback chain (Phase 2).
`E_SIMD_NO_LOWERING` only fires when `@simd(require_native)` is set or when even scalar
fallback is disabled by user pragma.

---

## §4 `ScalableVec<T>` Semantics — vscale-Bound

### §4.1 `lanes()` Runtime ABI

`lanes()` is a runtime call with target-specific ABI:

| Target | ABI Call | Notes |
|--------|----------|-------|
| ARM SVE2 | `svcntw()` for f32/i32; `svcntd()` for f64/i64; `svcntb()` for i8; `svcnth()` for i16 | Returns element count per SVE register; C1-ISA §2.1 |
| RISC-V RVV | `csrr t0, vlenb` then `t0 / sizeof(T)` | vlenb = VLEN/8 bytes; C1-ISA §2.2 §3 |

In MIR, `lanes()` on `ScalableVec<T>` lowers to `MirSimdScalableVsetvl(t: T)` (see §8.5).

### §4.2 `min_lanes()` Compile-Time ABI

`min_lanes()` is a compile-time const (no runtime cost):

| Target | T | min_lanes | Derivation |
|--------|---|-----------|-----------|
| SVE2 | f32 | 4 | Minimum VL = 128 bits; 128/32 = 4 lanes; C1-ISA §2.1 |
| SVE2 | f64 | 2 | 128/64 = 2 |
| SVE2 | i32 | 4 | 128/32 = 4 |
| SVE2 | i8 | 16 | 128/8 = 16 |
| RVV | f32 | 4 | Minimum VLEN = 128 bits; at LMUL=1: 128/32 = 4 lanes; C1-ISA §2.2 §6 |
| RVV | f64 | 2 | 128/64 = 2 |
| RVV | i32 | 4 | 128/32 = 4 |
| NEON | — | n/a | ScalableVec not valid on NEON; use FixedVec<T,4> |

Note: LMUL is a backend MIR pass decision, never user-facing (locked decision #3 per task
brief). The user sees only `ScalableVec<T>` and `min_lanes()`.

### §4.3 Strip-Mining Contract

The canonical pattern for a `ScalableVec<T>` loop:

```
# Correct: runtime stride via v.lanes()
fn scale_add(a: *f32, b: *f32, n: usize, c: f32):
    var i = 0usize
    val sv = ScalableVec<f32>::splat(0.0)
    while i < n:
        val v = ScalableVec<f32>::load_unaligned(a + i)
        val u = ScalableVec<f32>::load_unaligned(b + i)
        val r = v.fma(sv.splat(c), u)
        r.store_unaligned(a + i)
        i += sv.lanes()       # ← correct: runtime stride
```

If the user writes a hardcoded constant stride:

```
    i += 4    # ← wrong: hardcoded stride
```

The backend emits `W_SIMD_HARDCODED_STRIDE` when it detects the loop body contains a
`ScalableVec<T>` load/store but the induction increment is a compile-time constant.
Detection pass: `60.mir_opt/predicate_promote.spl` (augmented for stride detection).

### §4.4 `from_fixed` and `try_to_fixed`

**`from_fixed<const N>(v: FixedVec<T,N>) -> ScalableVec<T>`**:
- Allowed only if `N <= min_lanes()` for the target at compile time.
- If `N > min_lanes()`: emits `E_SIMD_FIXED_OVERFLOWS_SCALABLE`.
- Rationale: a fixed-width vector wider than the guaranteed minimum scalable lane count
  cannot be safely broadcast into a scalable register without knowing the runtime VL.

Example:
```
# On SVE2 (min_lanes for f32 = 4):
val fv4: FixedVec<f32, 4> = FixedVec<f32, 4>::splat(1.0)
val sv = ScalableVec<f32>::from_fixed(fv4)   # OK: N=4 == min_lanes()

val fv8: FixedVec<f32, 8> = FixedVec<f32, 8>::splat(1.0)
val sv2 = ScalableVec<f32>::from_fixed(fv8)  # ERROR: E_SIMD_FIXED_OVERFLOWS_SCALABLE(N=8 > min_lanes=4)
```

**`try_to_fixed<const N>() -> Option<FixedVec<T,N>>`**:
- Runtime check: if `self.lanes() == N`, returns `Some(fixed_vec)`.
- Otherwise returns `None`.
- No error emitted; caller must handle the `None` case.

### §4.5 PTX/CUDA: No `ScalableVec`

All `ScalableVec<T>` methods emit `E_SIMD_PTX_NO_SCALABLE` when the compile target is
PTX or CUDA. PTX has no concept of scalable vector length. C1-DEEP §3.1 (PTX execution
model) confirms: warp = 32 threads, each executing scalar; no `vsetvli` equivalent.

---

## §5 Mask Semantics — Full Table

### §5.1 Construction Methods (see §1.4 for signatures)

**`Mask::from_bits(bits: u64)`** — construct from bitmask.
- Bit `i` of `bits` → lane `i` active.
- For `FixedVec<T,N>`: bits N–63 are ignored.
- For `ScalableVec<T>`: only the low `lanes()` bits are used; excess bits raise `W_SIMD_MASK_BITS_OOB`.

**`Mask::all_ones()` / `Mask::all_zeros()`** — trivial; used for unconditional / masked-out ops.

**`Mask::from_cmp(cmp_result)`** — identity; the comparison methods already return `Self.Mask`.
This constructor is for cases where a mask is produced by one expression and consumed by another.

### §5.2 Mask Operations

All logical ops (`and`, `or`, `xor`, `not`, `andnot`) are element-wise on the mask bits.
On AVX-512: lower to `kandw/korw/kxorw/knotw/kandnw` instructions (k1–k7 only, k0 is
all-ones sentinel per B2 §4.4).
On SVE2: lower to `pand/por/peor/not/bic` predicate ops (C1-ISA §2.1).
On RVV: lower to `vmand.mm/vmor.mm/vmxor.mm/vmnot.m` (C1-ISA §2.2 §5); result always
lives in a v-register; must `vmv1r.v v0, vX` before using as mask (C1-DEEP §6-J).
On SSE/NEON: materialize as vector and use bitwise ops (see §5.4 materialization table).

### §5.3 Predication Model: `_z` vs `_x` vs `_m`

Only `_z` (zero-fill on inactive lanes) is user-visible (locked decision #4).

- **`_z` (zero-fill)**: inactive lanes get 0. Default for all user-facing masked ops.
- **`_x` (undefined/poison)**: inactive lanes hold undefined values. Backend choice.
  Emitted when liveness analysis proves inactive lane values are never read.
  The `60.mir_opt/predicate_promote.spl` pass promotes `_z` → `_x` when safe.
- **`_m` (merge/preserve)**: inactive lanes preserve the destination register value.
  Backend choice for operations where the destination value is live.

When `predicate_promote.spl` identifies a `_x` opportunity, it emits
`W_SIMD_PRED_PROMOTE_HINT` (informational; helps users understand when to use `@simd`
annotation or restructure loops for better codegen).

### §5.4 Mask Materialization Decision Table

| Target | Mask type | Materialization | Notes |
|--------|----------|-----------------|-------|
| x86-64 AVX-512 | `Mask<FixedVec<T,N>>` | k-register (k1–k7) | k0 = all-ones sentinel; unallocatable; B2 §4.4, C1-ISA §1.4 |
| x86-64 AVX2 | `Mask<FixedVec<T,N>>` | YMM vector (top-bit-per-lane) | `VCMPPS` → YMM; `VBLENDVPS` for select |
| x86-64 SSE2/SSE4 | `Mask<FixedVec<T,N>>` | XMM vector (sign-bit-per-lane) | `CMPEQPS` → XMM; `BLENDVPS` (SSE4.1) or `ANDPS+ANDNPS+ORPS` (SSE2) |
| ARM NEON | `Mask<FixedVec<T,N>>` | Q-register (all-ones per lane) | `VCMPEQ` → vector; `VBSL` for blend; C1-ISA §1.1 |
| ARM SVE2 | `Mask<ScalableVec<T>>` | P-register (bit per element) | P0–P15; p0 conventional for loop; C1-ISA §2.1 |
| RISC-V RVV | `Mask<ScalableVec<T>>` | v0 register (bit per element) | v0 is the ONLY mask source; computed masks in other v-regs need `vmv1r.v v0, vX`; C1-DEEP §6-J |
| PTX/CUDA | `Mask<WarpVec<T>>` | Predicate register (%p0–%p6) | `setp` + `@%p` conditional; no AVX-style k-reg |
| SPIR-V | `Mask<V>` | `OpTypeBool` per component | `OpCompositeConstruct` of bool vector; no dedicated k-reg |

---

## §6 `WarpVec<T>` Extension Trait — Full Method Specification

### §6.1 Shuffle Operations

All shuffle ops take a `mask: u32` parameter — the active warp mask. Per C1-DEEP §6-G:
the `mask` must include the calling thread's own lane bit. Backend enforces:

```
# invariant check (emitted by gpu_checker.spl):
assert (mask >> lane_id) & 1 == 1  # self-lane must be included
# else: E_WARP_SELF_EXCLUDED
```

PTX lowering: `shfl.sync.{up,down,bfly,idx}.b32 %dest, %src, %imm, %mask` (C1-ISA §3.1).
SPIR-V lowering: `OpGroupNonUniformShuffle{Up,Down,XorIndirect}` (KHR_shader_subgroup_basic).

### §6.2 Warp Reductions

`warp_reduce_sum` uses a shuffle-based binary tree reduction (log2(warp_size) steps).
PTX: `shfl.sync.bfly.b32` XOR-tree (standard pattern; C1-ISA §3.1).
SPIR-V: `OpGroupNonUniformFAdd(Subgroup, Reduce)` (C1-DEEP §5.1).

### §6.3 SubgroupSize Portability

Three runtime queries for portability across GPU targets:

| Query | PTX | SPIR-V Vulkan | AMD RDNA | Notes |
|-------|-----|--------------|----------|-------|
| `target_warp_size_const()` | 32 (compile const) | Specialization constant | wave_size (32 or 64) | Compile-time when deterministic |
| `target_warp_size_runtime()` | `warpSize` (always 32) | `gl_SubgroupSize` built-in | `gl_SubgroupSize` (32 or 64) | Runtime value |
| `subgroup_size_query()` | alias for above | alias for above | alias for above | Preferred name for SPIR-V |

AMD RDNA note: RDNA supports both wave32 and wave64 modes. `target_warp_size_runtime()`
returns the actual wave size at runtime. No architectural constant.

### §6.4 Apple M-Series Restriction

Per C1-DEEP §6-H: Apple M1/M2/M3/M4 support NEON but NOT SVE2 and have no documented
warp/subgroup model (AMX coprocessor is undocumented and not exposed as ISA). Any call to
any `WarpVec<T>` method when `target == apple-m-series` emits:

```
E_WARP_NO_APPLE_M
```

Fix-it: "Apple M-series does not support warp-scoped ops. Use FixedVec<T,4> with NEON
backend for fixed-width vectorization, or use a cross-platform compute framework."

Detection: `35.semantics/gpu_checker.spl` checks `SimdFeatureFlags.target_vendor == AppleM`.

---

## §7 Interpreter-Mode Parity

### §7.1 Policy

Per project memory `feedback_compile_mode_false_greens.md` and
`feedback_interpreter_test_limits.md`: interpreter-mode parity is REQUIRED for
correctness tests. All SIMD methods must have a scalar fallback that runs in the
interpreter. Performance tests must use compiled mode.

### §7.2 Scalar Fallback Rules

Every `Vector` trait method has an interpreter implementation as a pure-Simple scalar
loop over lanes:

| Method | Interpreter implementation | Performance |
|--------|--------------------------|------------|
| `add(a, b)` | `for i in 0..N: result[i] = a[i] + b[i]` | O(N) |
| `sub(a, b)` | element-wise subtraction | O(N) |
| `mul(a, b)` | element-wise multiplication | O(N) |
| `fma(a, b, c)` | `for i: result[i] = a[i]*b[i] + c[i]` | O(N) |
| `fnmadd(a, b, c)` | `for i: result[i] = -(a[i]*b[i]) + c[i]` | O(N) |
| `abs(a)` | element-wise `if a[i] < 0: -a[i] else a[i]` | O(N) |
| `neg(a)` | element-wise `-a[i]` | O(N) |
| `min(a, b)` | `for i: if a[i] < b[i]: a[i] else b[i]` | O(N) |
| `max(a, b)` | element-wise max | O(N) |
| `and/or/xor/andnot(a, b)` | element-wise bitwise op | O(N) |
| `shl/shr_logical/shr_arith` | element-wise shift | O(N) |
| `cmp_eq/lt/le/gt/ge/ne` | element-wise comparison → Mask | O(N) |
| `mask_select(m, t, f)` | `for i: if m[i]: t[i] else f[i]` | O(N) |
| `reduce_sum/min/max/and/or` | accumulate loop | O(N) |
| `shuffle(v, idx)` | `for i: result[i] = v[idx[i]]` | O(N) |
| `permute(v, ctrl)` | same as shuffle with const ctrl | O(N) |
| `broadcast_lane(v, lane)` | `for i: result[i] = v[lane]` | O(N) |
| `interleave_lo/hi` | element-wise interleave | O(N) |
| `load_aligned/unaligned` | element-wise load from ptr | O(N) |
| `store_aligned/unaligned` | element-wise store to ptr | O(N) |
| `gather(base, idx)` | `for i: result[i] = base[idx[i]]` | O(N) |
| `scatter(v, base, idx)` | `for i: base[idx[i]] = v[i]` | O(N) |
| `from_array/to_array` | element copy | O(N) |
| `splat(v)` | fill all lanes with v | O(N) |
| `cast<U>()` | element-wise numeric cast | O(N) |
| `Mask::from_bits/to_bits` | bit extract/pack loop | O(N) |
| `Mask::count_ones/any/all/none` | simple bit loop | O(N) |
| `ScalableVec::lanes()` | return fixed constant = min_lanes() | O(1) |

### §7.3 Compile-Only Methods (No Interpreter Implementation)

These methods emit `E_SIMD_COMPILE_ONLY` if reached in interpreter mode:

| Method | Reason |
|--------|--------|
| `Mask::ptx_preg_handle()` | PTX predicate register is a compile-time concept only |
| `WarpVec::shfl_*` | No warp concept in interpreter; scalar fallback would be wrong |
| `WarpVec::warp_reduce_*` | Requires warp execution context |
| `WarpVec::warp_ballot` | Vote requires warp execution model |
| `WarpVec::warp_active_mask` | No active mask concept in scalar interpreter |
| `WarpVec::warp_sync` | Barrier has no interpreter meaning |
| `FixedVec::preferred_lanes_for_target()` | OK in interp (returns const); not compile-only |

Note: `WarpVec` methods in the interpreter may optionally fall back to a single-thread
simulation (one "warp" of 1 thread) returning the self value for shuffles and
accumulate-0 for reductions. This simulation is valid for unit tests that check
call-correctness but not for any test that verifies shuffle semantics.

### §7.4 Interpreter Representation

In the interpreter, `FixedVec<T,N>` is stored as a `[T; N]` heap-allocated array of
boxed values. `ScalableVec<T>` is stored as a `[T; min_lanes()]` array (interpreter
uses the minimum lane count as the lane count). This is correct for correctness tests;
performance tests must use compiled mode.

---

## §8 Compile-Mode Lowering Pipeline — New MIR Opcodes

### §8.1 New MIR Opcode Types

These opcodes are added to `src/compiler/50.mir/mir_instructions.spl`:

```
# Splat
MirSimdSplat(dest: MirReg, val: MirReg, vec_type: MirType)

# Load / Store
MirSimdLoad(dest: MirReg, ptr: MirReg, aligned: bool, vec_type: MirType)
MirSimdStore(val: MirReg, ptr: MirReg, aligned: bool)

# Gather / Scatter
MirSimdGather(dest: MirReg, base: MirReg, indices: MirReg, vec_type: MirType)
MirSimdScatter(val: MirReg, base: MirReg, indices: MirReg)

# Binary ops
MirSimdBinop(dest: MirReg, lhs: MirReg, rhs: MirReg, op: SimdBinop)

enum SimdBinop:
    Add     # float + int
    Sub
    Mul
    Fma     # dest = lhs * rhs + third (uses MirSimdTernop below)
    Fnmadd
    Min
    Max
    And     # integer only
    Or      # integer only
    Xor     # integer only
    Andnot
    Shl
    ShrLogical
    ShrArith

# Ternary (FMA)
MirSimdTernop(dest: MirReg, a: MirReg, b: MirReg, c: MirReg, op: SimdTernop)

enum SimdTernop:
    Fma     # a*b + c
    Fnmadd  # -(a*b) + c

# Unary ops
MirSimdUnop(dest: MirReg, src: MirReg, op: SimdUnop)

enum SimdUnop:
    Neg
    Abs     # float only
    Not     # bitwise not; integer only
    Recip   # 1/x; float only; approximate
    Sqrt    # sqrt(x); float only

# Reductions → scalar
MirSimdReduce(dest: MirReg, src: MirReg, op: SimdReduce)

enum SimdReduce:
    Sum
    Min
    Max
    And
    Or

# Shuffle / permute
MirSimdShuffle(dest: MirReg, src: MirReg, indices: MirReg)
MirSimdPermute(dest: MirReg, src: MirReg, ctrl: MirConst)  # compile-time indices
MirSimdBroadcastLane(dest: MirReg, src: MirReg, lane: u32)
MirSimdInterleave(dest: MirReg, lhs: MirReg, rhs: MirReg, hi: bool)

# Comparison → Mask
MirSimdCmp(dest: MirReg, lhs: MirReg, rhs: MirReg, op: SimdCmpOp)

enum SimdCmpOp: Eq Ne Lt Le Gt Ge

# Mask → select
MirSimdSelect(dest: MirReg, mask: MirReg, t: MirReg, f: MirReg)

# Mask operations
MirSimdMaskOp(dest: MirReg, lhs: MirReg, rhs: MirReg, op: MaskBinop)

enum MaskBinop: And Or Xor Andnot Not  # Not uses lhs only; rhs is unused

# ScalableVec lane-length setup
MirSimdScalableVsetvl(dest_vl: MirReg, requested: MirReg, elem_type: MirType)
    # SVE2: no-op (predicate-driven, VL is implicit); returns svcnt*() result in dest_vl
    # RVV:  emits vsetvli dest_vl, requested, e{SEW}, m1, ta, ma

# Warp-specific opcodes (separate from MirSimd* to enforce trait separation)
MirWarpShfl(dest: MirReg, src: MirReg, delta: MirReg, mask: MirReg, op: WarpShflKind)

enum WarpShflKind: Up Down Xor Idx

MirWarpReduce(dest: MirReg, src: MirReg, mask: MirReg, op: WarpReduceOp)

enum WarpReduceOp: Sum Min Max Any All

MirWarpBallot(dest: MirReg, pred: MirReg, mask: MirReg)
MirWarpActivesMask(dest: MirReg)
MirWarpSync(mask: MirReg)
```

### §8.2 Type Annotation

All `MirSimd*` nodes carry `MirType` (for `FixedVec<T,N>` specialization) or
`MirTypeKind.ScalableVec(element, min_lanes)` (for `ScalableVec<T>`).

### §8.3 New MIR Optimization Passes

**`60.mir_opt/lmul_widen.spl`**: promotes RVV operations from LMUL=1 to LMUL=2/4/8
when profitable (wider ops reduce loop iterations). Decision: if the inner loop body
has no register-pressure conflict and the VLEN is known to be ≥ 256 bits, promote.

**`60.mir_opt/predicate_promote.spl`**: promotes `_z` (zero-fill) predication to `_x`
(undefined) when liveness analysis proves inactive lanes are dead. Also detects
`ScalableVec<T>` loops with hardcoded strides (§4.3) and emits `W_SIMD_HARDCODED_STRIDE`.

**`60.mir_opt/simd_split_unsupported.spl`**: implements the fallback chain from §3.2.
Splits `MirSimdBinop` on unsupported (T,N) pairs into multiple smaller ops.

### §8.4 Wiring in `50.mir/mir_lowering_expr.spl`

Currently (per C1-DEEP §2 internal state), `FixedVec::add` does NOT produce any
`MirSimd*` opcode — it resolves as a plain `Call` MIR node. The wiring must be added:

```
# In mir_lowering_expr.spl, MethodCall on FixedVec type:
case MethodCall(recv, "add", [rhs]) if is_simd_type(recv):
    emit MirSimdBinop(dest, lower(recv), lower(rhs), SimdBinop.Add)
```

This is the core change that makes the SIMD type system actually produce SIMD MIR.

### §8.5 `MirSimdScalableVsetvl` Lowering Specifics

- **SVE2 target**: `MirSimdScalableVsetvl` lowers to a call to `svcntw()` (or element-specific
  variant). No `vsetvli` instruction is emitted — SVE2 is predicate-driven and the vector
  length is implicit in the Z-register type. The dest_vl MirReg is set to the return of
  `svcnt*`. C1-ISA §2.1.
- **RVV target**: `MirSimdScalableVsetvl` lowers to `vsetvli dest_vl, requested, e{SEW}, m1, ta, ma`.
  LMUL may be promoted by `lmul_widen.spl` to m2/m4/m8 in a subsequent pass. C1-ISA §2.2 §6.

---

## §9 Diagnostic Catalog

**Table 9-A — Error Codes**

| Code | Phase | Trigger | Example Bad Source | Fix-it |
|------|-------|---------|-------------------|--------|
| `E_SIMD_BAD_LANES` | type-check | N not in {2,4,8,16,32,64} | `FixedVec<f32, 3>` | Use N ∈ {2,4,8,16,32,64} |
| `E_SIMD_TYPE_MISMATCH` | type-check | T not satisfying constraint (e.g. bool used for Numeric) | `FixedVec<bool, 4>` | Use a numeric type |
| `E_SIMD_FLOAT_ONLY` | type-check | Float-only method called on integer T | `FixedVec<i32,4>::fma(a,b,c)` | Use float type or different op |
| `E_SIMD_INT_ONLY` | type-check | Integer-only method called on float T | `FixedVec<f32,4>::and(a,b)` | Use integer type or bitcast |
| `E_SIMD_LANE_MISMATCH` | type-check | Mask and vector have different lane counts | `mask4.mask_select(v8, w8)` | Match lane counts |
| `E_SIMD_MASK_TYPE_MISMATCH` | type-check | Mask operations on incompatible Mask types | `Mask<FixedVec<f32,4>> and Mask<FixedVec<i32,4>>` | Use matching vector types |
| `E_SIMD_ARRAY_LEN_MISMATCH` | type-check | `from_array` array length != N | `FixedVec<f32,4>::from_array([1.0, 2.0])` | Pass array of length N |
| `E_SIMD_SLICE_TOO_SHORT` | type-check | `from_slice` slice shorter than N | slice of length 2 into FixedVec<f32,4> | Use slice of length >= N |
| `E_SIMD_SHIFT_OOB` | type-check | Shift count >= element bit width | `FixedVec<i32,4>::shl(v, 32)` | Use count < 32 for i32 |
| `E_SIMD_LANE_OOB` | type-check (constant) / runtime (interp) | Lane index >= lane count | `v.lane(8)` on `FixedVec<f32,4>` | Use index < 4 |
| `E_SIMD_TYPE_AMBIGUOUS` | type-check | `splat(0)` with no context | `val v = FixedVec<?, ?>: splat(0)` | Add type annotation |
| `E_SIMD_NO_LOWERING` | mono | No native or fallback lowering for (target, T, N) | `@simd(require_native) FixedVec<f64,16>` on SSE2 | Use `N = simd_lanes_preferred<T>()` |
| `E_SIMD_PTX_NO_SCALABLE` | mono | `ScalableVec<T>` used on PTX target | `ScalableVec<f32>` in CUDA kernel | Use `FixedVec<f32,N>` for PTX |
| `E_SIMD_FIXED_OVERFLOWS_SCALABLE` | type-check | `from_fixed(v)` with N > min_lanes() | `ScalableVec<f32>::from_fixed(fv8)` on SVE2 with min_lanes=4 | Use N <= 4 or load directly |
| `E_SIMD_MASK_BITS_OOB` | type-check | `from_bits(bits)` with bits beyond lane count | `Mask<FixedVec<f32,2>>::from_bits(0xFF)` | Mask bits to valid lane range |
| `E_SIMD_NO_WIDEN_TYPE` | type-check | `widen()` with no 2x-width type available | `FixedVec<i64,4>::widen()` (no i128) | Cannot widen i64 |
| `E_SIMD_NO_NARROW_TYPE` | type-check | `narrow()` with no half-width type available | `FixedVec<i8,4>::narrow()` (no i4) | Cannot narrow i8 |
| `E_SIMD_COMPILE_ONLY` | interp | Method called in interpreter that has no scalar fallback | `mask.ptx_preg_handle()` in test | Use compiled mode for this op |
| `E_SIMD_CONST_REQUIRED` | type-check | `permute(ctrl)` ctrl is not a compile-time const | `v.permute(runtime_idx)` | Use `shuffle()` for runtime indices |
| `E_WARP_NOT_IN_KERNEL` | semantics | `WarpVec` method called outside GPU kernel | `shfl_up(v, 1, 0xFFFFFFFF)` in CPU code | Move to kernel function |
| `E_WARP_NO_APPLE_M` | semantics | `WarpVec` method on Apple M-series target | any `WarpVec` call on apple-m | Use NEON FixedVec instead |
| `E_WARP_DELTA_OOB` | type-check | `shfl_up/down` delta >= warp_size | `shfl_down(v, 32, mask)` | Use delta < 32 |
| `E_WARP_SELF_EXCLUDED` | semantics | shfl mask does not include calling thread | `shfl_down(v, 1, 0)` | Set calling thread's bit in mask |
| `E_WARP_LANE_OOB` | type-check | `shfl_idx` src_lane >= warp_size | `shfl_idx(v, 32, mask)` | Use src_lane < warp_size |
| `E_WARP_SIZE_RUNTIME_ONLY` | type-check | `target_warp_size_const()` called on variable-size target | `target_warp_size_const()` on RDNA without known wave_size | Use `target_warp_size_runtime()` |

**Table 9-B — Warning Codes**

| Code | Phase | Trigger | Fix-it |
|------|-------|---------|--------|
| `W_SIMD_SCALAR_FALLBACK` | mir_opt | Split/fallback to scalar loop used | Use N matching target preferred lanes |
| `W_SIMD_NO_NATIVE_LOWERING` | mir_opt | Split into multiple sub-width ops | Use preferred-N or ScalableVec |
| `W_SIMD_HARDCODED_STRIDE` | mir_opt | `ScalableVec` loop with constant induction step | Use `v.lanes()` as stride |
| `W_SIMD_PRED_PROMOTE_HINT` | mir_opt | `_x` promotion opportunity detected by liveness | Informational; no action required |
| `W_SIMD_FIXED_EXCEEDS_MIN_LANES` | type-check | `to_scalable()` with N > min_lanes for target | Consider `from_fixed()` only when N <= min_lanes |
| `W_SIMD_MASK_BITS_OOB` | type-check | `from_bits` for ScalableVec with bits beyond runtime lanes | Truncate bits to runtime lane count |
| `W_WARP_SYNC_EMPTY_MASK` | semantics | `warp_sync(0)` called with empty mask | Use active warp mask |
| `W_SIMD_FP16_AUTOPROMOTE` | type-check | `FixedVec<f16,N>` on target without native FP16 | Promote to f32 explicitly; performance may differ |

---

## §10 Frontend Syntax Surface

### §10.1 Vector Literal Syntax

**FixedVec literal**: `[expr; lanes N]` where N must be a compile-time constant.

```
val v: FixedVec<f32, 4> = [1.0f32; lanes 4]    # all-ones splat
val w: FixedVec<f32, 4> = [1.0f32, 2.0f32, 3.0f32, 4.0f32; lanes 4]  # per-lane init
```

The `lanes` keyword is a disambiguator to avoid conflict with existing `[expr; N]`
array syntax. Parser rule: `[` ... `; lanes` `<int>` `]` → `FixedVec` literal node.
This does NOT conflict with `[expr; N]` (array repeat) because `lanes` is a reserved
contextual keyword in this position (not a general identifier ban).

Per project memory `feedback_struct_literal_brace_syntax.md`: the parser must handle
`FixedVec<f32, 4> { ... }` struct-literal syntax. To avoid ambiguity, SIMD vector
literals use `[...]` bracket syntax rather than brace syntax. The brace form
`FixedVec<f32,4> { data: [...] }` is also accepted for the internal struct field but
is not the recommended user-facing form.

**ScalableVec construction**: No literal syntax. Use constructor methods:

```
val sv = ScalableVec<f32>::splat(1.0f32)    # runtime N
val sv2 = ScalableVec<f32>::splat_n(1.0f32, n=v.lanes())
```

### §10.2 Lane Indexing

`v.lane(i)` is the canonical form for single-lane read. `v[i]` is accepted as sugar
for `v.lane(i)` when `v`'s static type is `FixedVec<T,N>` or `ScalableVec<T>`.

There is no `v[i]` ambiguity with array indexing because the type system resolves which
`[]` overload to use. If `v` is a `FixedVec<T,N>`, `v[i]` lowers to `v.lane(i)`.
Write is: `v[i] = x` → `v.set_lane(i, x)`.

### §10.3 `into_simd` Spread Syntax

```
val v = [1.0f32, 2.0f32, 3.0f32, 4.0f32].into_simd::<FixedVec<f32, 4>>()
```

This is implemented as a method on `[T]` array that calls `FixedVec<T,N>::from_array()`.
No new grammar production needed — this is a trait method call using the existing
`::<TypeParam>` turbofish-style syntax (already in the Simple parser).

### §10.4 Pattern Matching on `Mask`

Pattern matching on a `Mask<V>` is **not supported** in this design. Masks are opaque
at the language level. Use `.any()`, `.all()`, `.none()`, `.count_ones()`, or
`.lane_active(i)` for queries.

```
# Not allowed:
match mask:
    case Mask::all_ones(): ...  # rejected; use mask.all() == true

# Allowed:
if mask.all():
    ...
if mask.any():
    ...
```

This avoids the ambiguity of what "pattern matching on a mask" should bind to (the bits?
the lanes? the backing register?).

### §10.5 Interaction with Round-1 Grammar Reservation

Round-1 `simd_unified_architecture.md` reserved the following syntax forms. This section
confirms compatibility:

- `FixedVec<T, N>` — no conflict with existing generics syntax.
- `ScalableVec<T>` — no conflict.
- `[expr; lanes N]` — new production; `lanes` is context-keyword (only reserved after `;`
  inside `[...]`; does not shadow other uses of `lanes` as an identifier elsewhere).
- `v.lane(i)` — method call, no parser change needed.
- `v[i]` on SIMD type — resolved via type-directed desugaring, no grammar change.

---

## §11 Standard Library Landing Zone

### §11.1 Path

Per `.claude/rules/structure.md`: `src/lib/nogc_sync_mut/` is "Sync mutable
(ffi, fs, net, http, database, mcp, spec)". SIMD is a sync, no-GC, mutable operation
and fits this category. The SIMD landing zone is:

```
src/lib/nogc_sync_mut/simd/
```

### §11.2 File Layout

```
src/lib/nogc_sync_mut/simd/
├── mod.spl          # re-exports: FixedVec, ScalableVec, Vector, Mask, WarpVec, simd_lanes_preferred
├── vector.spl       # Vector trait definition (§1.1)
├── fixed.spl        # FixedVec<T,N> class + impl (§1.2)
├── scalable.spl     # ScalableVec<T> class + impl (§1.3, §4)
├── mask.spl         # Mask<V> trait + impl (§1.4, §5)
├── warp.spl         # WarpVec<T> trait + impl (§1.5, §6)
├── platform.spl     # SimdFeatureFlags, simd_lanes_preferred, target detection
│                    # supersedes src/compiler/30.types/simd_platform.spl (migration path: keep old file, re-export from new location)
├── aliases.spl      # back-compat type aliases (see §11.3)
└── intrinsics.spl   # INTERNAL — not re-exported by mod.spl; one fn per MIR opcode
```

**`mod.spl`** re-exports for public API:

```
use std.simd.vector :: Vector
use std.simd.fixed :: FixedVec
use std.simd.scalable :: ScalableVec
use std.simd.mask :: Mask
use std.simd.warp :: WarpVec
use std.simd.platform :: simd_lanes_preferred, SimdFeatureFlags
use std.simd.aliases :: Vec2f, Vec4f, Vec8f, Vec4d, Vec2d, Vec4i, Vec8i
```

### §11.3 `aliases.spl` — Back-Compat Aliases

```
type Vec2f  = FixedVec<f32, 2>
type Vec4f  = FixedVec<f32, 4>
type Vec8f  = FixedVec<f32, 8>
type Vec16f = FixedVec<f32, 16>
type Vec2d  = FixedVec<f64, 2>
type Vec4d  = FixedVec<f64, 4>
type Vec8d  = FixedVec<f64, 8>
type Vec4i  = FixedVec<i32, 4>
type Vec8i  = FixedVec<i32, 8>
type Vec16i = FixedVec<i32, 16>
type Vec4u  = FixedVec<u32, 4>
type Vec8u  = FixedVec<u32, 8>
```

Existing code using `Vec4f`, `Vec8f` etc. (from `30.types/simd.spl`) will resolve to
the new parameterized types after the migration. The concrete struct fields (`x`, `y`,
`z`, `w`) in the old types do NOT carry over — use `.lane(0)`, `.lane(1)` etc. or
destructure via `to_array()`.

### §11.4 `intrinsics.spl` — Internal Mapping

One entry per MIR opcode (§8.1). Not public. Example:

```
# @internal — do not use directly; use Vector trait methods
extern fn __simd_splat_f32x4(val: f32) -> FixedVec<f32, 4>          # → MirSimdSplat
extern fn __simd_add_f32x4(a: FixedVec<f32,4>, b: FixedVec<f32,4>) -> FixedVec<f32,4>  # → MirSimdBinop(Add)
# ... one entry per (op, T, N) combo
```

These are `@internal` fns recognized by `simd_lowering.spl` by name-prefix `__simd_`.
This is the bridge between the trait method dispatch and the existing name-match
lowering in `60.mir_opt/simd_lowering.spl:93–149`.

---

## §12 Open Architectural Questions

**OQ-A: f16/bf16 type existence in Simple's type system (R2-new)**
FP16 and BF16 instructions are confirmed on AVX-512-FP16 (Intel Sapphire Rapids),
ARM NEON (bf16 extension), and NVIDIA PTX (`.f16`). Whether Simple has `f16` and `bf16`
as first-class scalar types is not confirmed. If they do not exist, `FixedVec<f16,N>`
cannot be typed. Resolution path: file a feature request for `f16`/`bf16` primitive
types; use `FixedVec<f32,N>` with `widen()`/`narrow()` as interim; emit
`W_SIMD_FP16_AUTOPROMOTE` on attempted `FixedVec<f16,N>` use.

**OQ-B: `Mask<FixedVec<f32,4>>` vs `Mask<FixedVec<i32,4>>` — shared backing repr on AVX-512 (R2-new)**
Both types have 4 lanes and lower to the same k-register width (k-reg is 4 bits for
32-bit ops, 4 bits regardless of element type on most ops). C3 may wish to share a
physical k-register between `Mask<FixedVec<f32,4>>` and `Mask<FixedVec<i32,4>>`. The
type system keeps them distinct (§2.3), but the register allocator may coalesce them.
Resolution: C3 decides; document as a C3 decision and add a note in `mask.spl` that
the physical backing is target-dependent.

**OQ-C: `from_fixed` across element widths (R2-new)**
Is `ScalableVec<f32>::from_fixed(FixedVec<i32,4>)` allowed (cross-element-width) or
only same-T? Current design (§4.4) requires same T. But there are valid use cases
(reinterpret a bitfield as float). Resolution: keep same-T restriction; add a
separate `reinterpret_cast` method with explicit documentation of undefined behavior
risk if element widths differ.

**OQ-D: Monomorphization cap enforcement mechanism (continued from B1 §9 OQ-3)**
The cap N ∈ {2,4,8,16,32,64} and T ∈ {u8,u16,u32,u64,i8,i16,i32,i64,f32,f64} gives
60 × 6 = 60 combinations (T × N). At 70 backend modules (§3.1 table × platforms),
this is ~4200 specializations. The compiler must limit specialization generation or
use demand-driven specialization. Resolution: use demand-driven specialization in
`40.mono/instantiation.spl` — only specialize when a call site is found. Do not
eagerly generate all 4200 permutations.

**OQ-E: Strip-mining detection reliability (R2-new)**
`W_SIMD_HARDCODED_STRIDE` detection in §4.3 requires the MIR opt pass to identify
`ScalableVec<T>` loop induction increments. This requires the `ScalableVec` type to be
preserved through the MIR optimization pipeline (not erased to a scalar loop before
the pass runs). Resolution: ensure `MirSimdScalableVsetvl` is emitted BEFORE the
`predicate_promote.spl` pass runs and is not optimized away prematurely.

**OQ-F: `warp_active_mask` on SPIR-V (R2-new)**
PTX `activemask.b32` has no direct SPIR-V equivalent. `gl_SubgroupEqMask` + bitwise ops
can approximate it, but `gl_SubgroupActiveMask` (Vulkan 1.3 / VK_EXT_shader_subgroup_uniform_control_flow)
is the closest match. The exact lowering rule is not yet specified. Resolution: map
`warp_active_mask()` to `OpLoad %SubgroupEqMask` OR require
`VK_EXT_shader_subgroup_uniform_control_flow`; document the extension requirement in
`warp.spl`.

**OQ-G: ScalableVec iterator semantics (R2-new)**
The `iter()` method on `ScalableVec<T>` yields elements but the lane count is runtime.
`LaneIter<T>` must be a dynamically-sized iterator. The interaction with Simple's
for-loop desugaring (which may need a `len()` or `next()` protocol) is not yet
specified. Resolution: `ScalableVec::iter()` returns a `ScalableLaneIter<T>` that
holds a runtime index; the for-loop desugaring uses `while i < iter.len()` form rather
than an exact iterator.

---

*Document generated by Wave C2 (Round-2 deep-detail unified architecture). C3's
`simd_backend_strict_emit_detail.md` covers encoder bytes, ABI registers, and
golden fixtures. C4's rollout plan v2 covers milestone phasing and test budgets.*
++++++ Contents of side #2
<!-- claude-arch -->
# Architecture: Unified SIMD — Detail (Round 2)

**TL;DR:** Round 2 specifies every trait method signature, exact diagnostic codes,
monomorphization decision tables, `ScalableVec<T>` vscale ABI, Mask semantics, WarpVec
extension catalog, interpreter-mode parity rules, the new MIR opcodes required, frontend
syntax additions, and the `src/lib/nogc_sync_mut/simd/` file layout. It is the
IDE-tooltip / ABI-spec companion to Round-1 `simd_unified_architecture.md` (B1). Do not
implement from Round 1 alone; all compiler contracts are specified here.

---

## §0 Reading Order

| Section | Audience |
|---------|----------|
| §1 Trait method catalog | Implementors of `vector.spl`, `fixed.spl`, `scalable.spl`, `mask.spl`, `warp.spl` |
| §2 Type-system rules | Implementors of `35.semantics/simd_check.spl`, `40.mono/` |
| §3 Monomorphization rules | Implementors of `40.mono/`, `50.mir/mir_lowering_expr.spl` |
| §4 ScalableVec semantics | Implementors of `scalable.spl`, `50.mir/`, `60.mir_opt/lmul_widen.spl` |
| §5 Mask semantics | Implementors of `mask.spl`, `60.mir_opt/predicate_promote.spl` |
| §6 WarpVec extension | Implementors of `warp.spl`, `35.semantics/gpu_checker.spl` |
| §7 Interpreter parity | Implementors of `interp/` evaluation layer |
| §8 MIR opcodes | Implementors of `50.mir/`, `60.mir_opt/` |
| §9 Diagnostic catalog | All — error/warning handling |
| §10 Frontend syntax | Implementors of `00.parse/`, `10.lex/` |
| §11 Stdlib landing zone | Implementors of `src/lib/nogc_sync_mut/simd/` |
| §12 Open questions | Architects — unresolved; requires design decisions |

Cross-references to Round-1 use prefix **B1** (architecture) or **B2** (strict-emit).
Cross-references to C1 research docs use **C1-ISA** (survey) or **C1-DEEP** (ISA deep).

---

## §1 Complete Trait Method Catalog

### §1.0 T and N Constraints (shared conventions)

| Symbol | Meaning |
|--------|---------|
| `T: Numeric` | Any confirmed numeric scalar: `u8 u16 u32 u64 i8 i16 i32 i64 f32 f64`. `f16`/`bf16` are gated on OQ-A resolution; treat as absent until confirmed. |
| `T: Float` | Float subset of Numeric: `f32 f64` |
| `T: Integer` | Integer subset: `u8 u16 u32 u64 i8 i16 i32 i64` |
| `T: SignedInt` | Signed integer: `i8 i16 i32 i64` |
| `N: Pow2` | N ∈ {2, 4, 8, 16, 32, 64} — compile-time const, power-of-two |
| `N: TargetValid` | N is Pow2 AND (T,N) pair has at least one backend lowering (see §3 decision table) |

N=0, N=1, and non-power-of-two values emit **`E_SIMD_BAD_LANES`** at the type-check phase.
See §2 and §9 for full validation rules.

**`LaneIter<E>`** — a simple forward iterator yielding element values in lane order.
Defined in `src/lib/nogc_sync_mut/simd/fixed.spl` (FixedVec version, length known at
compile time) and `src/lib/nogc_sync_mut/simd/scalable.spl` (ScalableVec version,
`ScalableLaneIter<E>` with runtime length). Both implement the standard `Iterator<E>`
protocol via a `next() -> Option<E>` method and a `len() -> usize` method.

---

### §1.1 `Vector` Trait — Core Abstract Operations

The `Vector` trait is the shared contract for all SIMD vector types. It has NO
constructors — those live on the concrete type (`FixedVec`, `ScalableVec`). Associated
types must be declared by each implementor.

```
trait Vector:
    type Elem        # element scalar type
    type Mask        # associated mask type — Mask<Self>

    # — Arithmetic —
    fn add(self, rhs: Self) -> Self
    fn sub(self, rhs: Self) -> Self
    fn mul(self, rhs: Self) -> Self
    fn fma(self, b: Self, c: Self) -> Self     # self*b + c
    fn fnmadd(self, b: Self, c: Self) -> Self  # -(self*b) + c
    fn abs(self) -> Self                        # T: Float only
    fn neg(self) -> Self
    fn min(self, rhs: Self) -> Self
    fn max(self, rhs: Self) -> Self

    # — Bitwise (T: Integer only) —
    fn and(self, rhs: Self) -> Self
    fn or(self, rhs: Self) -> Self
    fn xor(self, rhs: Self) -> Self
    fn andnot(self, rhs: Self) -> Self         # ~self & rhs
    fn shl(self, count: u32) -> Self
    fn shr_logical(self, count: u32) -> Self   # zero-fill
    fn shr_arith(self, count: u32) -> Self     # T: SignedInt

    # — Comparison → Mask —
    fn cmp_eq(self, rhs: Self) -> Self.Mask
    fn cmp_ne(self, rhs: Self) -> Self.Mask
    fn cmp_lt(self, rhs: Self) -> Self.Mask
    fn cmp_le(self, rhs: Self) -> Self.Mask
    fn cmp_gt(self, rhs: Self) -> Self.Mask
    fn cmp_ge(self, rhs: Self) -> Self.Mask

    # — Selection / blend —
    fn mask_select(mask: Self.Mask, t: Self, f: Self) -> Self

    # — Reduction → scalar —
    fn reduce_sum(self) -> Self.Elem
    fn reduce_min(self) -> Self.Elem
    fn reduce_max(self) -> Self.Elem
    fn reduce_and(self) -> Self.Elem           # T: Integer
    fn reduce_or(self) -> Self.Elem            # T: Integer

    # — Permutation / shuffle —
    fn shuffle(self, indices: Self) -> Self    # indices are integer lanes
    fn permute(self, ctrl: Self) -> Self       # same as shuffle but compile-time ctrl
    fn broadcast_lane(self, lane: u32) -> Self
    fn interleave_lo(self, rhs: Self) -> Self
    fn interleave_hi(self, rhs: Self) -> Self

    # — Load / store —
    static fn load_aligned(ptr: *T) -> Self
    static fn load_unaligned(ptr: *T) -> Self
    fn store_aligned(self, ptr: *T)
    fn store_unaligned(self, ptr: *T)

    # — Gather / scatter —
    static fn gather(base: *T, indices: Self) -> Self   # indices T: Integer
    fn scatter(self, base: *T, indices: Self)            # indices T: Integer

    # — Lane count —
    fn lanes(self) -> usize       # runtime for ScalableVec; const for FixedVec
    fn len(self) -> usize         # alias for lanes()

    # — Lane access — (see §10 for indexing syntax)
    fn lane(self, i: usize) -> Self.Elem       # bounds-check in interp; UB if i>=lanes() in compiled
    fn set_lane(self, i: usize, v: Self.Elem) -> Self

    # — Debug —
    fn fmt(self) -> text
    fn to_string(self) -> text    # alias for fmt()

    # — Iteration —
    fn iter(self) -> LaneIter<Self.Elem>    # yields elements in lane order
```

**Table 1.1-A — `Vector` trait full method catalog**

Each row gives the exact Simple signature, element-type constraint, lane-count (N)
constraint, pre/post-conditions, diagnostic code on violation, and Round-1 §-reference.
`Self.Elem` denotes the associated element type; `Self.Mask` denotes the associated mask
type. For `FixedVec<T,N>`, `lanes()` is a compile-time const. For `ScalableVec<T>`,
`lanes()` is a runtime value.

| Method | Exact Simple signature | T constraint | N constraint | Pre / Post | Diagnostic | B1 §-ref |
|--------|----------------------|-------------|-------------|------------|------------|---------|
| `add` | `fn add(self, rhs: Self) -> Self` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.1 |
| `sub` | `fn sub(self, rhs: Self) -> Self` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.1 |
| `mul` | `fn mul(self, rhs: Self) -> Self` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.1 |
| `fma` | `fn fma(self, b: Self, c: Self) -> Self` | Float | Pow2 | — / result = self×b+c | `E_SIMD_FLOAT_ONLY` | B1 §2.1 |
| `fnmadd` | `fn fnmadd(self, b: Self, c: Self) -> Self` | Float | Pow2 | — / result = -(self×b)+c | `E_SIMD_FLOAT_ONLY` | B1 §2.1 |
| `abs` | `fn abs(self) -> Self` | Float | Pow2 | — | `E_SIMD_FLOAT_ONLY` | B1 §2.1 |
| `neg` | `fn neg(self) -> Self` | Numeric | Pow2 | — | — | B1 §2.1 |
| `min` | `fn min(self, rhs: Self) -> Self` | Numeric | Pow2 | — | — | B1 §2.1 |
| `max` | `fn max(self, rhs: Self) -> Self` | Numeric | Pow2 | — | — | B1 §2.1 |
| `and` | `fn and(self, rhs: Self) -> Self` | Integer | Pow2 | — | `E_SIMD_INT_ONLY` | B1 §2.1 |
| `or` | `fn or(self, rhs: Self) -> Self` | Integer | Pow2 | — | `E_SIMD_INT_ONLY` | B1 §2.1 |
| `xor` | `fn xor(self, rhs: Self) -> Self` | Integer | Pow2 | — | `E_SIMD_INT_ONLY` | B1 §2.1 |
| `andnot` | `fn andnot(self, rhs: Self) -> Self` | Integer | Pow2 | — / result = ~self & rhs | `E_SIMD_INT_ONLY` | B1 §2.1 |
| `shl` | `fn shl(self, count: u32) -> Self` | Integer | Pow2 | count < elem_bits | `E_SIMD_INT_ONLY`, `E_SIMD_SHIFT_OOB` | B1 §2.1 |
| `shr_logical` | `fn shr_logical(self, count: u32) -> Self` | Integer | Pow2 | count < elem_bits / zero-fills | `E_SIMD_INT_ONLY`, `E_SIMD_SHIFT_OOB` | B1 §2.1 |
| `shr_arith` | `fn shr_arith(self, count: u32) -> Self` | SignedInt | Pow2 | count < elem_bits / sign-extends | `E_SIMD_INT_ONLY`, `E_SIMD_SHIFT_OOB` | B1 §2.1 |
| `cmp_eq` | `fn cmp_eq(self, rhs: Self) -> Self.Mask` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.2 |
| `cmp_ne` | `fn cmp_ne(self, rhs: Self) -> Self.Mask` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.2 |
| `cmp_lt` | `fn cmp_lt(self, rhs: Self) -> Self.Mask` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.2 |
| `cmp_le` | `fn cmp_le(self, rhs: Self) -> Self.Mask` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.2 |
| `cmp_gt` | `fn cmp_gt(self, rhs: Self) -> Self.Mask` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.2 |
| `cmp_ge` | `fn cmp_ge(self, rhs: Self) -> Self.Mask` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.2 |
| `mask_select` | `static fn mask_select(mask: Self.Mask, t: Self, f: Self) -> Self` | Numeric | Pow2 | mask.lanes == self.lanes | `E_SIMD_LANE_MISMATCH` | B1 §2.3 |
| `reduce_sum` | `fn reduce_sum(self) -> Self.Elem` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.4 |
| `reduce_min` | `fn reduce_min(self) -> Self.Elem` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.4 |
| `reduce_max` | `fn reduce_max(self) -> Self.Elem` | Numeric | Pow2 | — | `E_SIMD_TYPE_MISMATCH` | B1 §2.4 |
| `reduce_and` | `fn reduce_and(self) -> Self.Elem` | Integer | Pow2 | — | `E_SIMD_INT_ONLY` | B1 §2.4 |
| `reduce_or` | `fn reduce_or(self) -> Self.Elem` | Integer | Pow2 | — | `E_SIMD_INT_ONLY` | B1 §2.4 |
| `shuffle` | `fn shuffle(self, indices: Self) -> Self` | Numeric | Pow2 | indices T must be Integer | `E_SIMD_TYPE_MISMATCH` | B1 §2.5 |
| `permute` | `fn permute(self, ctrl: Self) -> Self` | Numeric | Pow2 | ctrl must be compile-time const | `E_SIMD_CONST_REQUIRED` | B1 §2.5 |
| `broadcast_lane` | `fn broadcast_lane(self, lane: u32) -> Self` | Numeric | Pow2 | lane < lanes() | `E_SIMD_LANE_OOB` | B1 §2.5 |
| `interleave_lo` | `fn interleave_lo(self, rhs: Self) -> Self` | Numeric | Pow2 | — | — | B1 §2.5 |
| `interleave_hi` | `fn interleave_hi(self, rhs: Self) -> Self` | Numeric | Pow2 | — | — | B1 §2.5 |
| `load_aligned` | `static fn load_aligned(ptr: *T) -> Self` | Numeric | Pow2 | ptr aligned to N×sizeof(T) | — (UB in compiled if violated) | B1 §2.6 |
| `load_unaligned` | `static fn load_unaligned(ptr: *T) -> Self` | Numeric | Pow2 | ptr != null | — | B1 §2.6 |
| `store_aligned` | `fn store_aligned(self, ptr: *T)` | Numeric | Pow2 | ptr aligned to N×sizeof(T) | — (UB in compiled if violated) | B1 §2.6 |
| `store_unaligned` | `fn store_unaligned(self, ptr: *T)` | Numeric | Pow2 | ptr != null | — | B1 §2.6 |
| `gather` | `static fn gather(base: *T, indices: Self) -> Self` | Numeric | Pow2 | indices must be Integer T | `E_SIMD_TYPE_MISMATCH` | B1 §2.6 |
| `scatter` | `fn scatter(self, base: *T, indices: Self)` | Numeric | Pow2 | indices must be Integer T | `E_SIMD_TYPE_MISMATCH` | B1 §2.6 |
| `lanes` | `fn lanes(self) -> usize` | Numeric | Pow2 | — / const for FixedVec, runtime for ScalableVec | — | B1 §2.1 |
| `len` | `fn len(self) -> usize` | Numeric | Pow2 | alias for `lanes()` | — | B1 §2.1 |
| `lane` | `fn lane(self, i: usize) -> Self.Elem` | Numeric | Pow2 | i < lanes() | `E_SIMD_LANE_OOB` (runtime in interp, compile-time if i is const) | B1 §2.1 |
| `set_lane` | `fn set_lane(self, i: usize, v: Self.Elem) -> Self` | Numeric | Pow2 | i < lanes() | `E_SIMD_LANE_OOB` | B1 §2.1 |
| `fmt` | `fn fmt(self) -> text` | Numeric | Pow2 | — | — | B1 §2.1 |
| `to_string` | `fn to_string(self) -> text` | Numeric | Pow2 | alias for `fmt()` | — | B1 §2.1 |
| `iter` | `fn iter(self) -> LaneIter<Self.Elem>` | Numeric | Pow2 | — / yields lanes in order | — | B1 §2.1 |

**Total `Vector` trait methods: 46**

---

### §1.2 `FixedVec<T, const N>` — Additional Methods

`FixedVec<T,N>` implements `Vector` and adds compile-time-constant ops:

```
class FixedVec<T, const N: usize>:
    type Elem = T
    type Mask = Mask<FixedVec<T, N>>

impl<T: Numeric, const N: usize> FixedVec<T, N>:

    # — Construction —
    static fn splat(val: T) -> Self
    static fn zero() -> Self                              # splat(0)
    static fn from_array(arr: [T]) -> Self                # arr.len() must == N
    static fn from_slice(s: &[T]) -> Self                 # s.len() must >= N
    fn to_array(self) -> [T; N]
    fn to_slice(self, out: &mut [T])                      # out.len() must >= N

    # — Type conversion —
    fn cast<U: Numeric>(self) -> FixedVec<U, N>           # element-wise numeric cast
    fn widen(self) -> FixedVec<U, N> where U is 2x-width of T   # e.g. i16→i32
    fn narrow(self) -> FixedVec<U, N> where U is half-width of T # with saturation

    # — ScalableVec interop —
    fn to_scalable(self) -> ScalableVec<T>                # always valid; pads if needed
    static fn try_from_scalable(v: ScalableVec<T>) -> Option<FixedVec<T, N>>  # runtime check

    # — Compile-time lane metadata —
    const fn lane_count() -> usize                        # always N
    const fn byte_width() -> usize                        # N * sizeof(T)

    # — Zip / spread —
    fn zip_lo(self, rhs: Self) -> Self                    # = interleave_lo
    fn zip_hi(self, rhs: Self) -> Self                    # = interleave_hi
    fn unzip_even(self) -> FixedVec<T, N/2>
    fn unzip_odd(self) -> FixedVec<T, N/2>

    # — Preferred-lane hint (const) —
    static const fn preferred_lanes_for_target() -> usize  # see §3.3
```

**Table 1.2-A — `FixedVec<T,N>` additional method catalog**

| Method | Exact Simple signature | T constraint | N constraint | Pre / Post | Diagnostic | B1 §-ref |
|--------|----------------------|-------------|-------------|------------|------------|---------|
| `splat` | `static fn splat(val: T) -> Self` | Numeric | Pow2 | — | — | B1 §2.1 |
| `zero` | `static fn zero() -> Self` | Numeric | Pow2 | — / all lanes 0 | — | B1 §2.1 |
| `from_array` | `static fn from_array(arr: [T]) -> Self` | Numeric | Pow2 | arr.len() == N | `E_SIMD_ARRAY_LEN_MISMATCH` | B1 §2.1 |
| `from_slice` | `static fn from_slice(s: &[T]) -> Self` | Numeric | Pow2 | s.len() >= N | `E_SIMD_SLICE_TOO_SHORT` | B1 §2.1 |
| `to_array` | `fn to_array(self) -> [T; N]` | Numeric | Pow2 | — | — | B1 §2.1 |
| `to_slice` | `fn to_slice(self, out: &mut [T])` | Numeric | Pow2 | out.len() >= N | `E_SIMD_SLICE_TOO_SHORT` | B1 §2.1 |
| `cast` | `fn cast<U: Numeric>(self) -> FixedVec<U, N>` | Numeric | Pow2 | U: Numeric | `E_SIMD_TYPE_MISMATCH` | B1 §2.1 |
| `widen` | `fn widen(self) -> FixedVec<U, N>` | Numeric | Pow2 | 2×sizeof(T) type must exist | `E_SIMD_NO_WIDEN_TYPE` | B1 §2.1 |
| `narrow` | `fn narrow(self) -> FixedVec<U, N>` | Numeric | Pow2 | sizeof(T)/2 type must exist / saturating | `E_SIMD_NO_NARROW_TYPE` | B1 §2.1 |
| `to_scalable` | `fn to_scalable(self) -> ScalableVec<T>` | Numeric | Pow2 | N <= min_lanes recommended | `W_SIMD_FIXED_EXCEEDS_MIN_LANES` | B1 §2.4 |
| `try_from_scalable` | `static fn try_from_scalable(v: ScalableVec<T>) -> Option<Self>` | Numeric | Pow2 | runtime v.lanes() == N | — (None if mismatch) | B1 §2.4 |
| `lane_count` | `const fn lane_count() -> usize` | Numeric | Pow2 | — / returns N | — | B1 §2.1 |
| `byte_width` | `const fn byte_width() -> usize` | Numeric | Pow2 | — / returns N×sizeof(T) | — | B1 §2.1 |
| `zip_lo` | `fn zip_lo(self, rhs: Self) -> Self` | Numeric | Pow2 | — / alias for interleave_lo | — | B1 §2.5 |
| `zip_hi` | `fn zip_hi(self, rhs: Self) -> Self` | Numeric | Pow2 | — / alias for interleave_hi | — | B1 §2.5 |
| `unzip_even` | `fn unzip_even(self) -> FixedVec<T, N/2>` | Numeric | Pow2, N>=4 | N even and >= 4 | `E_SIMD_BAD_LANES` | B1 §2.5 |
| `unzip_odd` | `fn unzip_odd(self) -> FixedVec<T, N/2>` | Numeric | Pow2, N>=4 | N even and >= 4 | `E_SIMD_BAD_LANES` | B1 §2.5 |
| `preferred_lanes_for_target` | `static const fn preferred_lanes_for_target() -> usize` | Numeric | Pow2 | — / compile-time const | — | B1 §6 |

**Total `FixedVec<T,N>` additional methods: 18 (plus 46 inherited from `Vector` = 64 total)**

---

### §1.3 `ScalableVec<T>` — Additional Methods

`ScalableVec<T>` implements `Vector` with runtime-determined lane count.

```
class ScalableVec<T>:
    type Elem = T
    type Mask = Mask<ScalableVec<T>>

impl<T: Numeric> ScalableVec<T>:

    # — Construction —
    static fn splat(val: T) -> Self                       # runtime lanes
    static fn splat_n(val: T, n: usize) -> Self           # explicit lane count
    static fn zero() -> Self

    # — Lane count (runtime) —
    fn lanes(self) -> usize                               # calls svcntw/vlenb ABI (see §4)
    fn len(self) -> usize                                 # alias
    static const fn min_lanes() -> usize                  # compile-time architectural minimum (see §4)

    # — Interop with FixedVec —
    static fn from_fixed<const N: usize>(v: FixedVec<T, N>) -> Self
        # N <= min_lanes() required; else E_SIMD_FIXED_OVERFLOWS_SCALABLE
    fn try_to_fixed<const N: usize>(self) -> Option<FixedVec<T, N>>
        # runtime check: self.lanes() == N

    # — Load / store (stride-aware) —
    static fn load_strided(ptr: *T, stride: usize, n: usize) -> Self
    fn store_strided(self, ptr: *T, stride: usize)

    # — PTX: not supported —
    # All ScalableVec methods emit E_SIMD_PTX_NO_SCALABLE if target is PTX/CUDA
```

**Table 1.3-A — `ScalableVec<T>` additional method catalog**

| Method | Exact Simple signature | T constraint | Pre / Post | Diagnostic | B1 §-ref |
|--------|----------------------|-------------|------------|------------|---------|
| `splat` | `static fn splat(val: T) -> Self` | Numeric | — / runtime lanes | — | B1 §2.4 |
| `splat_n` | `static fn splat_n(val: T, n: usize) -> Self` | Numeric | n > 0 | `E_SIMD_BAD_LANES` | B1 §2.4 |
| `zero` | `static fn zero() -> Self` | Numeric | — | — | B1 §2.4 |
| `lanes` | `fn lanes(self) -> usize` | Numeric | runtime / calls svcnt*/vlenb ABI | — | B1 §2.4 |
| `len` | `fn len(self) -> usize` | Numeric | alias for lanes() | — | B1 §2.4 |
| `min_lanes` | `static const fn min_lanes() -> usize` | Numeric | compile-time arch min | — | B1 §2.4 |
| `from_fixed` | `static fn from_fixed<const N: usize>(v: FixedVec<T, N>) -> Self` | Numeric | N <= min_lanes() | `E_SIMD_FIXED_OVERFLOWS_SCALABLE` | B1 §2.4 |
| `try_to_fixed` | `fn try_to_fixed<const N: usize>(self) -> Option<FixedVec<T, N>>` | Numeric | runtime self.lanes() == N / None if mismatch | — | B1 §2.4 |
| `load_strided` | `static fn load_strided(ptr: *T, stride: usize, n: usize) -> Self` | Numeric | n > 0, ptr != null | — | B1 §2.6 |
| `store_strided` | `fn store_strided(self, ptr: *T, stride: usize)` | Numeric | ptr != null | — | B1 §2.6 |

**Note:** Any method called on PTX/CUDA target emits `E_SIMD_PTX_NO_SCALABLE` (B1 §7.4).

**Total `ScalableVec<T>` additional methods: 10 (plus 46 inherited from `Vector` = 56 total)**

---

### §1.4 `Mask<V>` — Full Method Catalog

`Mask<V>` is parameterized by the vector type `V` (not just lane count). This preserves
element-width information needed for SVE2 predicate granularity and RVV mask layout.
`Mask<FixedVec<f32,4>>` and `Mask<FixedVec<i32,4>>` are distinct types even though both
have 4 lanes; they carry different per-lane byte widths used in backend mask-register
allocation. See §5 for the materialization decision table.

```
trait Mask<V: Vector>:
    type Vec = V

impl<V: Vector> Mask<V>:

    # — Construction —
    static fn from_bits(bits: u64) -> Self
        # bits[i] == 1 means lane i is active; N bits used, rest ignored
        # For ScalableVec: bits must fit in runtime lanes count; else E_SIMD_MASK_BITS_OOB
    static fn all_ones() -> Self
    static fn all_zeros() -> Self
    static fn from_cmp(cmp_result: V.Mask) -> Self        # identity cast

    # — Logical operations —
    fn and(self, rhs: Self) -> Self
    fn or(self, rhs: Self) -> Self
    fn xor(self, rhs: Self) -> Self
    fn not(self) -> Self
    fn andnot(self, rhs: Self) -> Self    # ~self & rhs

    # — Queries —
    fn count_ones(self) -> usize
    fn any(self) -> bool
    fn all(self) -> bool
    fn none(self) -> bool
    fn lane_active(self, i: usize) -> bool   # single-lane test

    # — Conversion —
    fn to_bits(self) -> u64    # low N bits set per active lane; N must be <= 64
    fn to_bitmask_u32(self) -> u32   # for AVX-512 k-reg extraction (N <= 32)

    # — PTX predicate handle (compile-only) —
    fn ptx_preg_handle(self) -> u32   # E_SIMD_COMPILE_ONLY in interpreter (see §7)
```

**Table 1.4-A — `Mask<V>` full method catalog**

| Method | Exact Simple signature | Pre / Post | Diagnostic | B1 §-ref |
|--------|----------------------|------------|------------|---------|
| `from_bits` | `static fn from_bits(bits: u64) -> Self` | lane count <= 64 / bits[i]=1 means lane i active | `E_SIMD_MASK_BITS_OOB` | B1 §2.3 |
| `all_ones` | `static fn all_ones() -> Self` | — / all lanes active | — | B1 §2.3 |
| `all_zeros` | `static fn all_zeros() -> Self` | — / no lanes active | — | B1 §2.3 |
| `from_cmp` | `static fn from_cmp(cmp_result: V.Mask) -> Self` | — / identity cast | — | B1 §2.3 |
| `and` | `fn and(self, rhs: Self) -> Self` | same V type | `E_SIMD_MASK_TYPE_MISMATCH` | B1 §2.3 |
| `or` | `fn or(self, rhs: Self) -> Self` | same V type | `E_SIMD_MASK_TYPE_MISMATCH` | B1 §2.3 |
| `xor` | `fn xor(self, rhs: Self) -> Self` | same V type | `E_SIMD_MASK_TYPE_MISMATCH` | B1 §2.3 |
| `not` | `fn not(self) -> Self` | — | — | B1 §2.3 |
| `andnot` | `fn andnot(self, rhs: Self) -> Self` | same V type / result = ~self & rhs | `E_SIMD_MASK_TYPE_MISMATCH` | B1 §2.3 |
| `count_ones` | `fn count_ones(self) -> usize` | — / popcount of active lanes | — | B1 §2.3 |
| `any` | `fn any(self) -> bool` | — / true if any lane active | — | B1 §2.3 |
| `all` | `fn all(self) -> bool` | — / true if all lanes active | — | B1 §2.3 |
| `none` | `fn none(self) -> bool` | — / true if no lane active | — | B1 §2.3 |
| `lane_active` | `fn lane_active(self, i: usize) -> bool` | i < lane count | `E_SIMD_LANE_OOB` | B1 §2.3 |
| `to_bits` | `fn to_bits(self) -> u64` | lane count <= 64 | `E_SIMD_MASK_BITS_OOB` | B1 §2.3 |
| `to_bitmask_u32` | `fn to_bitmask_u32(self) -> u32` | lane count <= 32 | `E_SIMD_MASK_BITS_OOB` | B1 §2.3 |
| `ptx_preg_handle` | `fn ptx_preg_handle(self) -> u32` | compile mode only / returns PTX %p-reg index | `E_SIMD_COMPILE_ONLY` | B1 §7.4 |

**Total `Mask<V>` methods: 17**

---

### §1.5 `WarpVec<T>` — GPU-Only Extension Trait

`WarpVec<T>` extends `Vector` for CUDA/PTX and SPIR-V subgroup targets.
Calling any method outside a GPU kernel context is a compile-time error enforced by
`35.semantics/gpu_checker.spl`.

```
trait WarpVec<T: Numeric>: Vector:
    # — Shuffle within warp —
    fn shfl_up(self, delta: u32, mask: u32) -> Self
        # Shift value from lane (self_lane - delta); mask includes self; lane bound: delta < 32
    fn shfl_down(self, delta: u32, mask: u32) -> Self
        # Shift value from lane (self_lane + delta); mask includes self
    fn shfl_xor(self, lane_mask: u32, mask: u32) -> Self
        # XOR lane id with lane_mask to select source; shfl_bfly in B1
    fn shfl_idx(self, src_lane: u32, mask: u32) -> Self
        # Broadcast from specific src_lane; 0 <= src_lane < warp_size

    # — Warp reductions → scalar —
    fn warp_reduce_sum(self, mask: u32) -> T
    fn warp_reduce_min(self, mask: u32) -> T
    fn warp_reduce_max(self, mask: u32) -> T
    fn warp_reduce_any(self, mask: u32) -> bool    # T: Integer
    fn warp_reduce_all(self, mask: u32) -> bool    # T: Integer

    # — Ballot / vote —
    static fn warp_ballot(predicate: bool, mask: u32) -> u32
        # PTX: vote.sync.ballot.b32; SPIR-V: OpGroupNonUniformBallot
    static fn warp_active_mask() -> u32
        # PTX: activemask.b32; SPIR-V: OpSubgroupMask built-in

    # — Synchronization —
    static fn warp_sync(mask: u32)
        # PTX: bar.warp.sync; ensures all threads in mask reach this point
        # SPIR-V: OpControlBarrier(Subgroup, Subgroup, AcquireRelease)

    # — Subgroup size queries —
    static const fn target_warp_size_const() -> usize
        # Compile-time const: PTX → 32; SPIR-V/Vulkan → determined by pipeline specialization const
        # Returns E_WARP_SIZE_RUNTIME_ONLY if not known at compile time
    static fn target_warp_size_runtime() -> usize
        # Runtime value; PTX: reads warpSize; SPIR-V: reads gl_SubgroupSize built-in
    static fn subgroup_size_query() -> usize
        # Alias for target_warp_size_runtime(); preferred name for SPIR-V contexts
```

**Table 1.5-A — `WarpVec<T>` full method catalog**

| Method | Exact Simple signature | T constraint | Pre / Post | Diagnostic | Backend lowering |
|--------|----------------------|-------------|------------|------------|-----------------|
| `shfl_up` | `fn shfl_up(self, delta: u32, mask: u32) -> Self` | Numeric | delta < warp_size; mask includes self-lane / result from lane (self-delta) | `E_WARP_DELTA_OOB`, `E_WARP_SELF_EXCLUDED` | PTX `shfl.sync.up.b32`; SPIR-V `OpGroupNonUniformShuffleUp` |
| `shfl_down` | `fn shfl_down(self, delta: u32, mask: u32) -> Self` | Numeric | delta < warp_size; mask includes self-lane / result from lane (self+delta) | `E_WARP_DELTA_OOB`, `E_WARP_SELF_EXCLUDED` | PTX `shfl.sync.down.b32`; SPIR-V `OpGroupNonUniformShuffleDown` |
| `shfl_xor` | `fn shfl_xor(self, lane_mask: u32, mask: u32) -> Self` | Numeric | mask includes self-lane / result from lane (self XOR lane_mask) | `E_WARP_SELF_EXCLUDED` | PTX `shfl.sync.bfly.b32`; SPIR-V `OpGroupNonUniformShuffleXor` |
| `shfl_idx` | `fn shfl_idx(self, src_lane: u32, mask: u32) -> Self` | Numeric | 0 <= src_lane < warp_size; mask includes self-lane | `E_WARP_LANE_OOB`, `E_WARP_SELF_EXCLUDED` | PTX `shfl.sync.idx.b32`; SPIR-V `OpGroupNonUniformShuffle` |
| `warp_reduce_sum` | `fn warp_reduce_sum(self, mask: u32) -> T` | Numeric | — / XOR-tree reduction | — | PTX `shfl.sync.bfly` tree; SPIR-V `OpGroupNonUniformFAdd(Reduce)` |
| `warp_reduce_min` | `fn warp_reduce_min(self, mask: u32) -> T` | Numeric | — | — | PTX shuffle-tree; SPIR-V `OpGroupNonUniformFMin(Reduce)` |
| `warp_reduce_max` | `fn warp_reduce_max(self, mask: u32) -> T` | Numeric | — | — | PTX shuffle-tree; SPIR-V `OpGroupNonUniformFMax(Reduce)` |
| `warp_reduce_any` | `fn warp_reduce_any(self, mask: u32) -> bool` | Integer | — | `E_SIMD_INT_ONLY` | PTX `vote.sync.any.pred`; SPIR-V `OpGroupNonUniformAny` |
| `warp_reduce_all` | `fn warp_reduce_all(self, mask: u32) -> bool` | Integer | — | `E_SIMD_INT_ONLY` | PTX `vote.sync.all.pred`; SPIR-V `OpGroupNonUniformAll` |
| `warp_ballot` | `static fn warp_ballot(predicate: bool, mask: u32) -> u32` | — | — / returns active-lane bitmask | — | PTX `vote.sync.ballot.b32`; SPIR-V `OpGroupNonUniformBallot` |
| `warp_active_mask` | `static fn warp_active_mask() -> u32` | — | — / currently active lanes | — | PTX `activemask.b32`; SPIR-V `OpLoad %SubgroupEqMask` (see §12 OQ-F) |
| `warp_sync` | `static fn warp_sync(mask: u32)` | — | mask != 0 | `W_WARP_SYNC_EMPTY_MASK` | PTX `bar.warp.sync`; SPIR-V `OpControlBarrier(Subgroup,Subgroup,AcquireRelease)` |
| `target_warp_size_const` | `static const fn target_warp_size_const() -> usize` | — | compile-time known warp size | `E_WARP_SIZE_RUNTIME_ONLY` | compile-time const: PTX=32, RDNA=variable |
| `target_warp_size_runtime` | `static fn target_warp_size_runtime() -> usize` | — | — / runtime warp size | — | PTX `warpSize`; SPIR-V `gl_SubgroupSize` |
| `subgroup_size_query` | `static fn subgroup_size_query() -> usize` | — | alias for `target_warp_size_runtime()` | — | preferred name for SPIR-V contexts |

**Global constraints for all `WarpVec<T>` methods:**
- Must be called inside a GPU kernel function (`35.semantics/gpu_checker.spl` enforces) — else `E_WARP_NOT_IN_KERNEL`
- Apple M-series target: all methods emit `E_WARP_NO_APPLE_M` (C1-DEEP §6-H)

**Total `WarpVec<T>` additional methods: 15 (plus 46 inherited from `Vector` = 61 total)**

---

### §1.6 Method Count Summary

| Type | Inherited from `Vector` | Type-specific methods | Total |
|------|--------------------|----------------------|-------|
| `Vector` (trait) | — | 46 | 46 |
| `FixedVec<T,N>` | 46 | 18 | 64 |
| `ScalableVec<T>` | 46 | 10 | 56 |
| `Mask<V>` | — | 17 | 17 |
| `WarpVec<T>` | 46 | 15 | 61 |
| **Total catalog rows** | | | **183** |

The 183 total includes methods that appear on multiple types (e.g. `splat` on both
`FixedVec` and `ScalableVec`). Distinct method *names* across all types: ~100.

---

## §2 Type-System Rules

### §2.1 Const-N Validity

Valid N values for `FixedVec<T, const N>`:

```
N ∈ {2, 4, 8, 16, 32, 64}
```

All other values (including 0, 1, 3, 5, 6, 7, etc.) emit `E_SIMD_BAD_LANES` at
the type-check phase (`35.semantics/simd_check.spl`). This cap enforces the
monomorphization budget from B1 §9 OQ-3.

**Preferred N per target and T** (citing C1-DEEP §4 latency tables):

| Target | T | Preferred N | Notes |
|--------|---|-------------|-------|
| x86-64 AVX-512 | f32 | 16 | Full ZMM register; C1-DEEP §4.1 |
| x86-64 AVX-512 | f64 | 8 | Full ZMM register |
| x86-64 AVX-512 | i32 | 16 | Full ZMM register |
| x86-64 AVX-512 | i64 | 8 | Full ZMM register |
| x86-64 AVX2 | f32 | 8 | Full YMM register |
| x86-64 AVX2 | f64 | 4 | Full YMM register |
| x86-64 AVX2 | i32 | 8 | Full YMM register |
| x86-64 SSE2 | f32 | 4 | Full XMM register |
| x86-64 SSE2 | f64 | 2 | Full XMM register |
| x86-64 SSE2 | i32 | 4 | Full XMM register |
| ARM NEON (AArch64) | f32 | 4 | Full Q-register; C1-ISA §1.1 |
| ARM NEON (AArch64) | f64 | 2 | Full Q-register |
| ARM NEON (AArch64) | i32 | 4 | Full Q-register |
| ARM SVE2 | f32 | 4 (min_lanes) | VL-agnostic; prefer ScalableVec; C1-ISA §2.1 |
| RISC-V RVV | f32 | 4 (at VLEN=128, LMUL=1) | VL-agnostic; prefer ScalableVec; C1-ISA §2.2 |
| PTX/CUDA | f32 | 1 per thread (32 threads = warp) | Use WarpVec for cross-lane; C1-ISA §3.1 |

Users can query at compile time:

```
val n = FixedVec<f32, 4>::preferred_lanes_for_target()
```

This returns a compile-time usize const derived from `SimdFeatureFlags` (B1 §6).

### §2.2 Auto-Coercion Rules

`FixedVec<T,N>` literals are **never auto-created**. The following rules apply:

1. `splat(0.0)` on `FixedVec<f32,4>` — valid; `T` inferred as `f32`, `N` inferred from context.
   - If context is ambiguous (no annotation and no expected type), emits `E_SIMD_TYPE_AMBIGUOUS`.
2. `splat(0)` — `T` defaults to `i32` if no annotation; `N` must be explicit or context-inferred.
3. `[1.0f32; lanes 4]` (vector literal syntax, §10) → `FixedVec<f32,4>` directly.
4. **No implicit cast** between `FixedVec<f32,4>` and `FixedVec<f64,4>` — use `.cast<f64>()`.
5. **No implicit cast** between `FixedVec<f32,4>` and `FixedVec<f32,8>` — these are different types.

### §2.3 Mask Type Identity Rules

`Mask<V>` is a distinct type for each `V`:

- `Mask<FixedVec<f32,4>>` ≠ `Mask<FixedVec<i32,4>>` — different types.
  - Rationale: SVE2 predicate registers are element-width-sensitive (bit-per-byte vs
    bit-per-element); RVV v0 layout depends on SEW. Separating them preserves exact
    backend semantics without coercion. C1-ISA §2.1, §2.2.
  - AVX-512 k-registers are bit-per-lane regardless of element width, so both types
    lower to k-regs but remain separately typed at the Simple level.
- `Mask<FixedVec<f32,4>>` ≠ `Mask<FixedVec<f32,8>>` — different lane count.
- `Mask<ScalableVec<f32>>` ≠ `Mask<ScalableVec<i32>>` — separate scalable masks.
- Comparing or blending masks of different V emits `E_SIMD_MASK_TYPE_MISMATCH`.

### §2.4 Generic Bounds Composition

`where T: Numeric` and `where N: Pow2` compose as AND constraints. Both must hold.

**Table 2.4-A — Accepted/Rejected Type Examples**

| Type | Status | Reason |
|------|--------|--------|
| `FixedVec<f32, 4>` | Accepted | T=f32 ∈ Numeric; N=4 ∈ Pow2; has backend lowering |
| `FixedVec<f64, 16>` | Accepted (with warning) | Valid types; no AVX-512-f64x16 exists — emits `W_SIMD_NO_NATIVE_LOWERING`, falls back to scalar or split |
| `FixedVec<bool, 4>` | Rejected | `bool` ∉ Numeric — emits `E_SIMD_TYPE_MISMATCH` |
| `FixedVec<f32, 3>` | Rejected | N=3 ∉ Pow2 — emits `E_SIMD_BAD_LANES` |
| `FixedVec<i32, 0>` | Rejected | N=0 — emits `E_SIMD_BAD_LANES` |
| `FixedVec<*T, 4>` | Rejected | pointer ∉ Numeric — emits `E_SIMD_TYPE_MISMATCH` |
| `ScalableVec<f32>` | Accepted | T=f32 ∈ Numeric; N is runtime |
| `Mask<FixedVec<f32,4>>` | Accepted | valid mask for 4-lane f32 vector |
| `FixedVec<i8, 64>` | Accepted | i8 ∈ Numeric; N=64 ∈ Pow2; maps to 512-bit AVX-512 |
| `FixedVec<f32, 1>` | Rejected | N=1 — emits `E_SIMD_BAD_LANES` |

### §2.5 Trait-Impl Visibility

`[T; N]` (plain Simple arrays) do **NOT** automatically implement `Vector`. The SIMD
types are opt-in; users explicitly use `FixedVec` or `ScalableVec`. The conversion path
is `FixedVec<T,N>::from_array(arr)` and `.to_array()`.

This avoids ambiguity between array ops and SIMD ops and prevents unintended SIMD
codegen on value types.

No blanket impl of `Vector` for any standard library type.

---

## §3 Monomorphization Rules

### §3.1 Decision Table: (target, T, N) → backend module

`FixedVec<T,N>` is fully monomorphized at the call site. The compiler selects the
backend lowering module using this priority order:

1. If target has native N-wide T register → emit native intrinsic.
2. If target has a larger register → split N lanes across multiple native-width ops
   (see §3.2 fallback chain).
3. If target has only smaller registers → tile/split into multiple ops.
4. If no SIMD support → scalar-fallback loop (see §3.2).

**Table 3.1-A — (target × T × N) → backend module**

| Target | T | N | Backend Module | Notes |
|--------|---|---|---------------|-------|
| x86-64 AVX-512 | f32 | 16 | `x86_64_avx512.spl::SimdAvx512F32x16` | native ZMM |
| x86-64 AVX-512 | f32 | 8 | `x86_64_avx512.spl::SimdAvx512F32x8` | YMM via VL |
| x86-64 AVX-512 | f32 | 4 | `x86_64_avx512.spl::SimdAvx512F32x4` | XMM via VL |
| x86-64 AVX-512 | f64 | 8 | `x86_64_avx512.spl::SimdAvx512F64x8` | native ZMM |
| x86-64 AVX-512 | f64 | 4 | `x86_64_avx512.spl::SimdAvx512F64x4` | YMM via VL |
| x86-64 AVX-512 | i32 | 16 | `x86_64_avx512.spl::SimdAvx512I32x16` | native ZMM BW |
| x86-64 AVX-512 | i64 | 8 | `x86_64_avx512.spl::SimdAvx512I64x8` | native ZMM |
| x86-64 AVX2 | f32 | 8 | `x86_64_simd.spl::SimdAvx2F32x8` | native YMM |
| x86-64 AVX2 | f32 | 4 | `x86_64_simd.spl::SimdAvx2F32x4` | XMM |
| x86-64 AVX2 | f64 | 4 | `x86_64_simd.spl::SimdAvx2F64x4` | native YMM |
| x86-64 AVX2 | i32 | 8 | `x86_64_simd.spl::SimdAvx2I32x8` | native YMM |
| x86-64 SSE2 | f32 | 4 | `x86_64_simd.spl::SimdSse2F32x4` | native XMM |
| x86-64 SSE2 | f64 | 2 | `x86_64_simd.spl::SimdSse2F64x2` | native XMM |
| x86-64 SSE2 | i32 | 4 | `x86_64_simd.spl::SimdSse2I32x4` | native XMM |
| ARM NEON | f32 | 4 | `arm_neon.spl::SimdNeonF32x4` | native Q-reg |
| ARM NEON | f64 | 2 | `arm_neon.spl::SimdNeonF64x2` | native Q-reg |
| ARM NEON | i32 | 4 | `arm_neon.spl::SimdNeonI32x4` | native Q-reg |
| ARM NEON | i32 | 8 | `arm_neon.spl::SimdNeonI32x4 × 2` | split |
| ARM SVE2 | f32 | 4 | `arm_sve2.spl::SimdSve2F32` | prefer ScalableVec; FixedVec uses NEON path on SVE2 targets |
| RISC-V RVV | f32 | 4 | `riscv_rvv.spl::SimdRvvF32` | prefer ScalableVec; FixedVec uses scalar fallback pending RVV ISel |
| PTX/CUDA | f32 | 1 | `ptx_builder.spl::SimdPtxScalar` | per-thread scalar; WarpVec for cross-lane |
| Scalar fallback | any T | any N | `scalar_fallback.spl::SimdScalarLoop` | O(N) loop; no SIMD |

### §3.2 Fallback Chain

When the target lacks a native instruction for the exact (T,N) pair, the compiler
applies this ordered policy in `60.mir_opt/simd_split_unsupported.spl`:

```
Phase 1 — native: emit native op if target register width == N * sizeof(T).

Phase 2 — split into sub-width: if N * sizeof(T) > target_register_width,
           split into ceil(N / native_N) ops of FixedVec<T, native_N>.
           Example: (x86-64 SSE2, f32, 16) → 4× FixedVec<f32, 4>

Phase 3 — widen to next available register: if N * sizeof(T) < target_register_width
           AND N is valid for the next larger register on target,
           prefer native_N even if overkill (e.g. 2× f32 on AVX2 → use 4× XMM).

Phase 4 — scalar fallback: if no SIMD support on target (or unsupported T),
           emit O(N) scalar loop in MIR. No SIMD instructions produced.
           Emits W_SIMD_SCALAR_FALLBACK warning.
```

**Example:** `(x86-64-sse2, f32, 16)`:
1. Native: SSE2 XMM = 128 bits = 4× f32 ≠ 16× f32. Skip.
2. Split: 16/4 = 4 ops of `FixedVec<f32,4>` → `SimdSse2F32x4`. Use this.
MIR: `MirSimdSplitOp(lanes=16, sub_lanes=4, op=SimdSse2F32x4)` (see §8).

**Example:** `(arm-neon-only, f64, 16)`:
1. Native: NEON Q-reg = 128 bits = 2× f64 ≠ 16× f64. Skip.
2. Split: 16/2 = 8 ops of `FixedVec<f64,2>`. Use this.
Emits `W_SIMD_NO_NATIVE_LOWERING` if user used `@simd` annotation (forced vectorization).

**Example:** `(arm-neon-only, f64, 16)` with `@simd(require_native)`:
→ Emits `E_SIMD_NO_LOWERING(arm-neon, f64, 16)` with fix-it: "Use N=2 (preferred for NEON-f64)".

### §3.3 `SimdLanesPreferred<T>(target)` Const Function

Users can query the preferred lane count at compile time:

```
# In src/lib/nogc_sync_mut/simd/platform.spl
static const fn simd_lanes_preferred<T: Numeric>() -> usize
    # Returns preferred N for T on the current compile target.
    # AVX-512: f32→16, f64→8, i32→16, i64→8
    # AVX2: f32→8, f64→4, i32→8
    # SSE2: f32→4, f64→2, i32→4
    # NEON: f32→4, f64→2, i32→4
    # SVE2: f32→4 (min_lanes; scalable preferred over fixed)
    # RVV: f32→4 (min_lanes at VLEN=128)
    # Scalar: 1
```

Usage:

```
const N = simd_lanes_preferred<f32>()
val v: FixedVec<f32, N> = FixedVec<f32, N>::splat(1.0)
```

### §3.4 Monomorphization Failure

If no lowering exists (including scalar fallback) for (target, T, N):

```
E_SIMD_NO_LOWERING(target: text, T: TypeId, N: usize)
```

Fix-it: suggests `N = simd_lanes_preferred<T>()` for the target.

Example bad source:

```
val v: FixedVec<f32, 64> = FixedVec<f32, 64>::splat(1.0)  # on x86-64-sse2-only target
```

→ `E_SIMD_NO_LOWERING(x86-64-sse2, f32, 64)`: No native lowering; split would require 16
   ops of size 4. Consider using N=4 or N=8, or rewrite with ScalableVec<f32>.

Note: `(x86-64-sse2, f32, 64)` does NOT fail — it uses the split fallback chain (Phase 2).
`E_SIMD_NO_LOWERING` only fires when `@simd(require_native)` is set or when even scalar
fallback is disabled by user pragma.

---

## §4 `ScalableVec<T>` Semantics — vscale-Bound

### §4.1 `lanes()` Runtime ABI

`lanes()` is a runtime call with target-specific ABI:

| Target | ABI Call | Notes |
|--------|----------|-------|
| ARM SVE2 | `svcntw()` for f32/i32; `svcntd()` for f64/i64; `svcntb()` for i8; `svcnth()` for i16 | Returns element count per SVE register; C1-ISA §2.1 |
| RISC-V RVV | `csrr t0, vlenb` then `t0 / sizeof(T)` | vlenb = VLEN/8 bytes; C1-ISA §2.2 §3 |

In MIR, `lanes()` on `ScalableVec<T>` lowers to `MirSimdScalableVsetvl(t: T)` (see §8.5).

### §4.2 `min_lanes()` Compile-Time ABI

`min_lanes()` is a compile-time const (no runtime cost):

| Target | T | min_lanes | Derivation |
|--------|---|-----------|-----------|
| SVE2 | f32 | 4 | Minimum VL = 128 bits; 128/32 = 4 lanes; C1-ISA §2.1 |
| SVE2 | f64 | 2 | 128/64 = 2 |
| SVE2 | i32 | 4 | 128/32 = 4 |
| SVE2 | i8 | 16 | 128/8 = 16 |
| RVV | f32 | 4 | Minimum VLEN = 128 bits; at LMUL=1: 128/32 = 4 lanes; C1-ISA §2.2 §6 |
| RVV | f64 | 2 | 128/64 = 2 |
| RVV | i32 | 4 | 128/32 = 4 |
| NEON | — | n/a | ScalableVec not valid on NEON; use FixedVec<T,4> |

Note: LMUL is a backend MIR pass decision, never user-facing (locked decision #3 per task
brief). The user sees only `ScalableVec<T>` and `min_lanes()`.

### §4.3 Strip-Mining Contract

The canonical pattern for a `ScalableVec<T>` loop:

```
# Correct: runtime stride via v.lanes()
fn scale_add(a: *f32, b: *f32, n: usize, c: f32):
    var i = 0usize
    val sv = ScalableVec<f32>::splat(0.0)
    while i < n:
        val v = ScalableVec<f32>::load_unaligned(a + i)
        val u = ScalableVec<f32>::load_unaligned(b + i)
        val r = v.fma(sv.splat(c), u)
        r.store_unaligned(a + i)
        i += sv.lanes()       # ← correct: runtime stride
```

If the user writes a hardcoded constant stride:

```
    i += 4    # ← wrong: hardcoded stride
```

The backend emits `W_SIMD_HARDCODED_STRIDE` when it detects the loop body contains a
`ScalableVec<T>` load/store but the induction increment is a compile-time constant.
Detection pass: `60.mir_opt/predicate_promote.spl` (augmented for stride detection).

### §4.4 `from_fixed` and `try_to_fixed`

**`from_fixed<const N>(v: FixedVec<T,N>) -> ScalableVec<T>`**:
- Allowed only if `N <= min_lanes()` for the target at compile time.
- If `N > min_lanes()`: emits `E_SIMD_FIXED_OVERFLOWS_SCALABLE`.
- Rationale: a fixed-width vector wider than the guaranteed minimum scalable lane count
  cannot be safely broadcast into a scalable register without knowing the runtime VL.

Example:
```
# On SVE2 (min_lanes for f32 = 4):
val fv4: FixedVec<f32, 4> = FixedVec<f32, 4>::splat(1.0)
val sv = ScalableVec<f32>::from_fixed(fv4)   # OK: N=4 == min_lanes()

val fv8: FixedVec<f32, 8> = FixedVec<f32, 8>::splat(1.0)
val sv2 = ScalableVec<f32>::from_fixed(fv8)  # ERROR: E_SIMD_FIXED_OVERFLOWS_SCALABLE(N=8 > min_lanes=4)
```

**`try_to_fixed<const N>() -> Option<FixedVec<T,N>>`**:
- Runtime check: if `self.lanes() == N`, returns `Some(fixed_vec)`.
- Otherwise returns `None`.
- No error emitted; caller must handle the `None` case.

### §4.5 PTX/CUDA: No `ScalableVec`

All `ScalableVec<T>` methods emit `E_SIMD_PTX_NO_SCALABLE` when the compile target is
PTX or CUDA. PTX has no concept of scalable vector length. C1-DEEP §3.1 (PTX execution
model) confirms: warp = 32 threads, each executing scalar; no `vsetvli` equivalent.

---

## §5 Mask Semantics — Full Table

### §5.1 Construction Methods (see §1.4 for signatures)

**`Mask::from_bits(bits: u64)`** — construct from bitmask.
- Bit `i` of `bits` → lane `i` active.
- For `FixedVec<T,N>`: bits N–63 are ignored.
- For `ScalableVec<T>`: only the low `lanes()` bits are used; excess bits raise `W_SIMD_MASK_BITS_OOB`.

**`Mask::all_ones()` / `Mask::all_zeros()`** — trivial; used for unconditional / masked-out ops.

**`Mask::from_cmp(cmp_result)`** — identity; the comparison methods already return `Self.Mask`.
This constructor is for cases where a mask is produced by one expression and consumed by another.

### §5.2 Mask Operations

All logical ops (`and`, `or`, `xor`, `not`, `andnot`) are element-wise on the mask bits.
On AVX-512: lower to `kandw/korw/kxorw/knotw/kandnw` instructions (k1–k7 only, k0 is
all-ones sentinel per B2 §4.4).
On SVE2: lower to `pand/por/peor/not/bic` predicate ops (C1-ISA §2.1).
On RVV: lower to `vmand.mm/vmor.mm/vmxor.mm/vmnot.m` (C1-ISA §2.2 §5); result always
lives in a v-register; must `vmv1r.v v0, vX` before using as mask (C1-DEEP §6-J).
On SSE/NEON: materialize as vector and use bitwise ops (see §5.4 materialization table).

### §5.3 Predication Model: `_z` vs `_x` vs `_m`

Only `_z` (zero-fill on inactive lanes) is user-visible (locked decision #4).

- **`_z` (zero-fill)**: inactive lanes get 0. Default for all user-facing masked ops.
- **`_x` (undefined/poison)**: inactive lanes hold undefined values. Backend choice.
  Emitted when liveness analysis proves inactive lane values are never read.
  The `60.mir_opt/predicate_promote.spl` pass promotes `_z` → `_x` when safe.
- **`_m` (merge/preserve)**: inactive lanes preserve the destination register value.
  Backend choice for operations where the destination value is live.

When `predicate_promote.spl` identifies a `_x` opportunity, it emits
`W_SIMD_PRED_PROMOTE_HINT` (informational; helps users understand when to use `@simd`
annotation or restructure loops for better codegen).

### §5.4 Mask Materialization Decision Table

| Target | Mask type | Materialization | Notes |
|--------|----------|-----------------|-------|
| x86-64 AVX-512 | `Mask<FixedVec<T,N>>` | k-register (k1–k7) | k0 = all-ones sentinel; unallocatable; B2 §4.4, C1-ISA §1.4 |
| x86-64 AVX2 | `Mask<FixedVec<T,N>>` | YMM vector (top-bit-per-lane) | `VCMPPS` → YMM; `VBLENDVPS` for select |
| x86-64 SSE2/SSE4 | `Mask<FixedVec<T,N>>` | XMM vector (sign-bit-per-lane) | `CMPEQPS` → XMM; `BLENDVPS` (SSE4.1) or `ANDPS+ANDNPS+ORPS` (SSE2) |
| ARM NEON | `Mask<FixedVec<T,N>>` | Q-register (all-ones per lane) | `VCMPEQ` → vector; `VBSL` for blend; C1-ISA §1.1 |
| ARM SVE2 | `Mask<ScalableVec<T>>` | P-register (bit per element) | P0–P15; p0 conventional for loop; C1-ISA §2.1 |
| RISC-V RVV | `Mask<ScalableVec<T>>` | v0 register (bit per element) | v0 is the ONLY mask source; computed masks in other v-regs need `vmv1r.v v0, vX`; C1-DEEP §6-J |
| PTX/CUDA | `Mask<WarpVec<T>>` | Predicate register (%p0–%p6) | `setp` + `@%p` conditional; no AVX-style k-reg |
| SPIR-V | `Mask<V>` | `OpTypeBool` per component | `OpCompositeConstruct` of bool vector; no dedicated k-reg |

---

## §6 `WarpVec<T>` Extension Trait — Full Method Specification

### §6.1 Shuffle Operations

All shuffle ops take a `mask: u32` parameter — the active warp mask. Per C1-DEEP §6-G:
the `mask` must include the calling thread's own lane bit. Backend enforces:

```
# invariant check (emitted by gpu_checker.spl):
assert (mask >> lane_id) & 1 == 1  # self-lane must be included
# else: E_WARP_SELF_EXCLUDED
```

PTX lowering: `shfl.sync.{up,down,bfly,idx}.b32 %dest, %src, %imm, %mask` (C1-ISA §3.1).
SPIR-V lowering: `OpGroupNonUniformShuffle{Up,Down,XorIndirect}` (KHR_shader_subgroup_basic).

### §6.2 Warp Reductions

`warp_reduce_sum` uses a shuffle-based binary tree reduction (log2(warp_size) steps).
PTX: `shfl.sync.bfly.b32` XOR-tree (standard pattern; C1-ISA §3.1).
SPIR-V: `OpGroupNonUniformFAdd(Subgroup, Reduce)` (C1-DEEP §5.1).

### §6.3 SubgroupSize Portability

Three runtime queries for portability across GPU targets:

| Query | PTX | SPIR-V Vulkan | AMD RDNA | Notes |
|-------|-----|--------------|----------|-------|
| `target_warp_size_const()` | 32 (compile const) | Specialization constant | wave_size (32 or 64) | Compile-time when deterministic |
| `target_warp_size_runtime()` | `warpSize` (always 32) | `gl_SubgroupSize` built-in | `gl_SubgroupSize` (32 or 64) | Runtime value |
| `subgroup_size_query()` | alias for above | alias for above | alias for above | Preferred name for SPIR-V |

AMD RDNA note: RDNA supports both wave32 and wave64 modes. `target_warp_size_runtime()`
returns the actual wave size at runtime. No architectural constant.

### §6.4 Apple M-Series Restriction

Per C1-DEEP §6-H: Apple M1/M2/M3/M4 support NEON but NOT SVE2 and have no documented
warp/subgroup model (AMX coprocessor is undocumented and not exposed as ISA). Any call to
any `WarpVec<T>` method when `target == apple-m-series` emits:

```
E_WARP_NO_APPLE_M
```

Fix-it: "Apple M-series does not support warp-scoped ops. Use FixedVec<T,4> with NEON
backend for fixed-width vectorization, or use a cross-platform compute framework."

Detection: `35.semantics/gpu_checker.spl` checks `SimdFeatureFlags.target_vendor == AppleM`.

---

## §7 Interpreter-Mode Parity

### §7.1 Policy

Per project memory `feedback_compile_mode_false_greens.md` and
`feedback_interpreter_test_limits.md`: interpreter-mode parity is REQUIRED for
correctness tests. All SIMD methods must have a scalar fallback that runs in the
interpreter. Performance tests must use compiled mode.

### §7.2 Scalar Fallback Rules

Every `Vector` trait method has an interpreter implementation as a pure-Simple scalar
loop over lanes:

| Method | Interpreter implementation | Performance |
|--------|--------------------------|------------|
| `add(a, b)` | `for i in 0..N: result[i] = a[i] + b[i]` | O(N) |
| `sub(a, b)` | element-wise subtraction | O(N) |
| `mul(a, b)` | element-wise multiplication | O(N) |
| `fma(a, b, c)` | `for i: result[i] = a[i]*b[i] + c[i]` | O(N) |
| `fnmadd(a, b, c)` | `for i: result[i] = -(a[i]*b[i]) + c[i]` | O(N) |
| `abs(a)` | element-wise `if a[i] < 0: -a[i] else a[i]` | O(N) |
| `neg(a)` | element-wise `-a[i]` | O(N) |
| `min(a, b)` | `for i: if a[i] < b[i]: a[i] else b[i]` | O(N) |
| `max(a, b)` | element-wise max | O(N) |
| `and/or/xor/andnot(a, b)` | element-wise bitwise op | O(N) |
| `shl/shr_logical/shr_arith` | element-wise shift | O(N) |
| `cmp_eq/lt/le/gt/ge/ne` | element-wise comparison → Mask | O(N) |
| `mask_select(m, t, f)` | `for i: if m[i]: t[i] else f[i]` | O(N) |
| `reduce_sum/min/max/and/or` | accumulate loop | O(N) |
| `shuffle(v, idx)` | `for i: result[i] = v[idx[i]]` | O(N) |
| `permute(v, ctrl)` | same as shuffle with const ctrl | O(N) |
| `broadcast_lane(v, lane)` | `for i: result[i] = v[lane]` | O(N) |
| `interleave_lo/hi` | element-wise interleave | O(N) |
| `load_aligned/unaligned` | element-wise load from ptr | O(N) |
| `store_aligned/unaligned` | element-wise store to ptr | O(N) |
| `gather(base, idx)` | `for i: result[i] = base[idx[i]]` | O(N) |
| `scatter(v, base, idx)` | `for i: base[idx[i]] = v[i]` | O(N) |
| `from_array/to_array` | element copy | O(N) |
| `splat(v)` | fill all lanes with v | O(N) |
| `cast<U>()` | element-wise numeric cast | O(N) |
| `Mask::from_bits/to_bits` | bit extract/pack loop | O(N) |
| `Mask::count_ones/any/all/none` | simple bit loop | O(N) |
| `ScalableVec::lanes()` | return fixed constant = min_lanes() | O(1) |

### §7.3 Compile-Only Methods (No Interpreter Implementation)

These methods emit `E_SIMD_COMPILE_ONLY` if reached in interpreter mode:

| Method | Reason |
|--------|--------|
| `Mask::ptx_preg_handle()` | PTX predicate register is a compile-time concept only |
| `WarpVec::shfl_*` | No warp concept in interpreter; scalar fallback would be wrong |
| `WarpVec::warp_reduce_*` | Requires warp execution context |
| `WarpVec::warp_ballot` | Vote requires warp execution model |
| `WarpVec::warp_active_mask` | No active mask concept in scalar interpreter |
| `WarpVec::warp_sync` | Barrier has no interpreter meaning |
| `FixedVec::preferred_lanes_for_target()` | OK in interp (returns const); not compile-only |

Note: `WarpVec` methods in the interpreter may optionally fall back to a single-thread
simulation (one "warp" of 1 thread) returning the self value for shuffles and
accumulate-0 for reductions. This simulation is valid for unit tests that check
call-correctness but not for any test that verifies shuffle semantics.

### §7.4 Interpreter Representation

In the interpreter, `FixedVec<T,N>` is stored as a `[T; N]` heap-allocated array of
boxed values. `ScalableVec<T>` is stored as a `[T; min_lanes()]` array (interpreter
uses the minimum lane count as the lane count). This is correct for correctness tests;
performance tests must use compiled mode.

---

## §8 Compile-Mode Lowering Pipeline — New MIR Opcodes

### §8.1 New MIR Opcode Types

These opcodes are added to `src/compiler/50.mir/mir_instructions.spl`:

```
# Splat
MirSimdSplat(dest: MirReg, val: MirReg, vec_type: MirType)

# Load / Store
MirSimdLoad(dest: MirReg, ptr: MirReg, aligned: bool, vec_type: MirType)
MirSimdStore(val: MirReg, ptr: MirReg, aligned: bool)

# Gather / Scatter
MirSimdGather(dest: MirReg, base: MirReg, indices: MirReg, vec_type: MirType)
MirSimdScatter(val: MirReg, base: MirReg, indices: MirReg)

# Binary ops
MirSimdBinop(dest: MirReg, lhs: MirReg, rhs: MirReg, op: SimdBinop)

enum SimdBinop:
    Add     # float + int
    Sub
    Mul
    Fma     # dest = lhs * rhs + third (uses MirSimdTernop below)
    Fnmadd
    Min
    Max
    And     # integer only
    Or      # integer only
    Xor     # integer only
    Andnot
    Shl
    ShrLogical
    ShrArith

# Ternary (FMA)
MirSimdTernop(dest: MirReg, a: MirReg, b: MirReg, c: MirReg, op: SimdTernop)

enum SimdTernop:
    Fma     # a*b + c
    Fnmadd  # -(a*b) + c

# Unary ops
MirSimdUnop(dest: MirReg, src: MirReg, op: SimdUnop)

enum SimdUnop:
    Neg
    Abs     # float only
    Not     # bitwise not; integer only
    Recip   # 1/x; float only; approximate
    Sqrt    # sqrt(x); float only

# Reductions → scalar
MirSimdReduce(dest: MirReg, src: MirReg, op: SimdReduce)

enum SimdReduce:
    Sum
    Min
    Max
    And
    Or

# Shuffle / permute
MirSimdShuffle(dest: MirReg, src: MirReg, indices: MirReg)
MirSimdPermute(dest: MirReg, src: MirReg, ctrl: MirConst)  # compile-time indices
MirSimdBroadcastLane(dest: MirReg, src: MirReg, lane: u32)
MirSimdInterleave(dest: MirReg, lhs: MirReg, rhs: MirReg, hi: bool)

# Comparison → Mask
MirSimdCmp(dest: MirReg, lhs: MirReg, rhs: MirReg, op: SimdCmpOp)

enum SimdCmpOp: Eq Ne Lt Le Gt Ge

# Mask → select
MirSimdSelect(dest: MirReg, mask: MirReg, t: MirReg, f: MirReg)

# Mask operations
MirSimdMaskOp(dest: MirReg, lhs: MirReg, rhs: MirReg, op: MaskBinop)

enum MaskBinop: And Or Xor Andnot Not  # Not uses lhs only; rhs is unused

# ScalableVec lane-length setup
MirSimdScalableVsetvl(dest_vl: MirReg, requested: MirReg, elem_type: MirType)
    # SVE2: no-op (predicate-driven, VL is implicit); returns svcnt*() result in dest_vl
    # RVV:  emits vsetvli dest_vl, requested, e{SEW}, m1, ta, ma

# Warp-specific opcodes (separate from MirSimd* to enforce trait separation)
MirWarpShfl(dest: MirReg, src: MirReg, delta: MirReg, mask: MirReg, op: WarpShflKind)

enum WarpShflKind: Up Down Xor Idx

MirWarpReduce(dest: MirReg, src: MirReg, mask: MirReg, op: WarpReduceOp)

enum WarpReduceOp: Sum Min Max Any All

MirWarpBallot(dest: MirReg, pred: MirReg, mask: MirReg)
MirWarpActivesMask(dest: MirReg)
MirWarpSync(mask: MirReg)
```

### §8.2 Type Annotation

All `MirSimd*` nodes carry `MirType` (for `FixedVec<T,N>` specialization) or
`MirTypeKind.ScalableVec(element, min_lanes)` (for `ScalableVec<T>`).

### §8.3 New MIR Optimization Passes

**`60.mir_opt/lmul_widen.spl`**: promotes RVV operations from LMUL=1 to LMUL=2/4/8
when profitable (wider ops reduce loop iterations). Decision: if the inner loop body
has no register-pressure conflict and the VLEN is known to be ≥ 256 bits, promote.

**`60.mir_opt/predicate_promote.spl`**: promotes `_z` (zero-fill) predication to `_x`
(undefined) when liveness analysis proves inactive lanes are dead. Also detects
`ScalableVec<T>` loops with hardcoded strides (§4.3) and emits `W_SIMD_HARDCODED_STRIDE`.

**`60.mir_opt/simd_split_unsupported.spl`**: implements the fallback chain from §3.2.
Splits `MirSimdBinop` on unsupported (T,N) pairs into multiple smaller ops.

### §8.4 Wiring in `50.mir/mir_lowering_expr.spl`

Currently (per C1-DEEP §2 internal state), `FixedVec::add` does NOT produce any
`MirSimd*` opcode — it resolves as a plain `Call` MIR node. The wiring must be added:

```
# In mir_lowering_expr.spl, MethodCall on FixedVec type:
case MethodCall(recv, "add", [rhs]) if is_simd_type(recv):
    emit MirSimdBinop(dest, lower(recv), lower(rhs), SimdBinop.Add)
```

This is the core change that makes the SIMD type system actually produce SIMD MIR.

### §8.5 `MirSimdScalableVsetvl` Lowering Specifics

- **SVE2 target**: `MirSimdScalableVsetvl` lowers to a call to `svcntw()` (or element-specific
  variant). No `vsetvli` instruction is emitted — SVE2 is predicate-driven and the vector
  length is implicit in the Z-register type. The dest_vl MirReg is set to the return of
  `svcnt*`. C1-ISA §2.1.
- **RVV target**: `MirSimdScalableVsetvl` lowers to `vsetvli dest_vl, requested, e{SEW}, m1, ta, ma`.
  LMUL may be promoted by `lmul_widen.spl` to m2/m4/m8 in a subsequent pass. C1-ISA §2.2 §6.

---

## §9 Diagnostic Catalog

**Table 9-A — Error Codes**

| Code | Phase | Trigger | Example Bad Source | Fix-it |
|------|-------|---------|-------------------|--------|
| `E_SIMD_BAD_LANES` | type-check | N not in {2,4,8,16,32,64} | `FixedVec<f32, 3>` | Use N ∈ {2,4,8,16,32,64} |
| `E_SIMD_TYPE_MISMATCH` | type-check | T not satisfying constraint (e.g. bool used for Numeric) | `FixedVec<bool, 4>` | Use a numeric type |
| `E_SIMD_FLOAT_ONLY` | type-check | Float-only method called on integer T | `FixedVec<i32,4>::fma(a,b,c)` | Use float type or different op |
| `E_SIMD_INT_ONLY` | type-check | Integer-only method called on float T | `FixedVec<f32,4>::and(a,b)` | Use integer type or bitcast |
| `E_SIMD_LANE_MISMATCH` | type-check | Mask and vector have different lane counts | `mask4.mask_select(v8, w8)` | Match lane counts |
| `E_SIMD_MASK_TYPE_MISMATCH` | type-check | Mask operations on incompatible Mask types | `Mask<FixedVec<f32,4>> and Mask<FixedVec<i32,4>>` | Use matching vector types |
| `E_SIMD_ARRAY_LEN_MISMATCH` | type-check | `from_array` array length != N | `FixedVec<f32,4>::from_array([1.0, 2.0])` | Pass array of length N |
| `E_SIMD_SLICE_TOO_SHORT` | type-check | `from_slice` slice shorter than N | slice of length 2 into FixedVec<f32,4> | Use slice of length >= N |
| `E_SIMD_SHIFT_OOB` | type-check | Shift count >= element bit width | `FixedVec<i32,4>::shl(v, 32)` | Use count < 32 for i32 |
| `E_SIMD_LANE_OOB` | type-check (constant) / runtime (interp) | Lane index >= lane count | `v.lane(8)` on `FixedVec<f32,4>` | Use index < 4 |
| `E_SIMD_TYPE_AMBIGUOUS` | type-check | `splat(0)` with no context | `val v = FixedVec<?, ?>: splat(0)` | Add type annotation |
| `E_SIMD_NO_LOWERING` | mono | No native or fallback lowering for (target, T, N) | `@simd(require_native) FixedVec<f64,16>` on SSE2 | Use `N = simd_lanes_preferred<T>()` |
| `E_SIMD_PTX_NO_SCALABLE` | mono | `ScalableVec<T>` used on PTX target | `ScalableVec<f32>` in CUDA kernel | Use `FixedVec<f32,N>` for PTX |
| `E_SIMD_FIXED_OVERFLOWS_SCALABLE` | type-check | `from_fixed(v)` with N > min_lanes() | `ScalableVec<f32>::from_fixed(fv8)` on SVE2 with min_lanes=4 | Use N <= 4 or load directly |
| `E_SIMD_MASK_BITS_OOB` | type-check | `from_bits(bits)` with bits beyond lane count | `Mask<FixedVec<f32,2>>::from_bits(0xFF)` | Mask bits to valid lane range |
| `E_SIMD_NO_WIDEN_TYPE` | type-check | `widen()` with no 2x-width type available | `FixedVec<i64,4>::widen()` (no i128) | Cannot widen i64 |
| `E_SIMD_NO_NARROW_TYPE` | type-check | `narrow()` with no half-width type available | `FixedVec<i8,4>::narrow()` (no i4) | Cannot narrow i8 |
| `E_SIMD_COMPILE_ONLY` | interp | Method called in interpreter that has no scalar fallback | `mask.ptx_preg_handle()` in test | Use compiled mode for this op |
| `E_SIMD_CONST_REQUIRED` | type-check | `permute(ctrl)` ctrl is not a compile-time const | `v.permute(runtime_idx)` | Use `shuffle()` for runtime indices |
| `E_WARP_NOT_IN_KERNEL` | semantics | `WarpVec` method called outside GPU kernel | `shfl_up(v, 1, 0xFFFFFFFF)` in CPU code | Move to kernel function |
| `E_WARP_NO_APPLE_M` | semantics | `WarpVec` method on Apple M-series target | any `WarpVec` call on apple-m | Use NEON FixedVec instead |
| `E_WARP_DELTA_OOB` | type-check | `shfl_up/down` delta >= warp_size | `shfl_down(v, 32, mask)` | Use delta < 32 |
| `E_WARP_SELF_EXCLUDED` | semantics | shfl mask does not include calling thread | `shfl_down(v, 1, 0)` | Set calling thread's bit in mask |
| `E_WARP_LANE_OOB` | type-check | `shfl_idx` src_lane >= warp_size | `shfl_idx(v, 32, mask)` | Use src_lane < warp_size |
| `E_WARP_SIZE_RUNTIME_ONLY` | type-check | `target_warp_size_const()` called on variable-size target | `target_warp_size_const()` on RDNA without known wave_size | Use `target_warp_size_runtime()` |

**Table 9-B — Warning Codes**

| Code | Phase | Trigger | Fix-it |
|------|-------|---------|--------|
| `W_SIMD_SCALAR_FALLBACK` | mir_opt | Split/fallback to scalar loop used | Use N matching target preferred lanes |
| `W_SIMD_NO_NATIVE_LOWERING` | mir_opt | Split into multiple sub-width ops | Use preferred-N or ScalableVec |
| `W_SIMD_HARDCODED_STRIDE` | mir_opt | `ScalableVec` loop with constant induction step | Use `v.lanes()` as stride |
| `W_SIMD_PRED_PROMOTE_HINT` | mir_opt | `_x` promotion opportunity detected by liveness | Informational; no action required |
| `W_SIMD_FIXED_EXCEEDS_MIN_LANES` | type-check | `to_scalable()` with N > min_lanes for target | Consider `from_fixed()` only when N <= min_lanes |
| `W_SIMD_MASK_BITS_OOB` | type-check | `from_bits` for ScalableVec with bits beyond runtime lanes | Truncate bits to runtime lane count |
| `W_WARP_SYNC_EMPTY_MASK` | semantics | `warp_sync(0)` called with empty mask | Use active warp mask |
| `W_SIMD_FP16_AUTOPROMOTE` | type-check | `FixedVec<f16,N>` on target without native FP16 | Promote to f32 explicitly; performance may differ |

---

## §10 Frontend Syntax Surface

### §10.1 Vector Literal Syntax

**FixedVec literal**: `[expr; lanes N]` where N must be a compile-time constant.

```
val v: FixedVec<f32, 4> = [1.0f32; lanes 4]    # all-ones splat
val w: FixedVec<f32, 4> = [1.0f32, 2.0f32, 3.0f32, 4.0f32; lanes 4]  # per-lane init
```

The `lanes` keyword is a disambiguator to avoid conflict with existing `[expr; N]`
array syntax. Parser rule: `[` ... `; lanes` `<int>` `]` → `FixedVec` literal node.
This does NOT conflict with `[expr; N]` (array repeat) because `lanes` is a reserved
contextual keyword in this position (not a general identifier ban).

Per project memory `feedback_struct_literal_brace_syntax.md`: the parser must handle
`FixedVec<f32, 4> { ... }` struct-literal syntax. To avoid ambiguity, SIMD vector
literals use `[...]` bracket syntax rather than brace syntax. The brace form
`FixedVec<f32,4> { data: [...] }` is also accepted for the internal struct field but
is not the recommended user-facing form.

**ScalableVec construction**: No literal syntax. Use constructor methods:

```
val sv = ScalableVec<f32>::splat(1.0f32)    # runtime N
val sv2 = ScalableVec<f32>::splat_n(1.0f32, n=v.lanes())
```

### §10.2 Lane Indexing

`v.lane(i)` is the canonical form for single-lane read. `v[i]` is accepted as sugar
for `v.lane(i)` when `v`'s static type is `FixedVec<T,N>` or `ScalableVec<T>`.

There is no `v[i]` ambiguity with array indexing because the type system resolves which
`[]` overload to use. If `v` is a `FixedVec<T,N>`, `v[i]` lowers to `v.lane(i)`.
Write is: `v[i] = x` → `v.set_lane(i, x)`.

### §10.3 `into_simd` Spread Syntax

```
val v = [1.0f32, 2.0f32, 3.0f32, 4.0f32].into_simd::<FixedVec<f32, 4>>()
```

This is implemented as a method on `[T]` array that calls `FixedVec<T,N>::from_array()`.
No new grammar production needed — this is a trait method call using the existing
`::<TypeParam>` turbofish-style syntax (already in the Simple parser).

### §10.4 Pattern Matching on `Mask`

Pattern matching on a `Mask<V>` is **not supported** in this design. Masks are opaque
at the language level. Use `.any()`, `.all()`, `.none()`, `.count_ones()`, or
`.lane_active(i)` for queries.

```
# Not allowed:
match mask:
    case Mask::all_ones(): ...  # rejected; use mask.all() == true

# Allowed:
if mask.all():
    ...
if mask.any():
    ...
```

This avoids the ambiguity of what "pattern matching on a mask" should bind to (the bits?
the lanes? the backing register?).

### §10.5 Interaction with Round-1 Grammar Reservation

Round-1 `simd_unified_architecture.md` reserved the following syntax forms. This section
confirms compatibility:

- `FixedVec<T, N>` — no conflict with existing generics syntax.
- `ScalableVec<T>` — no conflict.
- `[expr; lanes N]` — new production; `lanes` is context-keyword (only reserved after `;`
  inside `[...]`; does not shadow other uses of `lanes` as an identifier elsewhere).
- `v.lane(i)` — method call, no parser change needed.
- `v[i]` on SIMD type — resolved via type-directed desugaring, no grammar change.

---

## §11 Standard Library Landing Zone

### §11.1 Path

Per `.claude/rules/structure.md`: `src/lib/nogc_sync_mut/` is "Sync mutable
(ffi, fs, net, http, database, mcp, spec)". SIMD is a sync, no-GC, mutable operation
and fits this category. The SIMD landing zone is:

```
src/lib/nogc_sync_mut/simd/
```

### §11.2 File Layout

```
src/lib/nogc_sync_mut/simd/
├── mod.spl          # re-exports: FixedVec, ScalableVec, Vector, Mask, WarpVec, simd_lanes_preferred
├── vector.spl       # Vector trait definition (§1.1)
├── fixed.spl        # FixedVec<T,N> class + impl (§1.2)
├── scalable.spl     # ScalableVec<T> class + impl (§1.3, §4)
├── mask.spl         # Mask<V> trait + impl (§1.4, §5)
├── warp.spl         # WarpVec<T> trait + impl (§1.5, §6)
├── platform.spl     # SimdFeatureFlags, simd_lanes_preferred, target detection
│                    # supersedes src/compiler/30.types/simd_platform.spl (migration path: keep old file, re-export from new location)
├── aliases.spl      # back-compat type aliases (see §11.3)
└── intrinsics.spl   # INTERNAL — not re-exported by mod.spl; one fn per MIR opcode
```

**`mod.spl`** re-exports for public API:

```
use std.simd.vector :: Vector
use std.simd.fixed :: FixedVec
use std.simd.scalable :: ScalableVec
use std.simd.mask :: Mask
use std.simd.warp :: WarpVec
use std.simd.platform :: simd_lanes_preferred, SimdFeatureFlags
use std.simd.aliases :: Vec2f, Vec4f, Vec8f, Vec4d, Vec2d, Vec4i, Vec8i
```

### §11.3 `aliases.spl` — Back-Compat Aliases

```
type Vec2f  = FixedVec<f32, 2>
type Vec4f  = FixedVec<f32, 4>
type Vec8f  = FixedVec<f32, 8>
type Vec16f = FixedVec<f32, 16>
type Vec2d  = FixedVec<f64, 2>
type Vec4d  = FixedVec<f64, 4>
type Vec8d  = FixedVec<f64, 8>
type Vec4i  = FixedVec<i32, 4>
type Vec8i  = FixedVec<i32, 8>
type Vec16i = FixedVec<i32, 16>
type Vec4u  = FixedVec<u32, 4>
type Vec8u  = FixedVec<u32, 8>
```

Existing code using `Vec4f`, `Vec8f` etc. (from `30.types/simd.spl`) will resolve to
the new parameterized types after the migration. The concrete struct fields (`x`, `y`,
`z`, `w`) in the old types do NOT carry over — use `.lane(0)`, `.lane(1)` etc. or
destructure via `to_array()`.

### §11.4 `intrinsics.spl` — Internal Mapping

One entry per MIR opcode (§8.1). Not public. Example:

```
# @internal — do not use directly; use Vector trait methods
extern fn __simd_splat_f32x4(val: f32) -> FixedVec<f32, 4>          # → MirSimdSplat
extern fn __simd_add_f32x4(a: FixedVec<f32,4>, b: FixedVec<f32,4>) -> FixedVec<f32,4>  # → MirSimdBinop(Add)
# ... one entry per (op, T, N) combo
```

These are `@internal` fns recognized by `simd_lowering.spl` by name-prefix `__simd_`.
This is the bridge between the trait method dispatch and the existing name-match
lowering in `60.mir_opt/simd_lowering.spl:93–149`.

---

## §12 Open Architectural Questions

**OQ-A: f16/bf16 type existence in Simple's type system (R2-new)**
FP16 and BF16 instructions are confirmed on AVX-512-FP16 (Intel Sapphire Rapids),
ARM NEON (bf16 extension), and NVIDIA PTX (`.f16`). Whether Simple has `f16` and `bf16`
as first-class scalar types is not confirmed. If they do not exist, `FixedVec<f16,N>`
cannot be typed. Resolution path: file a feature request for `f16`/`bf16` primitive
types; use `FixedVec<f32,N>` with `widen()`/`narrow()` as interim; emit
`W_SIMD_FP16_AUTOPROMOTE` on attempted `FixedVec<f16,N>` use.

**OQ-B: `Mask<FixedVec<f32,4>>` vs `Mask<FixedVec<i32,4>>` — shared backing repr on AVX-512 (R2-new)**
Both types have 4 lanes and lower to the same k-register width (k-reg is 4 bits for
32-bit ops, 4 bits regardless of element type on most ops). C3 may wish to share a
physical k-register between `Mask<FixedVec<f32,4>>` and `Mask<FixedVec<i32,4>>`. The
type system keeps them distinct (§2.3), but the register allocator may coalesce them.
Resolution: C3 decides; document as a C3 decision and add a note in `mask.spl` that
the physical backing is target-dependent.

**OQ-C: `from_fixed` across element widths (R2-new)**
Is `ScalableVec<f32>::from_fixed(FixedVec<i32,4>)` allowed (cross-element-width) or
only same-T? Current design (§4.4) requires same T. But there are valid use cases
(reinterpret a bitfield as float). Resolution: keep same-T restriction; add a
separate `reinterpret_cast` method with explicit documentation of undefined behavior
risk if element widths differ.

**OQ-D: Monomorphization cap enforcement mechanism (continued from B1 §9 OQ-3)**
The cap N ∈ {2,4,8,16,32,64} (6 values) and T ∈ {u8,u16,u32,u64,i8,i16,i32,i64,f32,f64}
(10 types) gives 10 × 6 = 60 (T,N) combinations per target. Across the 6 supported
backend targets (SSE2, AVX2, AVX-512, NEON, SVE2, RVV) plus the scalar fallback,
the theoretical maximum is 60 × 7 = 420 specializations. In practice fewer exist
because not every (T,N) has a meaningful lowering per target (many fall back to the
scalar path). Nonetheless the compiler must not eagerly generate all 420; use
demand-driven specialization in `40.mono/instantiation.spl` — only emit a
specialization when a concrete call site is found. Do not pre-generate the full matrix.

**OQ-E: Strip-mining detection reliability (R2-new)**
`W_SIMD_HARDCODED_STRIDE` detection in §4.3 requires the MIR opt pass to identify
`ScalableVec<T>` loop induction increments. This requires the `ScalableVec` type to be
preserved through the MIR optimization pipeline (not erased to a scalar loop before
the pass runs). Resolution: ensure `MirSimdScalableVsetvl` is emitted BEFORE the
`predicate_promote.spl` pass runs and is not optimized away prematurely.

**OQ-F: `warp_active_mask` on SPIR-V (R2-new)**
PTX `activemask.b32` has no direct SPIR-V equivalent. `gl_SubgroupEqMask` + bitwise ops
can approximate it, but `gl_SubgroupActiveMask` (Vulkan 1.3 / VK_EXT_shader_subgroup_uniform_control_flow)
is the closest match. The exact lowering rule is not yet specified. Resolution: map
`warp_active_mask()` to `OpLoad %SubgroupEqMask` OR require
`VK_EXT_shader_subgroup_uniform_control_flow`; document the extension requirement in
`warp.spl`.

**OQ-G: ScalableVec iterator semantics (R2-new)**
The `iter()` method on `ScalableVec<T>` yields elements but the lane count is runtime.
`LaneIter<T>` must be a dynamically-sized iterator. The interaction with Simple's
for-loop desugaring (which may need a `len()` or `next()` protocol) is not yet
specified. Resolution: `ScalableVec::iter()` returns a `ScalableLaneIter<T>` that
holds a runtime index; the for-loop desugaring uses `while i < iter.len()` form rather
than an exact iterator.

---

*Document generated by Wave C2 (Round-2 deep-detail unified architecture). C3's
`simd_backend_strict_emit_detail.md` covers encoder bytes, ABI registers, and
golden fixtures. C4's rollout plan v2 covers milestone phasing and test budgets.*
