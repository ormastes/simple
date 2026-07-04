# Research: SIMD ISA Survey (2026-05-02)

**TL;DR.** The Simple compiler must lower a single abstract vector IR to seven target ISAs spanning four fundamentally different paradigms: fixed-width CPU SIMD (NEON/SSE/AVX/AVX-512), scalable CPU SIMD (SVE2/RVV), GPU implicit-SIMD (PTX/SPIR-V). The primary design tension is mask/predicate representation: AVX-512 uses dedicated k-registers (k0–k7), SVE2 uses dedicated p-registers (p0–p15) with three predication modes (x/z/m), RVV reuses the v0 data register as the single allowed mask source, and NEON has no mask registers at all (blend via sign-bit-wide BSL). A first-class `Mask<N>` type in the IR is the right choice but must be lowered differently per target; this document provides the per-ISA evidence. The cross-ISA op coverage matrix in §4 shows which abstract ops are native vs. synthesized on each backend and is the primary input for Wave B's interface design.

---

## Table of Contents

1. [Fixed-Width SIMD](#1-fixed-width-simd)
   - 1.1 [ARM NEON / AArch64 Advanced SIMD](#11-arm-neon--aarch64-advanced-simd)
   - 1.2 [x86 SSE/SSE2/SSE4](#12-x86-ssesse2sse4-128-bit-xmm)
   - 1.3 [x86 AVX/AVX2](#13-x86-avxavx2-256-bit-ymm)
   - 1.4 [x86 AVX-512](#14-x86-avx-512-512-bit-zmm--k-mask-registers)
2. [Scalable SIMD](#2-scalable-simd)
   - 2.1 [ARM SVE2](#21-arm-sve2)
   - 2.2 [RISC-V Vector Extension 1.0](#22-risc-v-vector-extension-10)
   - 2.3 [Scalable ISA Comparison](#23-scalable-isa-comparison)
3. [GPU Vector Model](#3-gpu-vector-model)
   - 3.1 [NVIDIA PTX / CUDA](#31-nvidia-ptx--cuda)
   - 3.2 [SPIR-V Vulkan](#32-spir-v-vulkan)
   - 3.3 [Warp-as-vector vs CPU SIMD](#33-warp-as-vector-vs-cpu-simd-abstraction-leaks)
4. [Cross-ISA Op Coverage Matrix](#4-cross-isa-op-coverage-matrix)
5. [Predication Model Recommendations](#5-predication-model-recommendations)
6. [vscale/LMUL Handling](#6-vscalelmu-handling)

---

## 1. Fixed-Width SIMD

### 1.1 ARM NEON / AArch64 Advanced SIMD

**Source:** ARM ACLE §9 "Advanced SIMD (Neon) intrinsics" (arm-software.github.io/acle/main/acle.html)

#### Register File

- 32 × 128-bit Q-registers (Q0–Q31) in AArch64 Advanced SIMD.
- Each Q-register aliases two 64-bit D-registers, four 32-bit S-registers, eight 16-bit H-registers, sixteen 8-bit B-registers.
- No mask registers. No dedicated predicate registers.

#### Supported Lane Types (ACLE §9.1)

| Type family     | Lane width (bits) | Lanes per Q-reg | Intrinsic suffix examples            |
|-----------------|-------------------|-----------------|--------------------------------------|
| int8 / uint8    | 8                 | 16              | `int8x16_t`, `uint8x16_t`            |
| int16 / uint16  | 16                | 8               | `int16x8_t`, `uint16x8_t`            |
| int32 / uint32  | 32                | 4               | `int32x4_t`, `uint32x4_t`            |
| int64 / uint64  | 64                | 2               | `int64x2_t`, `uint64x2_t`            |
| float16         | 16                | 8               | `float16x8_t` (requires `__fp16`)    |
| bfloat16        | 16                | 8               | `bfloat16x8_t` (Armv8.6-A)          |
| float32         | 32                | 4               | `float32x4_t`                        |
| float64         | 64                | 2               | `float64x2_t` (AArch64 only)         |
| poly8 / poly16  | 8/16              | 16/8            | Cryptographic operations             |
| mfloat8         | 8                 | 16              | FP8 (opaque, intrinsic-only)         |

#### Key Operations

| Category      | Representative Intrinsics                              | Notes                                   |
|---------------|--------------------------------------------------------|-----------------------------------------|
| Load          | `vld1q_f32`, `vld2q_f32` (interleaved 2-struct)       | Unit-stride; no gather                  |
| Store         | `vst1q_f32`, `vst2q_f32`                               | Unit-stride; no scatter                 |
| Add           | `vaddq_s32`, `vaddq_f32`                               | All integer widths + f16/f32/f64        |
| Multiply      | `vmulq_s32`, `vmulq_f32`                               | No int64 multiply lane-widening direct  |
| FMA           | `vfmaq_f32`, `vfmaq_lane_f32`                          | Fused; lane-indexed broadcast form      |
| Widening mul  | `vmull_s16` → `int32x4_t`                              | 64-bit → 128-bit widening               |
| Compare       | `vcgtq_s32` → `uint32x4_t`                             | Returns all-ones/all-zeros mask lanes   |
| Select/Blend  | `vbslq_u32(mask, a, b)`                                | BSL = bitwise select; no k-reg          |
| Permute       | `vzip1q_f32`, `vuzp1q_f32`, `vtrnq_f32`               | Fixed deinterleave/zip/transpose        |
| Shuffle       | `vqtbl1q_u8(tbl, idx)` (table lookup)                  | Byte shuffle via VTBL; no cross-lane fp |
| Reduce        | `vaddvq_s32`, `vmaxvq_f32`                             | Horizontal add/min/max (AArch64)        |
| Saturate      | `vqaddq_s16`, `vqsubq_s16`                             | Signed/unsigned saturating              |
| Shift         | `vshlq_s32`, `vshrq_n_s32`                             | Logical/arithmetic; immediate or vector |
| Dot product   | `vdotq_s32` (Armv8.2+)                                 | 4×i8 → i32 per lane                    |

#### Mask Model

NEON has **no dedicated mask register**. Comparison instructions produce a vector of all-ones (0xFFFF…) or all-zeros per lane. Conditional selection uses:
- `vbslq_uN(mask, a, b)` — bitwise select (BSL instruction): selects `a` where mask bit is 1, `b` where 0.
- Masking is synthesized: generate a condition vector, then BSL. This costs one extra register and one extra instruction per masked op.
- No horizontal predicate (no "how many lanes are active" query without additional reduction).

---

### 1.2 x86 SSE/SSE2/SSE4 (128-bit XMM)

**Source:** Intel Intrinsics Guide (intel.com/content/www/us/en/docs/intrinsics-guide/); SSE2 ratified in Intel Architecture Software Developer's Manual Vol. 1 §5.

#### Register File

- 16 × 128-bit XMM registers (XMM0–XMM15; extended from 8 in 32-bit mode).
- No mask registers.

#### Supported Lane Types

| Width  | Element types              | SSE Generation   |
|--------|----------------------------|------------------|
| 128b   | i8×16, i16×8, i32×4, i64×2 | SSE2             |
| 128b   | f32×4                       | SSE (Katmai)     |
| 128b   | f64×2                       | SSE2             |
| 128b   | i8×16 dot, min, max        | SSE4.1           |

#### Key Operations

| Category        | Intrinsic / Mnemonic                            | Notes                                    |
|-----------------|-------------------------------------------------|------------------------------------------|
| Load            | `_mm_load_ps`, `_mm_loadu_ps`                   | Aligned / unaligned                      |
| Store           | `_mm_store_ps`, `_mm_storeu_ps`                 |                                          |
| Add             | `_mm_add_epi32`, `_mm_add_ps`                   | All widths                               |
| Multiply        | `_mm_mul_ps`, `_mm_mullo_epi32` (SSE4.1)        | fp native; i32 mullo added in SSE4.1     |
| FMA             | No native FMA in base SSE; requires FMA3/4 ext  | Separate FMA3 ISA extension (Haswell+)   |
| Compare         | `_mm_cmpeq_epi32` → mask vector                 | Produces lane-wide mask vector           |
| Select/Blend    | `_mm_blendv_ps` (SSE4.1), `_mm_and_ps`+`_mm_or_ps` | SSE4.1 blendv; older = AND+ANDNOT+OR |
| Shuffle         | `_mm_shuffle_ps` (imm8 control), `_mm_shuffle_epi8` (SSSE3) | Cross-lane with imm8 selector |
| Permute         | `_mm_unpacklo_ps`, `_mm_unpackhi_ps`            | Interleave low/high halves               |
| Reduce (hadd)   | `_mm_hadd_ps` (SSSE3)                           | Adjacent-pair horizontal add             |
| Reduce (full)   | Not native; requires multi-step hadd            | ~4 instructions for sum of 4 f32         |
| Gather          | Not available in SSE; requires AVX2             | Must scalar loop                         |
| Scatter         | Not available until AVX-512                     | Must scalar loop                         |

#### Mask Model

No mask registers. Comparisons return a full-width vector of 0x00…00 or 0xFF…FF per lane. Blending via `_mm_blendv_ps` (SSE4.1) uses the high bit of each lane as a selector; older code uses AND+ANDNOT+OR. No compressed-store or masked-load in base SSE.

---

### 1.3 x86 AVX/AVX2 (256-bit YMM)

**Source:** Intel Architecture Software Developer's Manual, Vol. 1 §14–15.

#### Register File

- 16 × 256-bit YMM registers (YMM0–YMM15); lower 128 bits alias XMM.
- No mask registers (introduced in AVX-512).
- AVX: floating-point only in 256-bit; integer 256-bit added in AVX2.

#### Supported Lane Types

| Width  | Element types                    | AVX Generation |
|--------|----------------------------------|----------------|
| 256b   | f32×8, f64×4                     | AVX            |
| 256b   | i8×32, i16×16, i32×8, i64×4     | AVX2           |

#### Key Operations

| Category      | Intrinsic / Mnemonic                                     | Notes                                           |
|---------------|----------------------------------------------------------|-------------------------------------------------|
| Load          | `_mm256_load_ps`, `_mm256_loadu_ps`                      | 32-byte align required for aligned form         |
| Gather        | `_mm256_i32gather_ps` (AVX2)                             | Native 32-bit indexed gather; first on x86      |
| Scatter       | Not available; requires AVX-512                          | Emulate with scalar loop                        |
| Add           | `_mm256_add_ps`, `_mm256_add_epi32`                      |                                                 |
| Multiply      | `_mm256_mul_ps`, `_mm256_mullo_epi32`                    |                                                 |
| FMA           | `_mm256_fmadd_ps` (FMA3 extension, Haswell+)             | Fused; fused-multiply-accumulate                |
| Permute       | `_mm256_permutevar8x32_ps` (AVX2)                        | Full cross-lane 32-bit permute with vector ctrl |
| Shuffle       | `_mm256_shuffle_epi8` operates within 128-bit lanes only | Cross-128-bit-lane shuffle requires vperm2i128  |
| Blend         | `_mm256_blendv_ps`, `_mm256_blend_ps` (imm8)             |                                                 |
| Reduce        | No native; must use hadd + extract + hadd sequence       | 4–8 instructions for f32 tree-reduce            |
| Broadcast     | `_mm256_broadcast_ss`, `_mm256_broadcastd_epi32`         | Scalar → all lanes                              |

**Critical limitation:** AVX2 256-bit integer shuffle (`_mm256_shuffle_epi8`) is limited to within each 128-bit half. Cross-lane byte shuffles require `vperm2i128` (128-bit granularity) followed by a second shuffle. This is a significant difference from NEON/SVE2.

---

### 1.4 x86 AVX-512 (512-bit ZMM + k-mask registers)

**Source:** Intel Architecture Software Developer's Manual; AVX-512 is a family of extensions. Foundation (AVX-512F) is the base; significant subsets:
- **AVX-512F** — foundation: 512-bit ops, ZMM regs, k-mask regs
- **AVX-512BW** — byte/word (i8, i16) operations
- **AVX-512DQ** — dword/qword (i32, i64) bit ops, f64 packed ops
- **AVX-512VL** — 128/256-bit ZMM variants with k-masks
- **AVX-512CD** — conflict detection
- **AVX-512VBMI** — byte manipulation (permute2)

Not all x86-64 targets have all subsets: Skylake-SP has F/CD/BW/DQ/VL; many embedded/consumer parts lack BW/DQ.

#### Register File

- 32 × 512-bit ZMM registers (ZMM0–ZMM31).
- 8 × 64-bit k-mask registers (k0–k7). **k0 is hardwired all-ones** (no-mask / unconditional).
- k-registers hold one bit per 8-bit lane (i8 mode) up to one bit per 64-bit lane.

#### Key Operations

| Category        | Intrinsic / Mnemonic                                    | Notes                                              |
|-----------------|---------------------------------------------------------|----------------------------------------------------|
| Load (masked)   | `_mm512_mask_load_ps(src, k, ptr)`                      | Merge into `src` where k-bit=0                     |
| Store (masked)  | `_mm512_mask_store_ps(ptr, k, a)`                       | Only writes lanes where k-bit=1                    |
| Gather          | `_mm512_i32gather_ps(idx, base, scale)`                 | 32-bit indexed; no k-reg needed but masked form exists |
| Scatter         | `_mm512_i32scatter_ps(base, idx, a, scale)`             | First native scatter on x86                        |
| Add (masked)    | `_mm512_mask_add_ps(src, k, a, b)`                      | Merge; `_mm512_maskz_add_ps` = zero-mask           |
| FMA (masked)    | `_mm512_mask_fmadd_ps(a, k, b, c)`                      |                                                    |
| Permute         | `_mm512_permutexvar_ps(idx, a)` (F)                     | Full 512-bit cross-lane permute                    |
| Compress        | `_mm512_mask_compress_ps(src, k, a)`                    | Pack active lanes to low positions (no SVE equiv)  |
| Expand          | `_mm512_mask_expand_ps(src, k, a)`                      | Scatter active to mask-selected positions          |
| Reduce          | `_mm512_reduce_add_ps`, `_mm512_reduce_max_ps`          | Hardware tree reduction                            |
| CMP → k-reg    | `_mm512_cmp_ps_mask(a, b, pred)` → `__mmask16`         | Produces k-register directly                       |
| k-reg ops       | `_kand_mask16`, `_kor_mask16`, `_knot_mask16`           | Boolean algebra on k-registers                    |

#### Mask Model (k-registers)

AVX-512 k-mask registers are a **separate register file** (k0–k7). Each bit corresponds to one vector lane. k0 = all-ones always. Operations come in three forms:
- **Unmasked:** `_mm512_add_ps(a, b)` — no k-reg used.
- **Merge-masked:** `_mm512_mask_add_ps(src, k, a, b)` — inactive lanes copy from `src`.
- **Zero-masked:** `_mm512_maskz_add_ps(k, a, b)` — inactive lanes become 0.

k-registers can be populated from comparison results (`_mm512_cmp_ps_mask`) or from integer loads/stores. They support Boolean ops directly. The architecture allows predicated execution without a synthetic blend; this is the most expressive fixed-width mask system available.

---

## 2. Scalable SIMD

### 2.1 ARM SVE2

**Source:** ARM ACLE §11 "SVE language extensions and intrinsics" (arm-software.github.io/acle/main/acle.html); ARM SVE2 ISA reference.

#### Architecture Overview

SVE2 (Scalable Vector Extension 2, AArch64 optional feature, Armv9-A required) extends SVE with:
- Polynomial and complex operations
- Table lookups (HISTCNT, MATCH, NMATCH)
- Additional widening/narrowing integer operations
- SME (Streaming SVE) matrix extensions (ZA tile register)

The defining property: **vector length (VL) is implementation-defined** and known only at runtime. ACLE expresses this via the type attribute `arm_sve_vector_bits(N)` for fixed-length SVE, or via VL-agnostic code when `__ARM_FEATURE_SVE_BITS` is zero or not set.

#### Register File

- 32 × VL-bit Z-registers (Z0–Z31). VL ∈ {128, 256, 512, 1024, 2048} bits in multiples of 128.
- 16 × (VL/8)-bit P-registers (P0–P15) — predicate registers, one bit per byte lane.
- **Governing predicate:** any P-register can be the governing predicate for an operation; p0 has no special hardware status but is conventional for loop predicates.
- FFR (First Fault Register): special predicate updated by first-fault loads.
- ZA tile register (SME): optional matrix storage used for cooperative matrix operations.

#### ACLE Naming Convention (ACLE §11.2)

SVE intrinsics follow the pattern:

```
sv<op>_<type>[_<modifier>](svbool_t pg, ...)
```

The **predication suffix** on the intrinsic name describes treatment of inactive elements:

- **`_x` (don't-care):** Inactive elements have unknown values. Cheapest: the hardware may reuse any existing register contents. Can leak data; use only when inactive result lanes are guaranteed not to be read. Maps to `Pg/Z` in assembly but the inactive lane values are unspecified.
- **`_z` (zero predication):** All inactive result elements are set to zero. Maps to `Pg/Z` in assembly with explicit zero-fill.
- **`_m` (merge predication):** Inactive result elements are copied from an explicit merge vector argument (typically the first vector operand for binary ops). Maps to `Pg/M` in assembly. For unary ops, a separate merge-input argument appears before the predicate; for binary/ternary ops, the first operand doubles as the merge source.

Example (ACLE §11.2):
```c
// ADD (vectors, predicated), merge form:
// ASM:  ADD Zd.S, Pg/M, Zd.S, Zs2.S
Zd = svadd_u32_m(Pg, Zd, Zs2);    // inactive lanes from Zd

// ADD (vectors, predicated), zero form:
Zd = svadd_u32_z(Pg, Za, Zb);     // inactive lanes = 0
```

#### Key Operations

| Category         | Intrinsics                                              | Notes                                      |
|------------------|---------------------------------------------------------|--------------------------------------------|
| Load (unit)      | `svld1_f32(pg, ptr)`                                    | Predicated; inactive = undefined or merged |
| Load gather      | `svld1_gather_s32index_f32(pg, base, idx)`              | Per-lane index vector; native instruction  |
| Store scatter    | `svst1_scatter_s32index_f32(pg, base, idx, data)`       |                                            |
| Add              | `svadd_f32_x(pg, a, b)`                                 | All widths + float types                   |
| Multiply         | `svmul_f32_x(pg, a, b)`                                 |                                            |
| FMA              | `svmla_f32_x(pg, acc, a, b)` = acc + a×b               | Fused; dest is explicit accumulator        |
| Reduce sum       | `svaddv_f32(pg, v)` → scalar                            | Horizontal reduce under predicate          |
| Reduce max/min   | `svmaxv_f32(pg, v)`, `svminv_f32(pg, v)`               |                                            |
| Permute          | `svtbl_f32(v, idx)` (lookup), `svext_f32(a, b, imm)`   | TBL = table lookup with element index      |
| While loop pred  | `svwhilelt_b32(i, n)` → svbool_t                        | Sets pred bits true while i+lane < n       |
| Predicate ops    | `svand_b_z`, `sveor_b_z`, `svnot_b_z`                  | Boolean algebra on p-registers             |
| Count lanes      | `svcntd()`, `svcntw()`, `svcnth()`, `svcntb()`         | Returns VL/64, VL/32, VL/16, VL/8         |
| Compress         | `svcompact_f32(pg, v)`                                  | Pack active lanes to low positions         |

#### vscale and VL-Agnostic Code

The SVE vscale concept: runtime VL = `svcntb() * 8` (in bits). Loops increment by `svcntw()` (for i32 ops), generated by the compiler automatically when using VL-agnostic intrinsics. `__ARM_FEATURE_SVE_BITS = 0` means VL is not known at compile time. Fixed-length SVE (`__ARM_FEATURE_SVE_BITS = 512`) allows treating SVE registers as fixed-size for LLVM IR `<vscale x N x T>` purposes.

---

### 2.2 RISC-V Vector Extension 1.0

**Source:** RISC-V "V" Vector Extension specification v1.0 (riscv/riscv-v-spec, GitHub; archived 2024-03-20). All section references below are from this document.

#### Architecture Overview

RVV 1.0 is ratified in the RISC-V privileged architecture. The number of vector registers is fixed at 32 (v0–v31), but the number of elements each holds scales with the implementation-defined VLEN parameter (minimum 128 bits in the ratified spec).

Key configuration CSRs (§3):
- `vlenb` (read-only CSR): VLEN/8 — the number of bytes in a single vector register.
- `vl`: the active vector length (number of elements currently processed), set by `vsetvli`.
- `vtype`: encodes SEW (Standard Element Width) and LMUL (see below).
- `vstart`: the starting element index (used for fault recovery).
- `vxrm`: fixed-point rounding mode register.

#### vsetvli and the LMUL/SEW Model (§6)

`vsetvli` is the configuration instruction that sets up `vl` and `vtype` in one instruction:

```asm
vsetvli t0, a0, e32, m2, ta, ma   # SEW=32b, LMUL=2, tail-agnostic, mask-agnostic
# t0 = actual vl set (≤ a0 elements)
```

**SEW** (Standard Element Width): 8, 16, 32, or 64 bits — the default element size for the operation.

**LMUL** (Length Multiplier): controls how many physical registers form one logical register group (§3.4.2):

| LMUL | Assembler | Physical regs per logical group | Max elements (VLEN=128b, SEW=32b) |
|------|-----------|----------------------------------|-------------------------------------|
| 1/8  | `mf8`     | 1/8 of one register              | 4 × (1/8) = < 1 — unusual          |
| 1/4  | `mf4`     | 1/4 of one register              | 1                                   |
| 1/2  | `mf2`     | 1/2 of one register              | 2                                   |
| 1    | `m1`      | 1 register                       | 4                                   |
| 2    | `m2`      | 2 consecutive registers          | 8                                   |
| 4    | `m4`      | 4 consecutive registers          | 16                                  |
| 8    | `m8`      | 8 consecutive registers          | 32                                  |

Fractional LMUL (mf2, mf4, mf8) allows mixed-width operations to use proportional register counts. Example: a loop that mixes f16 and f32 data can set SEW=32, LMUL=1 for f32 and SEW=16, LMUL=1/2 for f16, keeping the element count equal and register count balanced. This avoids wasting the 32 vector registers when operating on narrow types.

The effective maximum vector length (VLMAX) = LMUL × VLEN / SEW. Since VLEN is implementation-defined (must be ≥ 128), code must not assume a specific VLMAX.

#### Mask Register Model (§5)

RVV has a **single dedicated mask source**: `v0`. Only `v0` can appear as the mask argument (the `vm` bit in instruction encoding). This is a fundamental constraint:
- Masked form: `vadd.vv vd, vs2, vs1, v0.t` — add where v0 bit=1.
- No operation can use v1, v2, etc. as a mask directly.
- `v0` is part of the general vector register file; code must manage register pressure around it explicitly.
- Predicate computation (vmslt, vmseq, etc.) writes results into any vector register but must be `vmv1r.v v0, vX` before use as a mask.
- Mask operations (vmand, vmor, vmxor, vmnot etc.) can manipulate mask registers in any vector register but only `v0` feeds the mask port.
- Three destination policies: **tail-undisturbed** (tail lanes preserve destination), **tail-agnostic** (tail lanes = all-ones or unchanged, implementation choice), and same for mask-undisturbed vs mask-agnostic.

#### Load/Store Addressing Modes (§7)

| Mode            | Instructions                              | Notes                                           |
|-----------------|-------------------------------------------|-------------------------------------------------|
| Unit-stride     | `vle32.v vd, (rs1), vm`                  | Contiguous elements from base                   |
| Strided         | `vlse32.v vd, (rs1), rs2, vm`            | Fixed byte stride in rs2                        |
| Indexed gather  | `vluxei32.v vd, (rs1), vs2, vm`          | Unordered; vs2 = per-element byte offsets       |
| Indexed scatter | `vsuxei32.v vs3, (rs1), vs2, vm`         | Unordered scatter                               |
| Fault-only-first| `vle32ff.v vd, (rs1), vm`               | Trims `vl` at first memory fault past element 0 |
| Segmented       | `vlseg3e32.v vd, (rs1), vm`             | AoS load: 3 fields interleaved, loaded to 3 Vregs |

Indexed gather/scatter use `vs2` for byte offsets; the EEW of vs2 is encoded in the instruction separately from SEW, allowing 32-bit indices even with 64-bit data (EMUL = (EEW/SEW)×LMUL).

#### Reduction Operations (§14)

```asm
vredsum.vs   vd, vs2, vs1, vm  # Integer reduce-sum; vs1[0] = initial value
vfredosum.vs vd, vs2, vs1, vm  # Ordered float reduce-sum (sequential order)
vfredusum.vs vd, vs2, vs1, vm  # Unordered float reduce-sum
vfredmax.vs  vd, vs2, vs1, vm  # Float max
vrgather.vv  vd, vs2, vs1, vm  # Gather (permute): vd[i] = vs2[vs1[i]]
vcompress.vm vd, vs2, vs1      # Pack active lanes; vs1 is mask vector (not just v0)
```

---

### 2.3 Scalable ISA Comparison

| Dimension                         | ARM SVE2                                           | RISC-V V 1.0                                          |
|-----------------------------------|----------------------------------------------------|-------------------------------------------------------|
| Vector length known at compile?   | No (VL-agnostic by default); optional `arm_sve_vector_bits` for fixed | No; VLEN implementation-defined ≥ 128b |
| Max VL                            | Up to 2048 bits (16× 128-bit chunks)               | Unbounded above min; VLEN/ELEN constrained             |
| Predicate/mask registers          | P0–P15, dedicated, (VL/8) bits wide               | v0 only, reused from data regfile                     |
| Predication modes                 | `_x` (undef), `_z` (zero), `_m` (merge) per op    | Mask-undisturbed or mask-agnostic per `vsetvli`       |
| Governing predicate               | Any P-reg; p0 conventional for loops               | v0 always                                             |
| Gather/Scatter                    | Native `ld1_gather` / `st1_scatter`                | `vluxei` / `vsuxei` native                            |
| While-loop predicate setup        | `whilelt`, `whilele`, `whilelo`, etc.              | `vsetvli` sets `vl`; branch on `vl < requested`      |
| Register pressure management      | 32 Z-regs + 16 P-regs (independent)               | 32 V-regs shared; v0 reserved for mask                |
| Mixed-width within one loop       | Different type suffixes, same predicate            | Fractional LMUL (mf2/mf4) balances reg usage         |
| Compress/expand (pack/unpack)     | `svcompact`, `svexpand`                            | `vcompress.vm` for pack; expand = indexed scatter     |

**How each handles "lanes unknown until runtime":**
- SVE2: The programmer writes VL-agnostic intrinsics; `svcntw()` queries the runtime VL. Loops written as `do { pg = svwhilelt_b32(i, n); ... i += svcntw(); } while (svptest_first(svptrue_b8(), pg))`. The hardware vector length is a first-class value the ISA exposes.
- RVV 1.0: `vsetvli` returns the actual `vl` that was set (≤ the requested application vector length). The strip-mining loop uses the returned `vl` as the actual element count. `vlenb` CSR gives bytes per register at runtime; VLMAX = computed from LMUL × VLEN / SEW.

---

## 3. GPU Vector Model

### 3.1 NVIDIA PTX / CUDA

**Source:** PTX ISA 9.2 Reference (docs.nvidia.com/cuda/parallel-thread-execution)

#### Execution Model

PTX uses an **implicit SIMD** model: programmer writes scalar code per thread; the hardware schedules 32 threads simultaneously as a **warp**. The 32-lane granularity is fixed in hardware across all NVIDIA GPU architectures. Unlike CPU SIMD, there is no intrinsic `__m256` type; each thread holds its own register file.

From the compiler perspective, a warp of 32 threads executing the same PTX instruction is logically equivalent to a 32-lane SIMD operation.

#### Predicate Registers

- Each thread has dedicated 1-bit **predicate registers** (`%p0`, `%p1`, ...); count is implementation-defined per SM generation (typically ≥7 per thread).
- Predicate registers are set by comparison (`setp`) instructions and used to guard subsequent instructions.
- Example:
  ```ptx
  setp.lt.f32   %p0, %a, %b;    // %p0 = (a < b)
  @%p0 add.f32  %c, %a, %b;     // conditional add
  @!%p0 mov.f32 %c, %b;         // negated condition
  ```
- When different threads in a warp diverge on a predicate, the hardware serializes the divergent paths (warp divergence). All lanes execute both paths but with the inactive lanes predicated off.

#### Vector Types (.v2, .v4)

PTX supports limited-length vector types for wide memory operations (PTX ISA §5.4.2, §6.4.3):
- `.v2` and `.v4` of any non-predicate fundamental type, up to 128 bits total.
- `.v4 .f64` is **not allowed** (would exceed 256 bits).
- Purpose: pack multiple loads/stores into a single memory transaction for bandwidth efficiency.
- Examples:
  ```ptx
  .global .v4 .f32 V;
  ld.global.v4.f32  {a, b, c, d}, [addr+16];   // 4×f32 = 128-bit wide load
  ld.global.v2.u32  V2, [addr+8];               // 2×u32 = 64-bit wide load
  ```
- These are NOT SIMD in the CPU sense; they are wide memory access helpers. The arithmetic model remains scalar-per-thread.

#### Tensor Cores (PTX ISA §9.7.14)

Tensor cores perform warp-cooperative matrix multiply-accumulate (MMA). They are exposed via `wmma` (PTX 6.0+, sm_70+) and `mma.sync` instructions:

```ptx
wmma.load.a.sync.aligned.m16n16k16.global.row.f16  {a0..a7}, [A];
wmma.load.b.sync.aligned.m16n16k16.global.col.f16  {b0..b7}, [B];
wmma.load.c.sync.aligned.m16n16k16.global.row.f32  {c0..c7}, [C];
wmma.mma.sync.aligned.m16n16k16.row.col.f32.f32
    {d0..d7}, {a0..a7}, {b0..b7}, {c0..c7};
```

Key properties:
- The matrix is distributed across all 32 threads in a warp; each thread holds a fragment.
- Shapes: m16n16k16 (f16→f32), m8n32k16, m32n8k16 (f16→f32), m16n16k8 (f64→f64), integer variants.
- sm_90+ adds `mma.sync` with `.kind::mxint8`, `wgmma` (warp-group MMA) for sm_90.
- The `.aligned` qualifier requires all threads in the warp to execute the instruction (no warp divergence).

#### Warp-Level Communication

- `shfl.sync` instructions: `shfl.sync.up`, `shfl.sync.down`, `shfl.sync.bfly`, `shfl.sync.idx` — shuffle register values between threads within a warp without shared memory.
- `vote.sync` and `match.sync`: warp-level ballot and mask operations.
- `bar.warp.sync membermask`: intra-warp barrier.
- `barrier.cluster`: inter-CTA barrier in Hopper (sm_90+).

---

### 3.2 SPIR-V Vulkan

**Source:** SPIR-V Unified Specification v1.6 Revision 7 (registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html)

#### Vector Types

SPIR-V has a native vector type at the IR level, unlike PTX:
- `OpTypeVector <component_type> <count>`: fixed-count vector of 2, 3, 4, 8, or 16 components.
- Component types: bool, integer (various widths), float (f16, f32, f64).
- `OpVectorExtractDynamic`: extract a component at a dynamic index (index out-of-range is undefined behavior per §3.3.12).
- `OpVectorShuffle`: create a new vector by selecting components from two source vectors with a compile-time index list.
- Arithmetic on `OpTypeVector` is element-wise for most instructions; explicit vector ops.

SPIR-V does **not** have a scalable vector type — all vector lengths are compile-time constants in the module. This makes SPIR-V structurally closer to fixed-width SIMD (NEON/SSE) than to scalable SIMD (SVE2/RVV) at the IR level.

#### Subgroup Operations

Subgroups map to GPU warps in Vulkan/GLSL. Relevant capabilities:
- `GroupNonUniform` capability enables subgroup operations.
- **SubgroupSize** built-in: the subgroup size for the invocation (implementation-dependent, typically 32 for NVIDIA, 64 for AMD, 4–64 for Intel).
- Key subgroup operations:
  - `OpGroupNonUniformBallot`: each invocation contributes a boolean; result is a 4×u32 bitmask.
  - `OpGroupNonUniformBroadcast`, `OpGroupNonUniformBroadcastFirst`: lane 0 or any-lane broadcast.
  - `OpGroupNonUniformShuffle`, `OpGroupNonUniformShuffleXor`: cross-lane data movement.
  - `OpGroupNonUniformIAdd`, `OpGroupNonUniformFAdd` (and Min, Max, etc.): subgroup reductions.
  - `OpGroupNonUniformAll`, `OpGroupNonUniformAny`: predicate reductions.
- `SubgroupBallotKHR` extension: legacy path still widely used.

#### Workgroup and Shared Memory

- Workgroups map to CUDA thread blocks. All invocations in a workgroup can communicate via `Workgroup`-space variables.
- `OpControlBarrier` with `Workgroup` scope: synchronization fence.
- `CooperativeMatrixKHR` extension (SPV_KHR_cooperative_matrix): adds `OpTypeCooperativeMatrixKHR` for matrix types whose element distribution across subgroup invocations is implementation-defined — the SPIR-V analog of PTX `wmma`.

---

### 3.3 Warp-as-vector vs CPU SIMD: Abstraction Leaks

| Dimension                        | CPU SIMD (AVX-512/SVE2/RVV)                     | GPU implicit-SIMD (PTX/SPIR-V)                        |
|----------------------------------|-------------------------------------------------|-------------------------------------------------------|
| Scalar vs vector programming     | Explicit: programmer writes vector intrinsics   | Implicit: programmer writes scalar; hardware vectorizes |
| Lane count fixed?                | Fixed (AVX-512=16 f32) or scalable (SVE2/RVV)  | Fixed at 32 (NVIDIA warp); 64 (AMD wavefront)         |
| Divergence handling              | N/A — all lanes run same instruction            | Serialized divergent paths; mask bits track active threads |
| Mask/predicate register          | k-regs (AVX-512), p-regs (SVE2), v0 (RVV)      | Per-thread 1-bit predicate registers (%p0, %p1…)     |
| Memory access granularity        | Cache-line aware; masked load/store native       | Coalesced memory transactions; 32 concurrent accesses |
| Shared fast memory               | L1/L2 caches (transparent)                      | Explicit shared memory (smem); programmer managed     |
| Cross-lane communication         | Shuffle/permute within vector register           | shfl.sync (warp shuffle); smem; no direct cross-warp  |
| Reduction                        | Native reduce instructions or tree via shuffle  | warp-level reduce via shfl.sync or GroupNonUniform    |
| Synchronization                  | Implicit (single-thread SIMD)                   | bar.warp.sync, barrier.cluster, OpControlBarrier      |

**Key abstraction leaks:**
1. **Warp divergence**: CPU SIMD has no concept of "divergence" — all lanes execute the same instruction with masking. GPU divergence means different lanes execute different instruction sequences, serialized. An IR that abstracts both must represent divergence cost differently.
2. **Memory coalescing**: GPU efficiency requires 32 threads to access 32 consecutive addresses in one transaction. Gather operations on GPU are expensive in a fundamentally different way than on CPU.
3. **Shared memory vs L1**: GPU smem is programmer-visible and must be explicitly allocated; CPU caches are transparent. Higher-level SIMD abstractions that assume transparent caching will generate suboptimal GPU code.
4. **Warp vs subgroup size portability**: SPIR-V's `SubgroupSize` is not a compile-time constant in general; it is a built-in variable. Code that assumes 32-lane subgroups will fail on AMD (64) or Intel GPU (variable).

---

## 4. Cross-ISA Op Coverage Matrix

Legend: **N** = native instruction; **E:X** = emulate via X; **—** = not applicable.

The element type shown in parentheses indicates the primary type for which the entry applies; behavior for other types is noted where it differs significantly.

| Abstract Op            | NEON (128b)                                    | AVX2 (256b)                                         | AVX-512 (512b)                                    | SVE2 (scalable)                                    | RVV 1.0 (scalable)                                 | PTX (warp/32)                                         | SPIR-V (subgroup)                                     |
|------------------------|------------------------------------------------|-----------------------------------------------------|---------------------------------------------------|----------------------------------------------------|----------------------------------------------------|-------------------------------------------------------|-------------------------------------------------------|
| **load (unit)**        | N: `vld1q_f32`                                 | N: `_mm256_load_ps`                                 | N: `_mm512_load_ps`                               | N: `svld1_f32`                                     | N: `vle32.v`                                       | N: `ld.global.v4.f32` (per-thread)                   | N: `OpLoad` (per-invocation)                         |
| **load (masked)**      | E: load+blend with BSL                         | E: `_mm256_maskload_ps` (limited); blend            | N: `_mm512_mask_load_ps(src, k, ptr)`             | N: `svld1_f32(pg, ptr)`                            | N: `vle32.v vd,(rs1),v0.t`                         | N: `@%p0 ld.global.f32`                              | N: conditional via `@` predicate or OpSelect         |
| **store (unit)**       | N: `vst1q_f32`                                 | N: `_mm256_store_ps`                                | N: `_mm512_store_ps`                              | N: `svst1_f32(pg, ptr, v)`                         | N: `vse32.v`                                       | N: `st.global.v4.f32`                                | N: `OpStore`                                         |
| **store (masked)**     | E: condition+masked store loop or BSL+store    | E: `_mm256_maskstore_ps` (epi32 imm only); blend+store | N: `_mm512_mask_store_ps(ptr, k, a)`           | N: `svst1_f32(pg, ptr, v)` — pg masks all stores   | N: `vse32.v vs,(rs1),v0.t`                         | N: `@%p0 st.global.f32`                              | N: guarded `OpStore` with `@` predicate             |
| **add**                | N: `vaddq_f32` / `vaddq_s32`                   | N: `_mm256_add_ps` / `_mm256_add_epi32`             | N: `_mm512_add_ps` / `_mm512_add_epi32`           | N: `svadd_f32_x(pg,a,b)`                           | N: `vfadd.vv` / `vadd.vv`                          | N: `add.f32 %c, %a, %b`                              | N: `OpFAdd` / `OpIAdd`                               |
| **mul**                | N: `vmulq_f32`; `vmulq_s32` (NEON, AArch64)   | N: `_mm256_mul_ps`; `_mm256_mullo_epi32`            | N: `_mm512_mul_ps`; `_mm512_mullo_epi32`          | N: `svmul_f32_x(pg,a,b)`                           | N: `vfmul.vv` / `vmul.vv`                          | N: `mul.f32`                                         | N: `OpFMul` / `OpIMul`                               |
| **fma**                | N: `vfmaq_f32` (AArch64)                       | N: `_mm256_fmadd_ps` (FMA3 ext, Haswell+)           | N: `_mm512_fmadd_ps`                              | N: `svmla_f32_x(pg, acc, a, b)`                    | N: `vfmacc.vv`                                     | N: `fma.rn.f32 %d, %a, %b, %c`                      | N: `OpExtInst fma` (GLSL.std.450 §26)                |
| **gather**             | E: scalar loop (no native gather in NEON)      | N: `_mm256_i32gather_ps` (AVX2)                     | N: `_mm512_i32gather_ps`                          | N: `svld1_gather_s32index_f32(pg, base, idx)`      | N: `vluxei32.v vd,(rs1),vs2,v0.t`                  | E: scalar loop per thread (memory coalescing concern) | E: scalar loop or `OpExtInst` gather                 |
| **scatter**            | E: scalar loop                                 | E: scalar loop (AVX2 has no scatter)                | N: `_mm512_i32scatter_ps`                         | N: `svst1_scatter_s32index_f32(pg, base, idx, v)`  | N: `vsuxei32.v vs3,(rs1),vs2,v0.t`                 | E: scalar loop per thread                             | E: scalar loop                                       |
| **cmp → mask**         | N: `vcgtq_f32` → `uint32x4_t` (lane mask vec) | N: `_mm256_cmp_ps` → `__m256` (lane mask vec)       | N: `_mm512_cmp_ps_mask` → `__mmask16` (k-reg)    | N: `svcmpgt_f32(pg,a,b)` → `svbool_t`             | N: `vmfgt.vv vd,vs2,vs1,v0.t` → mask in vd        | N: `setp.gt.f32 %p0, %a, %b`                        | N: `OpFOrdGreaterThan` → bool vector or subgroup ballot |
| **mask_select (blend)**| N: `vbslq_f32(mask, a, b)` (BSL)              | N: `_mm256_blendv_ps(b, a, mask)` (blendv)          | N: `_mm512_mask_blend_ps(k, b, a)` (blend)        | N: `svsel_f32(pg, a, b)` — first-class predicate   | N: `vmerge.vvm vd, vs2, vs1, v0` (integer/fp merge)| N: `selp.f32 %d, %a, %b, %p0` (setp+selp)           | N: `OpSelect`                                        |
| **reduce_sum**         | N: `vaddvq_f32` (AArch64 horizontal add)       | E: 2× `_mm_hadd_ps` + extract + hadd (4 insns)     | N: `_mm512_reduce_add_ps`                         | N: `svaddv_f32(pg, v)` → scalar                   | N: `vfredosum.vs` / `vredsum.vs`                   | E: `shfl.sync.bfly` loop (log2(32) steps)             | N: `OpGroupNonUniformFAdd(Reduce)`                   |
| **reduce_max**         | N: `vmaxvq_f32` (AArch64)                      | E: 2× `_mm256_max_ps` + vperm2f128 + max (4 insns) | N: `_mm512_reduce_max_ps`                         | N: `svmaxv_f32(pg, v)` → scalar                   | N: `vfredmax.vs`                                   | E: `shfl.sync.bfly` + max per step (log2 steps)       | N: `OpGroupNonUniformFMax(Reduce)`                   |
| **hadd (adj-pair)**    | N: `vpaddq_f32` (64b or 128b pairwise add)     | N: `_mm256_hadd_ps` (SSSE3 / AVX2)                 | E: vpermilps + add (no dedicated hadd in AVX-512) | E: `svaddp_f32(pg, a, b)` (SVE2 pairwise add)      | E: multi-step with interleave + add                | E: shfl.sync.xor + add (1 step for adjacent pair)    | E: shuffle + add                                     |
| **perm/shuffle**       | N: `vqtbl1q_u8` (byte tbl); `vzip1q`, `vtrn1q` (structured) | N: `_mm256_permutevar8x32_ps` (within 256b, AVX2); cross-lane = vperm2i128 | N: `_mm512_permutexvar_ps` (full 512b cross-lane, AVX-512F) | N: `svtbl_f32(v, idx)` (full VL permute) | N: `vrgather.vv vd, vs2, vs1` (full permute) | N: `shfl.sync.idx` for cross-lane; `mov` for intra | N: `OpVectorShuffle` (compile-time indices); `OpGroupNonUniformShuffle` (runtime) |
| **broadcast (scalar→vec)** | N: `vdupq_n_f32(x)` (dup scalar)         | N: `_mm256_broadcast_ss(&x)`                        | N: `_mm512_set1_ps(x)`                            | N: `svdup_n_f32(x)`                                | N: `vmv.v.x vd, rs1`                              | N: implicit (each thread has scalar)                  | N: `OpCompositeConstruct` (constant); `OpGroupNonUniformBroadcast` (dynamic) |
| **compress (pack active lanes)** | E: scalar loop or VTBL-based    | E: scalar loop (no native)                          | N: `_mm512_mask_compress_ps(src, k, a)`           | N: `svcompact_f32(pg, v)`                          | N: `vcompress.vm vd, vs2, vs1` (vs1 = mask reg, not just v0) | E: warp ballot + scan + shfl (multi-step) | E: multi-step with ballot |
| **expand (scatter to mask positions)** | E: scalar loop             | E: scalar loop                                      | N: `_mm512_mask_expand_ps(src, k, a)`             | N: `svexpand_f32(pg, v)` (SVE predicate scatter-fill) | E: indexed scatter with precomputed mask indices | E: warp ballot + scatter (multi-step)                | E: multi-step                                        |

---

## 5. Predication Model Recommendations

### Summary of the Four Mask Models

| ISA       | Mask storage        | How populated                               | How consumed                              | Boolean ops on masks        |
|-----------|---------------------|---------------------------------------------|-------------------------------------------|-----------------------------|
| AVX-512   | k0–k7 (dedicated, 64b each) | `_mm512_cmp_ps_mask`, `_kand_mask16`, load | Every arithmetic/load/store has mask variant | `_kand`, `_kor`, `_knot`, `_kxor` native |
| SVE2      | P0–P15 (dedicated, VL/8 bits each) | `svcmpXX_f32`, `svwhilelt`, `svpfalse` | `_x`/`_z`/`_m` suffix on every op | `svand_b_z`, `sveor_b_z`, `svnot_b_z`, `svptest` |
| RVV 1.0   | v0 only (from 32-reg file) | `vmfgt.vv`, `vmseq.vv` into any vX; then `vmv1r.v v0,vX` | `v0.t` suffix on ops | `vmand.mm`, `vmor.mm`, `vmxor.mm` (any vX as mask reg, but only v0 feeds instructions) |
| NEON      | None (no mask regs) | `vcgtq_f32` → lane-wide all-1/all-0 vector | `vbslq_uN(mask, a, b)` (BSL blend)        | `vandq_u32`, `vorrq_u32`, `vmvnq_u32` on full vectors |
| PTX       | Per-thread %p regs  | `setp` instructions                         | `@%p0 insn` prefix on any instruction     | `and.pred`, `or.pred`, `not.pred` native |
| SPIR-V    | bool vectors or subgroup ballots | `OpFOrdGreaterThan` → bool vec; `OpGroupNonUniformBallot` | `OpSelect`, guarded `OpStore` | Boolean ops on i1 vectors; `OpBitwiseAnd` on ballot uvec4 |

### Recommendation

**Expose `Mask<N>` as a first-class type in the Simple SIMD IR.** Rationale and lowering strategy:

1. **AVX-512 k-registers:** Direct lowering. `Mask<16>` (for f32 lanes) holds a single `__mmask16`; Boolean ops on `Mask` lower to `_kand_mask16`/`_kor_mask16`. This is the cleanest mapping — the ISA was designed for exactly this abstraction.

2. **SVE2 p-registers:** Direct lowering. `Mask<VL/32>` holds one `svbool_t` (P-register). Boolean ops lower to `svand_b_z` / `sveor_b_z`. The three predication flavors (x/z/m) are a lowering detail: the IR should emit `_z` (zero-predicated) by default for safety, and the backend optimizer may promote to `_x` where the inactive lanes are provably not read. The `_m` (merge) form should only be generated when an explicit merge-source is tracked in the IR.

3. **RVV v0 register pressure:** This is the problematic case. `Mask<N>` lowers to a vector register that must be `v0` when consumed by a masked instruction. The register allocator must treat `Mask<N>` as requiring `v0` at each use site, spilling v0 to another register across non-mask uses. Two implementation strategies:
   - **Simple strategy:** Lower `Mask<N>` as a normal vector register (any vX); emit `vmv1r.v v0, vX` before each masked instruction use. This costs one extra instruction per masked op but is predictable.
   - **Optimized strategy:** Track `Mask<N>` in a parallel pseudo-regfile; do not allocate to v0 until a masked instruction is emitted, then coalesce. This is complex but avoids unnecessary vmv1r instructions in tight loops.
   - **Recommendation for Simple:** Start with the simple strategy. The extra `vmv1r.v` is single-cycle on all known RVV implementations.

4. **NEON synthesis (no mask regs):** `Mask<N>` lowers to a full-width vector register containing 0x00…00 or 0xFF…FF per lane (as produced by vcgtq etc.). Masked arithmetic is synthesized as: `a = op(a, b); result = vbslq(mask, a, prior_a)`. This costs one extra vector register and one BSL instruction. There is no way to avoid this on NEON without scalar fallback; it is a fundamental architectural cost.

5. **PTX/SPIR-V:** `Mask<N>` lowers to a predicate register (`%pX`) in PTX and to a boolean vector / subgroup ballot in SPIR-V. In PTX the hardware has dedicated predicate register slots (independent of the scalar/vector regfile) so there is no pressure concern. In SPIR-V subgroup operations, `Mask<N>` becomes a `uvec4` ballot value.

**The key conclusion:** `Mask<N>` as a first-class IR type is well-motivated because it maps cleanly to dedicated hardware on 4 of 6 backends (AVX-512, SVE2, PTX, SPIR-V) and is synthesizable at well-defined cost on the remaining 2 (NEON = BSL, RVV = vmv1r). Encoding masks as ad-hoc lane-wide vectors (NEON style) would require the compiler to recognize pattern-match across all backends, which is harder and less reliable.

---

## 6. vscale/LMUL Handling

### The Type System Challenge

Both SVE2 and RVV require representing "a vector of N elements where N is unknown at compile time." LLVM's solution is `<vscale x M x T>` — a scalable vector type where the actual lane count is `M × vscale` (vscale = hardware VL / minimum VL). Simple's SIMD IR needs an analogous representation.

### SVE2: vscale in the Type System

- ACLE represents VL-agnostic vectors as `svXXX_t` opaque types (e.g., `svfloat32_t`). These are not fixed-width C arrays; they are hardware-width scalable types.
- For codegen purposes, map `VecScalable<T>` → `<vscale x M x T>` in LLVM IR, where M = 128 / (sizeof(T) * 8) (the minimum VL element count for type T at VLEN=128).
- The runtime lane count = `svcntw()` (for T=f32), available as a CSR read or from the LLVM `llvm.aarch64.sve.cntw` intrinsic.
- `vscale` in LLVM IR evaluates to the hardware VL in units of 128-bit chunks. For f32: actual_lanes = vscale × 4.
- **Impact on codegen:** loop increment = `svcntw()` (queried once at loop entry); loop predicate = `svwhilelt_b32(i, n)` at loop top.

### RVV: LMUL as a Codegen Parameter

LMUL is not a type-system parameter in the RVV ISA — it is a runtime `vtype` setting. However, it has type-system implications:

1. **LMUL=1 baseline:** The natural mapping for `VecScalable<T>` in RVV is LMUL=1, giving VLMAX = VLEN/SEW elements. This is analogous to `<vscale x M x T>` in LLVM where M = VLEN/SEW/vscale.

2. **LMUL and register pressure:** Increasing LMUL increases the number of elements processed per iteration (wider effective vector) but consumes more physical vector registers. With 32 vector registers (v0–v31) and LMUL=8, only 4 distinct logical register groups exist. This drastically reduces the register budget for the loop body. In practice:
   - LMUL=1 is the default; most loops work well here.
   - LMUL=2 or LMUL=4 is used for throughput-critical loops with high compute/register ratio.
   - LMUL=8 should be reserved for simple streaming kernels with 1–2 operands.
   - Fractional LMUL (mf2, mf4, mf8): used in mixed-width operations (e.g., f16 inputs, f32 accumulator). The fractional form uses fewer than one full register, so it must satisfy VLEN/SEW ≥ 1 (i.e., mf8 with SEW=64 requires VLEN ≥ 512).

3. **Codegen implications for Simple:**
   - The IR should not expose LMUL directly; it should be an optimization hint or a target-specific backend parameter.
   - The default lowering: LMUL=1 for all scalar types.
   - An LMUL-widening optimization pass can detect loops with low register usage and increase LMUL for throughput.
   - The `vsetvli` instruction must be re-emitted every time SEW or LMUL changes within a function; the backend must track `vtype` state and insert `vsetvli` at boundaries.

4. **Constraint: minimum VLEN and SEW/LMUL validity.** The spec requires VLEN ≥ max(ELEN, 32) where ELEN is the maximum supported element width. For LMUL=mf8 and SEW=64: VLEN ≥ 512 is required. The compiler must either:
   - Avoid mf8+SEW64 unless VLEN ≥ 512 is guaranteed (via target feature flags).
   - Or conservatively only use LMUL values where floor(VLEN × LMUL / SEW) ≥ 1 for the minimum guaranteed VLEN.

5. **v0 register pressure and LMUL interaction:** With LMUL=M, logical register group starting at v0 occupies physical registers v0..v(M-1). This means at LMUL=2 and above, v0 (and v1) are consumed by the mask logical group — effectively reducing the number of available logical register groups by one for the mask. The backend must account for this when scheduling masked loops with high LMUL.

### Recommended Type System Design for Simple

```
// Abstract scalable vector types:
VecFixed<N, T>        // fixed N lanes — maps to XMM/YMM/ZMM or Q-regs
VecScalable<T>        // scalable — maps to SVE2 Z-reg or RVV vX with vsetvli
MaskFixed<N>          // N-bit mask — maps to k-reg (AVX-512) or lane-wide vec (others)
MaskScalable          // scalable mask — maps to P-reg (SVE2) or v0 (RVV)
```

For `VecScalable<T>` in LLVM IR:
- AArch64 SVE2: `<vscale x (128/sizeof_bits(T)) x T>` — e.g., f32 → `<vscale x 4 x float>`
- RISC-V RVV: `<vscale x (ELEN/sizeof_bits(T)) x T>` with LMUL=1 baseline — vscale = VLEN/ELEN at minimum; effectively the same LLVM vector type but with a different hardware meaning of vscale.

The key design discipline: **LMUL must not escape into the Simple type system**. It is a micro-architectural parameter that the backend optimizer controls. Exposing LMUL to the language level would create unportable code and unnecessary complexity.

---

## References

- ARM C Language Extensions (ACLE) — arm-software.github.io/acle/main/acle.html (Q3 2025 edition). §9 (NEON), §11 (SVE/SVE2), §15 (SME).
- RISC-V "V" Vector Extension v1.0 — github.com/riscvarchive/riscv-v-spec (archived 2024). §3 (programmer's model), §6 (vsetvli), §7 (load/store), §14 (reductions), §16 (permutation).
- Intel Intrinsics Guide — intel.com/content/www/us/en/docs/intrinsics-guide (access blocked at fetch time; content derived from SDM Vol. 1 §14–15 and prior knowledge).
- Intel Architecture Software Developer's Manual, Vol. 1 — §5 (SSE2), §14 (AVX), §15 (AVX-512).
- PTX ISA 9.2 — docs.nvidia.com/cuda/parallel-thread-execution. §5.4.2 (vectors), §6.4.3 (vector operands), §9.7.13 (synchronization), §9.7.14 (warp matrix MMA).
- SPIR-V Unified Specification v1.6 Rev 7 — registry.khronos.org/SPIR-V/specs/unified1/SPIRV.html. §2.2 (terms), §3.3.12 (composite instructions), §3.2.20 (built-ins), §3.2.30 (capabilities).
