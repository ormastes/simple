<!-- claude-arch -->
# Architecture: Backend Strict-Emit — Detail Part 1 (Encoders + Bytes)

**TL;DR:** This document covers §1–7 of the SIMD backend encoder specification: MachInst
enum extensions, per-target helper signatures, and full byte-level encoder pseudocode for
EVEX (AVX-512), AArch64 SVE2, and RVV 1.0, plus NEON synthesis recipes and the AVX2
scatter-fallback loop. Register-allocation contracts, verification harnesses, capability
detection, and errata guards (§8–14) are covered in
`simd_backend_strict_emit_detail_part2.md` (C3b). All byte/bit claims cite C1
(`doc/01_research/simd_isa_deep_2026-05-02.md`) and carry `[UNVERIFIED]` where the
original research flagged primary-spec cross-check as pending.

---

## Table of Contents

1. [MachInst Extension — Enum Definitions](#1-machinst-extension--enum-definitions)
2. [Per-Target Encoder Helper Signatures](#2-per-target-encoder-helper-signatures)
3. [EVEX Byte-Layout Encoder](#3-evex-byte-layout-encoder)
4. [AArch64 SVE2 32-bit Instruction Encoder](#4-aarch64-sve2-32-bit-instruction-encoder)
5. [RVV Instruction Encoder](#5-rvv-instruction-encoder)
6. [NEON Synthesis Recipes](#6-neon-synthesis-recipes)
7. [AVX2 Scatter Fallback](#7-avx2-scatter-fallback)

---

## 1. MachInst Extension — Enum Definitions

### 1.1 `MachRegKind` Additions

One row per register class. Existing `Gpr`/`Neon128` included for cross-reference.
`LMUL-align` applies only to RVV (§1.1a); N/A elsewhere.
Callee-saved sets follow SysV AMD64 ABI (Linux), AArch64 PCS, RISC-V psABI.

| Variant | Bit-width | Count | LMUL-align | Caller-saved | Callee-saved | Notes |
|---|---|---|---|---|---|---|
| `Gpr` | 64 | 16/31/32 | N/A | platform | platform | Existing; not SIMD |
| `Neon128` | 128 | 32 (V0–V31) | N/A | V0–V7 | V8–V15 (low 64b only) | V16–V31 temp. AArch64 PCS §5.1.2 |
| `XmmYmm` | 128/256 | 16 (XMM0–15) | N/A | XMM0–5 | XMM6–15 (Win only) | Linux: all caller-saved. Intel SDM §3.2.1 |
| `Zmm` | 512 | 32 (ZMM0–31) | N/A | ZMM0–15 | none | All caller-saved Linux. ZMM16–31 new in AVX-512 |
| `Avx512K` | 64 (mask) | 8 (k0–k7) | N/A | k1–k7 | none | **k0 reserved all-ones; unallocatable.** Intel SDM §2.6.3 |
| `SveZ` | VL-bit (≥128) | 32 (Z0–Z31) | N/A | Z0–Z7 | Z8–Z23 (full VL); Z24–Z31 temp | ARMv9 ARM §A2.6 |
| `SvePred` | VL/8-bit | 16 (P0–P15) | N/A | P0–P3 | P4–P15 | ARMv9 ARM §A2.6 |
| `RvvV` | VLEN-bit | 32 (v0–v31) | see §1.1a | v0–v7 | v8–v23; v24–v31 temp | RVV psABI draft §3 [UNVERIFIED] |
| `RvvMask` | VLEN/8-bit | 1 logical (v0) | N/A | v0 | — | Single mask reg; vmv1r emitted before each masked op |
| `WarpReg` | 32 (.b32/.f32) | unlimited (virtual) | N/A | caller (CUDA) | none | PTX virtual; no physical callee concept |

**§1.1a — RVV LMUL grouping constraints (C1 §3.5):**

| vlmul[2:0] | LMUL | Group-start constraint | Reserved? |
|---|---|---|---|
| 000 | m1 | any vN | no |
| 001 | m2 | N mod 2 == 0 | no |
| 010 | m4 | N mod 4 == 0 | no |
| 011 | m8 | N mod 8 == 0 | no |
| **100** | **—** | **—** | **YES — reserved hole; must never emit** |
| 101 | mf8 | any vN | no [UNVERIFIED bits] |
| 110 | mf4 | any vN | no [UNVERIFIED bits] |
| 111 | mf2 | any vN | no [UNVERIFIED bits] |

The regalloc must never produce vlmul=100. Any LMUL enum translation table must
skip index 4 (`RVV spec §3.4.2`).

---

### 1.2 `MachOpcode` Additions

Grouped by backend. Columns: `Variant` | `Bytes` (encoding byte count) |
`Operands` (D=dest, S1/S2/S3=sources, K=k-mask, M=mem, I=imm, P=pred, vm=RVV mask bit) |
`Pred role` | `Fault class`.

**NEON / AArch64 ASIMD**

| Variant | Bytes | Operands | Pred role | Fault class |
|---|---|---|---|---|
| `NeonFaddF32x4` | 4 | D,S1,S2 | None | None |
| `NeonFmulF32x4` | 4 | D,S1,S2 | None | None |
| `NeonFmlaF32x4` | 4 | D,S1,S2 | None | None (D=acc) |
| `NeonFsubF32x4` | 4 | D,S1,S2 | None | None |
| `NeonFdivF32x4` | 4 | D,S1,S2 | None | FP divide |
| `NeonFabsF32x4` | 4 | D,S1 | None | None |
| `NeonFnegF32x4` | 4 | D,S1 | None | None |
| `NeonFsqrtF32x4` | 4 | D,S1 | None | FP sqrt |
| `NeonFcmgtF32x4` | 4 | D,S1,S2 | None | None (mask out) |
| `NeonBslQ` | 4 | D,S1,S2,S3 | None | None (synth mask) |
| `NeonFaddpF32x4` | 4 | D,S1,S2 | None | None |
| `NeonFaddpScalar` | 4 | D,S1 | None | None |
| `NeonVld1qF32` | 4 | D,M | None | Load fault |
| `NeonVst1qF32` | 4 | M,S1 | None | Store fault |
| `NeonVgetqLaneF32` | 4 | D,S1,I | None | None |
| `NeonVsetqLaneF32` | 4 | D,S1,I,S2 | None | None |
| `NeonVaddvqF32` | 4 | D,S1 | None | None |
| `NeonVmaxvqF32` | 4 | D,S1 | None | None |
| `NeonVdupqNF32` | 4 | D,S1 | None | None (splat) |
| `NeonVqtbl1qU8` | 4 | D,S1,S2 | None | None |
| `NeonVzip1qF32` | 4 | D,S1,S2 | None | None |
| `NeonFmaxnmF32x4` | 4 | D,S1,S2 | None | None (IEEE minimumNumber) |
| `NeonFminnmF32x4` | 4 | D,S1,S2 | None | None |
| `NeonFmaxF32x4` | 4 | D,S1,S2 | None | None |
| `NeonFminF32x4` | 4 | D,S1,S2 | None | None |

**x86 SSE/AVX2**

| Variant | Bytes | Operands | Pred role | Fault class |
|---|---|---|---|---|
| `SseAddpsXmm` | 4 | D,S1,S2 | None | None |
| `SseMulpsXmm` | 4 | D,S1,S2 | None | None |
| `SseFmadd213psXmm` | 5 | D,S1,S2 | None | None |
| `SseSqrtpsXmm` | 4 | D,S1 | None | FP sqrt |
| `SseMovapsXmm` | 4 | D,S1 | None | None |
| `SseVaddpsYmm` | 4 | D,S1,S2 | None | None (VEX) |
| `SseVmulpsYmm` | 4 | D,S1,S2 | None | None |
| `SseVfmadd213psYmm` | 5 | D,S1,S2 | None | None |
| `SseVgatherdpsYmm` | 5 | D,S1,S2,K | Merge | Load; mask clears per lane |
| `Avx2VpermdYmm` | 5 | D,S1,S2 | None | None |
| `Avx2VpshufbYmm` | 5 | D,S1,S2 | None | None |
| `Avx2VblendvpsYmm` | 5 | D,S1,S2,S3 | None (S3=mask) | None |
| `Avx2VcmppsYmm` | 5 | D,S1,S2,I | None | None |
| `Avx2VbroadcastssYmm` | 4 | D,M | None | Load |

**x86 AVX-512**

| Variant | Bytes | Operands | Pred role | Fault class |
|---|---|---|---|---|
| `EvexVaddpsZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVsubpsZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVmulpsZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVdivpsZmm` | 6 | D,S1,S2,K | Merge or Zero | FP divide |
| `EvexVfmadd213psZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVfmadd132psZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVfmadd231psZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVfmadd213pdZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVsqrtpsZmm` | 6 | D,S1,K | Merge or Zero | FP sqrt |
| `EvexVmovapsZmm` | 6 | D,S1,K | Merge or Zero | None |
| `EvexVgatherdpsZmm` | 6 | D,M,K | Merge (k clears) | Load fault |
| `EvexVscatterdpsZmm` | 6 | M,S1,K | None (k required) | Store fault |
| `EvexVpscatterddZmm` | 6 | M,S1,K | None | Store fault |
| `EvexVpscatterdqZmm` | 6 | M,S1,K | None | Store fault |
| `EvexVpermt2psZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVbroadcastssZmm` | 6 | D,S1,K | Merge or Zero | None |
| `EvexVcmppsZmm` | 6 | K,S1,S2,I | Zero (result→k) | None |
| `EvexKandK` | 3 | K,K,K | None | None |
| `EvexKorK` | 3 | K,K,K | None | None |
| `EvexKnotK` | 3 | K,K | None | None |
| `EvexKmovwK` | 3 | K,S1 | None | None |
| `EvexVmaxpsZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVminpsZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVpadddZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVpxordZmm` | 6 | D,S1,S2,K | Merge or Zero | None |
| `EvexVaddpdZmm` | 6 | D,S1,S2,K | Merge or Zero | None |

**AArch64 SVE2**

| Variant | Bytes | Operands | Pred role | Fault class |
|---|---|---|---|---|
| `SveFaddS` | 4 | D,P,S1,S2 | Governed /M | None |
| `SveFmulS` | 4 | D,P,S1,S2 | Governed /M | None |
| `SveFmlaS` | 4 | D,P,S1,S2 | Governed /M | None |
| `SveFsubS` | 4 | D,P,S1,S2 | Governed /M | None |
| `SveFdivS` | 4 | D,P,S1,S2 | Governed /M | FP divide |
| `SveFabsS` | 4 | D,P,S1 | Governed /M | None |
| `SveFnegS` | 4 | D,P,S1 | Governed /M | None |
| `SveFsqrtS` | 4 | D,P,S1 | Governed /M | FP sqrt |
| `SveFcmpgtS` | 4 | K,P,S1,S2 | Governed /Z | None |
| `SveFmaxnmS` | 4 | D,P,S1,S2 | Governed /M | None |
| `SveFminnmS` | 4 | D,P,S1,S2 | Governed /M | None |
| `SvePtrue` | 4 | P,I | None | None (pred pattern) |
| `SveWhilelt` | 4 | P,S1,S2 | None | None |
| `SveWhilelo` | 4 | P,S1,S2 | None | None |
| `SveLd1wGather` | 4 | D,P,M,Z | Governed /Z | Load fault |
| `SveSt1wScatter` | 4 | M,P,Z,S1 | Governed | Store fault |
| `SveLd1wContiguous` | 4 | D,P,M | Governed /Z | Load fault |
| `SveSt1wContiguous` | 4 | M,P,S1 | Governed | Store fault |
| `SveIncd` | 4 | D,I | None | None |
| `SveCntw` | 4 | D | None | None (reads VLENB) |
| `SveIndex` | 4 | D,S1,S2 | None | None |
| `SveSel` | 4 | D,P,S1,S2 | Governed | None |
| `SveCompact` | 4 | D,P,S1 | Governed | None |
| `SvePtest` | 4 | P,P | None | None |

**RVV 1.0**

| Variant | Bytes | Operands | Pred role | Fault class |
|---|---|---|---|---|
| `RvvVsetvli` | 4 | D,S1,I | None | None |
| `RvvVsetivli` | 4 | D,I,I | None | None |
| `RvvVfaddVv` | 4 | D,S1,S2,vm | Masked (vm=0) | None |
| `RvvVfsubVv` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfmulVv` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfdivVv` | 4 | D,S1,S2,vm | Masked | FP divide |
| `RvvVfmaccVv` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfnmaccVv` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfmvVf` | 4 | D,S1 | None | None (splat) |
| `RvvVlwV` | 4 | D,M,vm | Masked | Load fault |
| `RvvVswV` | 4 | M,S1,vm | Masked | Store fault |
| `RvvVluxeiV` | 4 | D,M,S1,vm | Masked | Load (indexed) |
| `RvvVsuxeiV` | 4 | M,S1,S2,vm | Masked | Store (indexed) |
| `RvvVmv1r` | 4 | D,S1 | None | None (mask copy) |
| `RvvVmseqVv` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfredosumVs` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfredmaxVs` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfmaxVv` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVfminVv` | 4 | D,S1,S2,vm | Masked | None |
| `RvvVrgatherVv` | 4 | D,S1,S2,vm | Masked | None |

**PTX / CUDA**

| Variant | Bytes | Operands | Pred role | Fault class |
|---|---|---|---|---|
| `PtxAddF32` | text | D,S1,S2 | None | None |
| `PtxMulF32` | text | D,S1,S2 | None | None |
| `PtxFmaF32` | text | D,S1,S2,S3 | None | None |
| `PtxLdGlobalF32` | text | D,M | None | Load |
| `PtxStGlobalF32` | text | M,S1 | None | Store |
| `PtxSetp` | text | K,S1,S2 | None | None |
| `PtxSelp` | text | D,S1,S2,K | None | None |
| `PtxWarpShuffle` | text | D,S1,I | None | None |
| `PtxBarSync` | text | I | None | None |
| `PtxMmaM16N8K16` | text | D×4,S1×8,S2×4,S3×4 | None | None (tensor core) |

**SPIR-V / Vulkan**

| Variant | SPIR-V words | Operands | Pred role | Fault class |
|---|---|---|---|---|
| `SpvOpFAdd` | 5 | result-id,S1,S2 | None | None |
| `SpvOpFMul` | 5 | result-id,S1,S2 | None | None |
| `SpvOpFma` | 6 | result-id,S1,S2,S3 | None | None (GLSL ext) |
| `SpvOpLoad` | 4 | result-id,ptr | None | Load |
| `SpvOpStore` | 3 | ptr,S1 | None | Store |
| `SpvOpSelect` | 6 | result-id,K,S1,S2 | None | None |
| `SpvOpDot` | 5 | result-id,S1,S2 | None | None |
| `SpvOpGroupFAdd` | 6 | result-id,scope,S1 | None | None |
| `SpvOpGroupFMax` | 6 | result-id,scope,S1 | None | None |
| `SpvOpCoopMat` | varies | D,S1,S2 | None | None (KHR ext) |
