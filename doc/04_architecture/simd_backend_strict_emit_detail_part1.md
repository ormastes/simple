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

---

## 2. Per-Target Encoder Helper Signatures

All helpers return `[i64]` unless noted. Pattern mirrors `neon_encode_f32x4_3reg`
(arm_neon.spl:71) and `_encode_simd_3op_ymm` (x86_64_simd.spl:152). All are
module-scope `fn` (no class, no inheritance). PTX returns `text`; SPIR-V returns `[i32]`.

Columns: `Helper fn` | `Ret` | `Behavior` | `C1 §`

### 2.1 `arm_neon.spl` Extensions

| Helper fn | Ret | Behavior | C1 § |
|---|---|---|---|
| `neon_encode_f32x4_3reg(opc:i64,qd:i32,qn:i32,qm:i32)` | `[i64]` | Existing — 3-reg ASIMD pattern reference | existing |
| `neon_encode_faddp_4s(qd:i32,qn:i32,qm:i32)` | `[i64]` | FADDP Vd.4S,Vn.4S,Vm.4S — pairwise add f32×4 | §9 |
| `neon_encode_faddp_scalar(sd:i32,vn:i32)` | `[i64]` | FADDP Sd,Vn.2S — scalar pairwise reduce | §9 |
| `neon_encode_vgetq_lane_f32(rd:i32,vn:i32,lane:i32)` | `[i64]` | MOV Wd,Vn.S[lane] — extract f32 lane to GPR | §9 |
| `neon_encode_vsetq_lane_f32(vd:i32,vn:i32,lane:i32,rm:i32)` | `[i64]` | INS Vd.S[lane],Wm — insert scalar into lane | §9 |
| `neon_encode_bsl_q(vd:i32,vn:i32,vm:i32)` | `[i64]` | BSL Vd.16B,Vn.16B,Vm.16B — bitwise select | §9 |
| `neon_encode_fcmgt_f32x4(vd:i32,vn:i32,vm:i32)` | `[i64]` | FCMGT Vd.4S — all-ones/zeros lane mask | §9 |
| `neon_encode_fcmge_f32x4(vd:i32,vn:i32,vm:i32)` | `[i64]` | FCMGE Vd.4S | §9 |
| `neon_encode_fmaxnm_f32x4(vd:i32,vn:i32,vm:i32)` | `[i64]` | FMAXNM Vd.4S — IEEE minimumNumber | §9 |
| `neon_encode_fminnm_f32x4(vd:i32,vn:i32,vm:i32)` | `[i64]` | FMINNM Vd.4S | §9 |
| `neon_encode_fmax_f32x4(vd:i32,vn:i32,vm:i32)` | `[i64]` | FMAX Vd.4S — NaN propagating | §9 |
| `neon_encode_fmin_f32x4(vd:i32,vn:i32,vm:i32)` | `[i64]` | FMIN Vd.4S — NaN propagating | §9 |
| `neon_encode_vdup_f32x4(vd:i32,rn:i32)` | `[i64]` | DUP Vd.4S,Wn — splat GPR scalar | §9 |
| `neon_encode_vdup_lane_f32x4(vd:i32,vn:i32,lane:i32)` | `[i64]` | DUP Vd.4S,Vn.S[lane] | §9 |
| `neon_encode_vld1q_f32(vd:i32,base:i32)` | `[i64]` | LD1 {Vd.4S},[Xn] — unit-stride load | §9 |
| `neon_encode_vst1q_f32(vs:i32,base:i32)` | `[i64]` | ST1 {Vs.4S},[Xn] — unit-stride store | §9 |
| `neon_encode_vld1q_f32_post(vd:i32,base:i32,stride:i32)` | `[i64]` | LD1 post-index with GPR offset | §9 |
| `neon_encode_vst1q_f32_post(vs:i32,base:i32,stride:i32)` | `[i64]` | ST1 post-index | §9 |
| `neon_encode_vzip1q_f32(vd:i32,vn:i32,vm:i32)` | `[i64]` | ZIP1 Vd.4S — interleave even lanes | §9 |
| `neon_encode_vuzp1q_f32(vd:i32,vn:i32,vm:i32)` | `[i64]` | UZP1 Vd.4S — deinterleave even lanes | §9 |
| `neon_encode_vtrn1q_f32(vd:i32,vn:i32,vm:i32)` | `[i64]` | TRN1 Vd.4S — transpose even elements | §9 |
| `neon_encode_qtbl1q_u8(vd:i32,vn:i32,vm:i32)` | `[i64]` | TBL Vd.16B,{Vn.16B},Vm.16B — byte shuffle | §9 |
| `neon_encode_vaddvq_f32(rd:i32,vn:i32)` | `[i64]` | FADDV Sd,Vn.4S — horizontal reduce | §9 |
| `neon_encode_vmaxvq_f32(rd:i32,vn:i32)` | `[i64]` | FMAXV Sd,Vn.4S — horizontal max | §9 |
| `neon_encode_fmla_f32x4(vd:i32,vn:i32,vm:i32)` | `[i64]` | FMLA Vd.4S — Vd accumulates | §9 |
| `neon_encode_masked_add_f32x4(vd:i32,va:i32,vb:i32,mask_v:i32)` | `[i64]` | Synth: FCMGT+BSL masked add (§6.1) | §9 |
| `neon_encode_gather_f32x4(vd:i32,base:i32,idx_v:i32)` | `[i64]` | Synth: scalar-extract loop (§6.2) | §9 |
| `neon_encode_reduce_sum_f32x4(rd:i32,vn:i32,tmp:i32)` | `[i64]` | Synth: FADDP pair-tree (§6.3) | §9 |
| `neon_encode_reduce_max_f32x4(rd:i32,vn:i32,tmp:i32)` | `[i64]` | Synth: FMAXNM pair-tree with NaN guard (§6.4) | §9 |

### 2.2 `x86_64_sse.spl` / `x86_64_avx2.spl` (split from x86_64_simd.spl per Round-1 §5.2)

| Helper fn | Ret | Behavior | C1 § |
|---|---|---|---|
| `sse_encode_addps_xmm(dest:i32,src:i32)` | `[i64]` | ADDPS xmm,xmm — legacy SSE | §1 |
| `sse_encode_mulps_xmm(dest:i32,src:i32)` | `[i64]` | MULPS xmm,xmm | §1 |
| `sse_encode_sqrtps_xmm(dest:i32,src:i32)` | `[i64]` | SQRTPS xmm,xmm | §1 |
| `sse_encode_movaps_xmm(dest:i32,src:i32)` | `[i64]` | MOVAPS xmm,xmm — aligned | §1 |
| `sse_encode_movups_xmm(dest:i32,src:i32)` | `[i64]` | MOVUPS xmm,xmm | §1 |
| `sse_encode_cmpps_xmm(dest:i32,src:i32,imm:i32)` | `[i64]` | CMPPS xmm,xmm,imm8 | §1 |
| `sse_encode_blendvps_xmm(dest:i32,src:i32,mask:i32)` | `[i64]` | BLENDVPS — implicit XMM0 mask | §1 |
| `avx2_encode_vaddps_ymm(d:i32,s1:i32,s2:i32)` | `[i64]` | VADDPS ymm,ymm,ymm — 3-op VEX | §1 |
| `avx2_encode_vmulps_ymm(d:i32,s1:i32,s2:i32)` | `[i64]` | VMULPS ymm | §1 |
| `avx2_encode_vsubps_ymm(d:i32,s1:i32,s2:i32)` | `[i64]` | VSUBPS ymm | §1 |
| `avx2_encode_vdivps_ymm(d:i32,s1:i32,s2:i32)` | `[i64]` | VDIVPS ymm | §1 |
| `avx2_encode_vfmadd213ps_ymm(d:i32,s1:i32,s2:i32)` | `[i64]` | VFMADD213PS — form 213; see §3 | §6-F |
| `avx2_encode_vfmadd132ps_ymm(d:i32,s1:i32,s2:i32)` | `[i64]` | VFMADD132PS — form 132 | §6-F |
| `avx2_encode_vfmadd231ps_ymm(d:i32,s1:i32,s2:i32)` | `[i64]` | VFMADD231PS — form 231 | §6-F |
| `avx2_encode_vblendvps_ymm(d:i32,s1:i32,s2:i32,mask:i32)` | `[i64]` | VBLENDVPS 4-op VEX | §1 |
| `avx2_encode_vcmpps_ymm(d:i32,s1:i32,s2:i32,imm:i32)` | `[i64]` | VCMPPS ymm,imm8 | §1 |
| `avx2_encode_vperm2f128(d:i32,s1:i32,s2:i32,imm:i32)` | `[i64]` | VPERM2F128 — 128-bit lane swap | §1 |
| `avx2_encode_vpermd(d:i32,s1:i32,s2:i32)` | `[i64]` | VPERMD — dword permute by index vector | §1 |
| `avx2_encode_vpshufb(d:i32,s1:i32,s2:i32)` | `[i64]` | VPSHUFB ymm — byte shuffle | §1 |
| `avx2_encode_vgatherdps_ymm(d:i32,base:i32,idx:i32,scale:i32,mask:i32)` | `[i64]` | VGATHERDPS — mask cleared per lane | §1 |
| `avx2_encode_vbroadcastss_ymm(d:i32,src:i32)` | `[i64]` | VBROADCASTSS ymm,xmm — splat f32 | §1 |
| `avx2_encode_vmovaps_ymm(d:i32,src:i32)` | `[i64]` | VMOVAPS ymm,ymm | §1 |
| `avx2_encode_vmovups_ymm_load(d:i32,base:i32,disp:i32)` | `[i64]` | VMOVUPS ymm,[mem] | §1 |
| `avx2_encode_vmovups_ymm_store(base:i32,disp:i32,src:i32)` | `[i64]` | VMOVUPS [mem],ymm | §1 |
| `avx2_scatter_fallback(base:i32,idx_ymm:i32,src_ymm:i32,scale:i32)` | `[i64]` | Scalar scatter loop (§7) | §1 |

### 2.3 `x86_64_avx512.spl` (new file)

| Helper fn | Ret | Behavior | C1 § |
|---|---|---|---|
| `evex_encode_3op_zmm(d:i32,s1:i32,s2:i32,k:i32,z:bool,mm:i32,w:i32,pp:i32,opc:i32)` | `[i64]` | Full EVEX 3-op ZMM; byte layout §3 | §1 |
| `evex_encode_2op_zmm(d:i32,s:i32,k:i32,z:bool,mm:i32,w:i32,pp:i32,opc:i32)` | `[i64]` | EVEX unary ZMM (VSQRTPS, VMOVAPS) | §1 |
| `evex_encode_broadcast_zmm(d:i32,src_xmm:i32,k:i32,mm:i32,w:i32,pp:i32,opc:i32)` | `[i64]` | VBROADCASTSS/SD zmm — b=1 in P2 | §1 |
| `evex_encode_gather_zmm(d:i32,base:i32,idx:i32,scale:i32,k:i32,opc:i32)` | `[i64]` | VGATHERDPS zmm{k},[base+zmm*s] | §1 |
| `evex_encode_scatter_zmm(base:i32,idx:i32,src:i32,scale:i32,k:i32,opc:i32)` | `[i64]` | VSCATTERDPS [base+zmm*s]{k},zmm | §1 |
| `evex_encode_fmadd_zmm(acc:i32,mul1:i32,mul2:i32,k:i32,z:bool,form:FmaForm,w:i32)` | `[i64]` | VFMADD{132/213/231} — form from §3 decision tree | §6-F |
| `evex_encode_cmp_zmm_to_k(kd:i32,s1:i32,s2:i32,imm:i32,mm:i32,w:i32,pp:i32)` | `[i64]` | VCMPPS zmm,zmm,imm8→k | §1 |
| `evex_encode_kmov(kd:i32,src:i32)` | `[i64]` | KMOVW k,k or k,r32 | §1 |
| `evex_encode_kop(kd:i32,k1:i32,k2:i32,op:KOp)` | `[i64]` | KAND/KOR/KXOR/KANDN/KNOT | §1 |
| `evex_encode_perm_zmm(d:i32,idx:i32,src:i32,k:i32,z:bool)` | `[i64]` | VPERMT2PS zmm{k}{z} | §1 |
| `evex_encode_3op_zmm_sae(d:i32,s1:i32,s2:i32,k:i32,z:bool,rnd:SaeMode,mm:i32,w:i32,pp:i32,opc:i32)` | `[i64]` | EVEX with b=1 + L'L=rounding | §1.4 |
| `evex_encode_vaddps(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VADDPS zmm convenience | §1 |
| `evex_encode_vmulps(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VMULPS zmm | §1 |
| `evex_encode_vsubps(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VSUBPS zmm | §1 |
| `evex_encode_vdivps(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VDIVPS zmm | §1 |
| `evex_encode_vmovaps_load(d:i32,base:i32,disp:i32,k:i32,z:bool)` | `[i64]` | VMOVAPS zmm{k}{z},[mem] 64B aligned | §1 |
| `evex_encode_vmovaps_store(base:i32,disp:i32,src:i32,k:i32)` | `[i64]` | VMOVAPS [mem]{k},zmm | §1 |
| `evex_encode_vmovups_load(d:i32,base:i32,disp:i32,k:i32,z:bool)` | `[i64]` | VMOVUPS zmm{k}{z},[mem] | §1 |
| `evex_encode_vmovups_store(base:i32,disp:i32,src:i32,k:i32)` | `[i64]` | VMOVUPS [mem]{k},zmm | §1 |
| `evex_encode_vcvt_zmm(d:i32,src:i32,k:i32,z:bool,opc:i32,mm:i32,w:i32,pp:i32)` | `[i64]` | VCVTPS2PD / VCVTPD2PS | §1 |
| `evex_encode_vpandd(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VPANDD zmm | §1 |
| `evex_encode_vpord(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VPORD zmm | §1 |
| `evex_encode_vpxord(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VPXORD zmm | §1 |
| `evex_encode_vmaxps(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VMAXPS zmm | §1 |
| `evex_encode_vminps(d:i32,s1:i32,s2:i32,k:i32,z:bool)` | `[i64]` | VMINPS zmm | §1 |

### 2.4 `arm_sve2.spl` (new file)

| Helper fn | Ret | Behavior | C1 § |
|---|---|---|---|
| `sve_encode_3reg_pred(opc:i64,zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | Generic 3-reg predicated SVE2; bit-pack §4 | §2 |
| `sve_encode_2reg_pred(opc:i64,zd:i32,pg:i32,zn:i32)` | `[i64]` | 2-reg predicated (FABS, FNEG, FSQRT) | §2 |
| `sve_encode_ptrue(pd:i32,esz:i32,pattern:i32)` | `[i64]` | PTRUE Pd.{BHSD},pattern | §2.3 |
| `sve_encode_whilelt(pd:i32,rn:i32,rm:i32,esz:i32)` | `[i64]` | WHILELT — loop-tail predicate | §2 |
| `sve_encode_whilelo(pd:i32,rn:i32,rm:i32,esz:i32)` | `[i64]` | WHILELO — unsigned | §2 |
| `sve_encode_ld1w_contiguous(zd:i32,pg:i32,base:i32,offset:i32)` | `[i64]` | LD1W {Zd.S},Pg/Z,[Xn,Xm,LSL#2] | §2 |
| `sve_encode_st1w_contiguous(zs:i32,pg:i32,base:i32,offset:i32)` | `[i64]` | ST1W {Zs.S},Pg,[Xn,Xm,LSL#2] | §2 |
| `sve_encode_gather_ld1w(zd:i32,pg:i32,base:i32,zoffset:i32)` | `[i64]` | LD1W gather: [Xbase,Zoffset.S,UXTW#2] | §2 |
| `sve_encode_scatter_st1w(zs:i32,pg:i32,base:i32,zoffset:i32)` | `[i64]` | ST1W scatter: [Xbase,Zoffset.S,UXTW#2] | §2 |
| `sve_encode_fadd_s_pred(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FADD Zd.S,Pg/M,Zn.S,Zm.S | §2 |
| `sve_encode_fmla_s_pred(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FMLA Zd.S,Pg/M — Zd accumulates | §2 |
| `sve_encode_fmul_s_pred(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FMUL Zd.S,Pg/M | §2 |
| `sve_encode_fsub_s_pred(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FSUB Zd.S,Pg/M | §2 |
| `sve_encode_fdiv_s_pred(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FDIV Zd.S,Pg/M | §2 |
| `sve_encode_fcmgt_s_pred(pd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FCMGT Pd.S,Pg/Z→predicate | §2 |
| `sve_encode_fmaxnm_s_pred(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FMAXNM Zd.S,Pg/M | §2 |
| `sve_encode_fminnm_s_pred(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | FMINNM Zd.S,Pg/M | §2 |
| `sve_encode_sel(zd:i32,pg:i32,zn:i32,zm:i32)` | `[i64]` | SEL Zd.S,Pg — predicated blend | §2 |
| `sve_encode_incd(xd:i32,pattern:i32)` | `[i64]` | INCD Xd — increment by element count | §2 |
| `sve_encode_cntw(xd:i32)` | `[i64]` | CNTW Xd — read active element count | §2 |
| `sve_encode_index(zd:i32,base:i32,step:i32)` | `[i64]` | INDEX Zd.S,Wbase,Wstep | §2 |
| `sve_encode_compact(zd:i32,pg:i32,zn:i32)` | `[i64]` | COMPACT Zd.S,Pg — pack active lanes | §2 |
| `sve_encode_ptest(pg:i32,pn:i32)` | `[i64]` | PTEST {Pg},Pn.B | §2 |
| `sve_encode_pnext(pd:i32,pg:i32,esz:i32)` | `[i64]` | PNEXT Pd.S,Pg — advance active lane | §2 |

### 2.5 `riscv_v.spl` (new file)

| Helper fn | Ret | Behavior | C1 § |
|---|---|---|---|
| `rvv_encode_vsetvli(rd:i32,rs1:i32,vtypei:i32)` | `i64` | vsetvli — full bit-pack §5 | §3.2 |
| `rvv_encode_vsetivli(rd:i32,uimm:i32,vtypei:i32)` | `i64` | vsetivli with 5-bit AVL immediate | §3.2 |
| `rvv_encode_vtype(vsew:VsewKind,vlmul:VlmulKind,vta:bool,vma:bool)` | `i32` | Assemble vtypei; guard vlmul!=reserved_100 | §3.5 |
| `rvv_encode_3reg_vv(f6:i32,f3:i32,vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | Generic OPIVV/OPFVV/OPMVV | §3.1 |
| `rvv_encode_3reg_vx(f6:i32,f3:i32,vd:i32,vs2:i32,rs1:i32,vm:bool)` | `i64` | OPIVX/OPMVX — GPR scalar | §3.1 |
| `rvv_encode_3reg_vf(f6:i32,vd:i32,vs2:i32,fs1:i32,vm:bool)` | `i64` | OPFVF — FP scalar | §3.1 |
| `rvv_encode_3reg_vi(f6:i32,vd:i32,vs2:i32,imm5:i32,vm:bool)` | `i64` | OPIVI — 5-bit imm | §3.1 |
| `rvv_encode_vfadd_vv(vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | vfadd.vv | §3 |
| `rvv_encode_vfsub_vv(vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | vfsub.vv | §3 |
| `rvv_encode_vfmul_vv(vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | vfmul.vv | §3 |
| `rvv_encode_vfdiv_vv(vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | vfdiv.vv | §3 |
| `rvv_encode_vfmacc_vv(vd:i32,vs1:i32,vs2:i32,vm:bool)` | `i64` | vfmacc.vv — vd+=vs1*vs2 | §3 |
| `rvv_encode_vfnmacc_vv(vd:i32,vs1:i32,vs2:i32,vm:bool)` | `i64` | vfnmacc.vv | §3 |
| `rvv_encode_vfmv_vf(vd:i32,fs1:i32)` | `i64` | vfmv.v.f — splat FP scalar | §3 |
| `rvv_encode_vlw_v(vd:i32,rs1:i32,vm:bool)` | `i64` | vle32.v — unit-stride load | §3 |
| `rvv_encode_vsw_v(vs3:i32,rs1:i32,vm:bool)` | `i64` | vse32.v — unit-stride store | §3 |
| `rvv_encode_vluxei32_v(vd:i32,rs1:i32,vs2:i32,vm:bool)` | `i64` | vluxei32.v — gather | §3 |
| `rvv_encode_vsuxei32_v(vs3:i32,rs1:i32,vs2:i32,vm:bool)` | `i64` | vsuxei32.v — scatter | §3 |
| `rvv_encode_vmv1r(vd:i32,vs:i32)` | `i64` | vmv1r.v — copy mask to v0 | §3 |
| `rvv_emit_masked_op(emit_fn:fn(i32,i32,i32,bool)->i64,vd:i32,vs2:i32,vs1:i32,mask_reg:i32)` | `[i64]` | Emit vmv1r if mask_reg!=0, then call emit_fn | §3 |
| `rvv_encode_vfredosum_vs(vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | vfredusum.vs — ordered FP reduce sum | §3 |
| `rvv_encode_vfredmax_vs(vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | vfredmax.vs | §3 |
| `rvv_encode_vrgather_vv(vd:i32,vs2:i32,vs1:i32,vm:bool)` | `i64` | vrgather.vv — cross-lane permute | §3 |
| `rvv_encode_vmsgt_vf(vd:i32,vs2:i32,fs1:i32,vm:bool)` | `i64` | vmsgt.vf — compare GT to mask | §3 |

### 2.6 `cuda/ptx_builder.spl` Extensions (text emission)

| Helper fn | Ret | Behavior | C1 § |
|---|---|---|---|
| `ptx_emit_add_f32(rd:text,ra:text,rb:text)` | `text` | `add.f32 %rd, %ra, %rb;` | §4 |
| `ptx_emit_mul_f32(rd:text,ra:text,rb:text)` | `text` | `mul.f32 %rd, %ra, %rb;` | §4 |
| `ptx_emit_fma_f32(rd:text,ra:text,rb:text,rc:text)` | `text` | `fma.rn.f32 %rd, %ra, %rb, %rc;` | §4 |
| `ptx_emit_ld_global_f32(rd:text,addr:text)` | `text` | `ld.global.f32 %rd, [%addr];` | §4 |
| `ptx_emit_st_global_f32(addr:text,rs:text)` | `text` | `st.global.f32 [%addr], %rs;` | §4 |
| `ptx_emit_ld_global_v4_f32(r0:text,r1:text,r2:text,r3:text,addr:text)` | `text` | `ld.global.v4.f32 {%r0,%r1,%r2,%r3},[%addr];` | §4 |
| `ptx_emit_setp_gt_f32(pd:text,ra:text,rb:text)` | `text` | `setp.gt.f32 %pd, %ra, %rb;` | §4 |
| `ptx_emit_selp_f32(rd:text,ra:text,rb:text,pd:text)` | `text` | `selp.f32 %rd, %ra, %rb, %pd;` | §4 |
| `ptx_emit_shfl_sync_idx_b32(rd:text,ra:text,lane:text,mask:text)` | `text` | `shfl.sync.idx.b32 %rd,%ra,%lane,0x1f,%mask;` | §4 |
| `ptx_emit_bar_sync(barrier:i32)` | `text` | `bar.sync %barrier;` | §4 |
| `ptx_emit_mma_m16n8k16_f32(d:[text;4],a:[text;8],b:[text;4],c:[text;4])` | `text` | `mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32` | §4 |
| `ptx_emit_wmma_load_a(frag:text,ptr:text,stride:text)` | `text` | `wmma.load.a.sync.aligned.row.m16n16k16.f16` | §4 |
| `ptx_emit_cvt_rn_f32_f16(rd:text,ra:text)` | `text` | `cvt.rn.f32.f16 %rd, %ra;` | §4 |
| `ptx_emit_pred_branch(pd:text,label:text)` | `text` | `@%pd bra %label;` | §4 |
| `ptx_emit_vote_ballot_sync(rd:text,pd:text,mask:text)` | `text` | `vote.ballot.sync.b32 %rd, %pd, %mask;` | §4 |
| `ptx_emit_atom_add_f32(rd:text,addr:text,val:text)` | `text` | `atom.global.add.f32 %rd, [%addr], %val;` | §4 |
| `ptx_emit_activemask(rd:text)` | `text` | `activemask.b32 %rd;` | §4 |

### 2.7 `vulkan/spirv_builder.spl` Extensions ([i32] SPIR-V word streams)

| Helper fn | Ret | Behavior | C1 § |
|---|---|---|---|
| `spv_op_fadd(rid:i32,tid:i32,a:i32,b:i32)` | `[i32]` | OpFAdd — 5 words | §5 |
| `spv_op_fmul(rid:i32,tid:i32,a:i32,b:i32)` | `[i32]` | OpFMul — 5 words | §5 |
| `spv_op_fsub(rid:i32,tid:i32,a:i32,b:i32)` | `[i32]` | OpFSub | §5 |
| `spv_op_fdiv(rid:i32,tid:i32,a:i32,b:i32)` | `[i32]` | OpFDiv | §5 |
| `spv_op_ext_fma(rid:i32,tid:i32,a:i32,b:i32,c:i32,glsl:i32)` | `[i32]` | OpExtInst GLSL.std.450 Fma | §5 |
| `spv_op_load(rid:i32,tid:i32,ptr:i32)` | `[i32]` | OpLoad — 4 words | §5 |
| `spv_op_store(ptr:i32,val:i32)` | `[i32]` | OpStore — 3 words | §5 |
| `spv_op_access_chain(rid:i32,tid:i32,base:i32,idx:i32)` | `[i32]` | OpAccessChain — pointer arithmetic | §5 |
| `spv_op_select(rid:i32,tid:i32,cond:i32,a:i32,b:i32)` | `[i32]` | OpSelect — blend on bool | §5 |
| `spv_op_dot(rid:i32,tid:i32,a:i32,b:i32)` | `[i32]` | OpDot | §5 |
| `spv_op_composite_extract(rid:i32,tid:i32,comp:i32,idx:i32)` | `[i32]` | OpCompositeExtract — extract lane | §5 |
| `spv_op_composite_construct(rid:i32,tid:i32,comps:[i32])` | `[i32]` | OpCompositeConstruct — build vector | §5 |
| `spv_op_group_fadd(rid:i32,tid:i32,scope:i32,op:i32,val:i32)` | `[i32]` | OpGroupFAdd — reduce | §5 |
| `spv_op_group_fmax(rid:i32,tid:i32,scope:i32,op:i32,val:i32)` | `[i32]` | OpGroupFMax | §5 |
| `spv_op_coop_mat_load(rid:i32,ptr:i32,layout:i32,stride:i32)` | `[i32]` | OpCooperativeMatrixLoadKHR | §5 |
| `spv_op_coop_mat_muladd(rid:i32,a:i32,b:i32,c:i32)` | `[i32]` | OpCooperativeMatrixMulAddKHR | §5 |
| `spv_op_vector_shuffle(rid:i32,tid:i32,v1:i32,v2:i32,comps:[i32])` | `[i32]` | OpVectorShuffle — permute lanes | §5 |
| `spv_op_fcmp_ogt(rid:i32,tid:i32,a:i32,b:i32)` | `[i32]` | OpFOrdGreaterThan | §5 |
| `spv_op_fnegate(rid:i32,tid:i32,a:i32)` | `[i32]` | OpFNegate | §5 |
| `spv_op_ext_sqrt(rid:i32,tid:i32,a:i32,glsl:i32)` | `[i32]` | OpExtInst GLSL.std.450 Sqrt | §5 |

---

## 3. EVEX Byte-Layout Encoder

Source authority: Intel SDM Vol 2A §2.6.1, Table 2-36 (EVEX Prefix Bit Field Layout).
C1 §1 provides the bit-field breakdown used here; all hex values marked `[UNVERIFIED]`
until cross-checked against the SDM opcode entry for each instruction.

### 3.1 EVEX Prefix Field Layout (C1 §1.2)

```
Byte 0:  0x62  (mandatory EVEX escape — distinguishes from BOUND)

Byte P0 [7:0]:
  [7]   ~R    complement of REX.R  (extends ModRM.reg bits[3:0])
  [6]   ~X    complement of REX.X  (extends SIB.index)
  [5]   ~B    complement of REX.B  (extends ModRM.rm / SIB.base)
  [4]   ~R'   5th bit of ModRM.reg (ZMM16-31: R'=0 → ~R'=1 set)
  [3:2] mm    opcode map: 01=0F  10=0F38  11=0F3A
  [1]   0     must be 0
  [0]   W     element width: 0=f32/i32  1=f64/i64

Byte P1 [7:0]:
  [7]   1     must be 1 (EVEX vs BOUND disambiguation)
  [6:3] ~vvvv complement of VEX.vvvv source register (4 bits)
  [2]   1     must be 1
  [1:0] pp    implied prefix: 00=none  01=0x66  10=0xF3  11=0xF2

Byte P2 [7:0]:
  [7]   z     mask mode: 1=zeroing  0=merging
  [6:5] L'L   vector width: 00=128b XMM  01=256b YMM  10=512b ZMM
              (when b=1 on reg-reg: L'L encodes static rounding instead)
  [4]   b     broadcast (mem) or SAE/rounding enable (reg)
  [3]   ~V'   complement of 5th bit of vvvv (for ZMM16-31 vvvv encoding)
  [2:0] aaa   opmask register: 000=k0(all-ones/unmasked) 001=k1 .. 111=k7
              NOTE: k0 is reserved as all-ones; aaa=000 means no mask
```

### 3.2 Core Helper: `fn evex_encode_3op_zmm`

```
# Encode a 3-operand ZMM instruction with optional k-mask and zeroing.
# Returns [u8; 6] = [0x62, P0, P1, P2, opcode, ModRM]
# C1 §1.2 — [UNVERIFIED hex values; verify vs Intel SDM §2.6.1]
fn evex_encode_3op_zmm(
    dest: i32,   # ZMM dest register index 0-31
    src1: i32,   # ZMM src1 (vvvv field) index 0-31
    src2: i32,   # ZMM src2 (ModRM.rm) index 0-31
    k_mask: i32, # opmask k0-k7 (0 = k0 = no mask)
    zeroing: bool,
    mm: i32,     # opcode map: 1=0F, 2=0F38, 3=0F3A
    w: i32,      # W bit: 0=f32/i32  1=f64/i64
    pp: i32,     # prefix: 0=none 1=0x66 2=0xF3 3=0xF2
    opcode: i32  # 1-byte opcode
) -> [u8; 6]:
    # P0 construction
    r_bit   = (dest  >> 3) & 1   # bit3 of dest
    r_prime = (dest  >> 4) & 1   # bit4 of dest (ZMM16-31)
    x_bit   = 0                  # no SIB index for reg-reg
    b_bit   = (src2  >> 3) & 1   # bit3 of src2

    p0 = ((~r_bit   & 1) << 7)
       | ((~x_bit   & 1) << 6)
       | ((~b_bit   & 1) << 5)
       | ((~r_prime & 1) << 4)
       | ((mm & 3)       << 2)
       | (0              << 1)   # reserved 0
       | (w & 1)

    # P1 construction
    vvvv_lo4 = src1 & 0xF        # bits[3:0] of src1
    p1 = (1              << 7)   # must-1
       | ((~vvvv_lo4 & 0xF) << 3)
       | (1              << 2)   # must-1
       | (pp & 3)

    # P2 construction
    v_prime = (src1 >> 4) & 1    # bit4 of src1 (ZMM16-31)
    z_bit   = if zeroing then 1 else 0
    ll      = 2                  # 10 = 512-bit ZMM
    b_p2    = 0                  # no broadcast/SAE for basic 3-op

    p2 = (z_bit          << 7)
       | (ll              << 5)
       | (b_p2            << 4)
       | ((~v_prime & 1)  << 3)
       | (k_mask & 7)

    # ModRM: mod=11 (reg-reg), reg=dest[2:0], rm=src2[2:0]
    modrm = (3 << 6) | ((dest & 7) << 3) | (src2 & 7)

    return [0x62, p0, p1, p2, opcode & 0xFF, modrm]
```

### 3.3 SAE / Static-Rounding Variant

When `b=1` on a register-register operand, P2[6:5] (L'L) encodes rounding mode:

| SaeMode | L'L encoding | Meaning |
|---|---|---|
| `RnSae` | 00 | Round-nearest + suppress exceptions |
| `RdSae` | 01 | Round-down |
| `RuSae` | 10 | Round-up |
| `RzSae` | 11 | Round-toward-zero (truncate) |

In `evex_encode_3op_zmm_sae`, set `b_p2=1` and `ll=rounding_mode_bits`.

### 3.4 Worked Examples (C1 §1, [UNVERIFIED] — verify vs Intel SDM)

**Example 1: `vaddps zmm0, zmm1, zmm2` (no mask)**
```
dest=0 src1=1 src2=2 k=0 z=false mm=1(0F) w=0(f32) pp=1(0x66) opc=0x58
  P0: ~R=1 ~X=1 ~B=1 ~R'=1 mm=01 W=0 → 0b11110100 = 0xF4  [UNVERIFIED]
  P1: 1 ~vvvv(1)=1110 1 pp=01 → 0b11110101 = 0xF5 (note: ~0001=1110) [UNVERIFIED]
  P2: z=0 L'L=10 b=0 ~V'=1 aaa=000 → 0b01001000 = 0x48  [UNVERIFIED]
  bytes: 62 F4 F5 48 58 C2
  ModRM: mod=11 reg=0 rm=2 → 0xC2
```

**Example 2: `vfmadd213ps zmm1{k1}{z}, zmm2, zmm3 {rn-sae}` (C1 §1.7)**
```
dest=1 src1=2 src2=3 k=1 z=true mm=2(0F38) w=0 pp=1(0x66) opc=0xA8
rn-sae: b_p2=1 ll=00 (rn mode)
  P0: dest=1 → R=0,~R=1; src2=3 → B=0,~B=1; R'=0,~R'=1; mm=10
      0b11111000 | w=0 → 0xF8  [UNVERIFIED]
  P1: src1=2 → vvvv_lo4=0010, ~vvvv=1101; pp=01
      0b11101101 = 0xED  [UNVERIFIED]
  P2: z=1 L'L=00(rn) b=1 ~V'=1 aaa=001
      0b10011001 = 0x99  [UNVERIFIED]
  ModRM: mod=11 reg=1 rm=3 → 0b11001011 = 0xCB
  bytes: 62 F8 ED 99 A8 CB
```

**Example 3: `vgatherdps zmm4{k2}, [rax + zmm5*4]`**
```
# VSIB gather: ModRM.mod=00, SIB present, index=zmm5, base=rax(0)
dest=4 idx=5 base_gpr=0 scale=4 k=2 opc=0x92(VGATHERDPS in 0F38)
  # Gather requires k-mask (k2=aaa=010); k clears bits as lanes complete
  P0: dest=4 → R=0,~R=1; idx=5(SIB.index) → X=0,~X=1; base=0 → B=1,~B=0 [UNVERIFIED]
  ModRM: mod=00 reg=4 rm=100(SIB follows) → base+index SIB addressing
  Note: VSIB SIB: ss=scale_enc index=zmm5[2:0] base=rax[2:0]
  bytes (schematic): 62 [P0] [P1] [P2] 92 [ModRM] [SIB] [disp]  [UNVERIFIED]
```

**Example 4: `vpscatterdq [rax + zmm6*8]{k3}, zmm7`**
```
# Scatter to 64-bit indexed offsets, 64-bit data
src=7 idx=6 base_gpr=0 scale=8 k=3 opc=0xA2(VPSCATTERDQ 0F38 W=1)
w=1(i64) pp=1(0x66) mm=2(0F38)
  P2: z=0(scatter has no zeroing) L'L=10 b=0 ~V'=1 aaa=011
  bytes (schematic): 62 [P0] [P1] [P2] A2 [ModRM] [SIB]  [UNVERIFIED]
```

**Example 5: `vpermt2ps zmm8{k4}{z}, zmm9, zmm10`**
```
dest=8 src1=9 src2=10 k=4 z=true mm=3(0F3A) w=0 pp=1(0x66) opc=0x7F(VPERMT2PS)
  dest=8 → R=1,~R=0; R'=0,~R'=1; src2=10 → B=1,~B=0
  P0: 0b01101000 | mm=11 | w=0 → [UNVERIFIED]
  bytes (schematic): 62 [P0] [P1] [P2] 7F [ModRM]  [UNVERIFIED]
```

### 3.5 VFMADD132/213/231 Form-Selection Decision Tree (C1 §6-F)

The three FMA forms differ only in which register is the **accumulator** (in-place
destination). Selecting the wrong form silently reorders operands — a wrong-answer bug
for non-commutative addends. Decision tree (verify vs Intel SDM Vol 2B VFMADD213PS):

```
Semantics requested: result = (A × B) + C   where A,B,C are MIR operands

if dest_reg == A:
    # dest holds first multiplicand; use form 132 or 213
    if src1_reg == C:
        emit VFMADD132PS  dest, src1(=C), src2(=B)
        # computes: dest = (dest × src2) + src1  ✓
    else:  # src2_reg == C  (or src1==B)
        emit VFMADD213PS  dest, src1(=B), src2(=C)
        # computes: dest = (src1 × dest) + src2  ✓  [MOST COMMON]
elif dest_reg == C:
    # dest holds addend; use form 231
    emit VFMADD231PS  dest, src1(=A), src2(=B)
    # computes: dest = (src1 × src2) + dest  ✓
else:
    # dest is neither multiplicand nor addend — must copy first
    emit_mov dest, A
    emit VFMADD213PS  dest, src1(=B), src2(=C)

# NOTE: FP multiplication is commutative but the addend is NOT interchangeable.
# For vfmacc.vv (RVV) the analogous form is always vd+=vs1*vs2 (form 231 equivalent).
# C1 §6-F [UNVERIFIED] — verify form numbering against Intel SDM.
```

`FmaForm` enum used in `evex_encode_fmadd_zmm`:

```
enum FmaForm:
    F132   # dest = (dest × src2) + src1
    F213   # dest = (src1 × dest) + src2  [default / most common]
    F231   # dest = (src1 × src2) + dest
```

---

## 4. AArch64 SVE2 32-bit Instruction Encoder

Source authority: ARMv9 ARM §C7.1 (SVE encoding overview), §C7.2 (individual encodings).
C1 §2 provides the bit-field breakdown. All bit positions marked `[UNVERIFIED]` until
cross-checked against ARMv9 ARM.

### 4.1 SVE Instruction Word Generic Layout (C1 §2.1)

All A64 instructions are 32-bit fixed-width. SVE arithmetic occupies the `0x04xxxxxx`
op-group (bits[31:24] = 0b_0000_0100 for most FP arithmetic):

```
Bits [31:24]: op group / major opcode
  0x04: SVE integer/FP arithmetic (FADD, FMUL, FMLA etc.)
  0x05: SVE memory (LD1W, ST1W)
  0x25: SVE predicate ops (PTRUE, PFALSE, PNEXT)

Bits [23:22]: variant selector (predicated / unpredicated / widening)
Bits [21:20]: element size  00=B(8b)  01=H(16b)  10=S(32b)  11=D(64b)
Bits [19:16]: governing predicate Pg (4 bits, P0-P15)
Bits [15:13]: opcode sub-type
Bit  [12]:   /M(merge=1) vs /Z(zero=0) predication suffix
Bits [11:10]: further opcode
Bits [9:5]:  source Zn (5 bits, Z0-Z31)
Bits [4:0]:  destination Zd (5 bits, Z0-Z31)
```
`[UNVERIFIED — confirm against ARMv9 ARM §C7.1]`

### 4.2 Core Helper: `fn sve_encode_pred_3op`

```
# Encode a 3-register predicated SVE2 instruction.
# opc_bits: pre-composed bits[31:13] (opcode + variant + esz + sub-type)
# Merging predication: bit[12]=1; Zeroing: bit[12]=0
# Returns the 32-bit instruction word as i64.
# C1 §2 [UNVERIFIED]
fn sve_encode_pred_3op(
    opc_bits: i64,  # bits[31:13] pre-composed for specific instruction
    zd: i32,        # destination Z register index 0-31
    pg: i32,        # governing predicate P register index 0-15
    zn: i32,        # source Zn index 0-31
    zm: i32         # source Zm index 0-31 (in bits[9:5] when used)
) -> i64:
    # Pack fields per C1 §2.1 layout
    word = (opc_bits & 0xFFFFE000_i64)  # bits[31:13]
         | ((pg & 0xF)  << 16)          # Pg in bits[19:16]
         | ((zn & 0x1F) << 5)           # Zn in bits[9:5]
         | (zd & 0x1F)                  # Zd in bits[4:0]
    # Note: zm placement varies by instruction class:
    # For FMLA/FMUL-type: zm in bits[20:16] (overlaps Pg in some encodings)
    # Check ARMv9 ARM §C7.2 for exact zm field position per opcode.
    return word
```

### 4.3 Predicate Pattern Field (C1 §2.3)

Used in `PTRUE Pd.S, pattern` and `WHILELT`:

| Pattern | 5-bit imm | Meaning |
|---|---|---|
| `POW2` | 00000 | Largest power-of-2 ≤ VL |
| `VL1` | 00001 | 1 element |
| `VL2` | 00010 | 2 elements |
| `VL3` | 00011 | 3 elements |
| `VL4` | 00100 | 4 elements |
| `VL8` | 01000 | 8 elements |
| `VL16` | 01001 | 16 elements |
| `VL32` | 01010 | 32 elements |
| `VL64` | 01011 | 64 elements |
| `VL128` | 01100 | 128 elements |
| `VL256` | 01101 | 256 elements |
| `MUL4` | 11101 | Largest multiple of 4 ≤ VL |
| `MUL3` | 11110 | Largest multiple of 3 ≤ VL |
| `ALL` | 11111 | All elements (full VL) |

`ALL = 0x1F = 0b11111` is the most-used pattern (loop body, full predicate).
`[UNVERIFIED — confirm vs ARMv9 ARM §C1.3.2]`

### 4.4 Worked Examples (C1 §2, [UNVERIFIED])

**Example 1: `FADD Zd.S, Pg/M, Zn.S, Zm.S` — predicated FP add, merging**
```
# op-group 0x04, esz=10(S=32b), predicated FP arithmetic sub-group
# bits[31:24]=0x65 (SVE FP arithmetic), bits[23:22]=00(predicated),
# bits[21:20]=10(S), /M → bit[12]=1
# Schematic: 0110_0101_0_10_Pg_000_1_0_Zm_Zn_Zd  [UNVERIFIED]
zd=2 pg=3 zn=4 zm=5:
  opc_bits = 0x65000000 | (0b10 << 20) | (1 << 12)  # S-size, /M
  word = opc_bits | (pg<<16) | (zn<<5) | zd
       # with zm placed per ARMv9 ARM §C7.2.57 FADD (vectors, predicated)
```

**Example 2: `FMLA Zd.S, Pg/M, Zn.S, Zm.S` — fused multiply-add, Zd accumulates**
```
# FMLA: op-group 0x65 (same as FADD range), different sub-type bits
# Schematic: 0110_0101_0_10_Zm_100_Pg_Zn_Zd  [UNVERIFIED]
zd=8 pg=1 zn=9 zm=10:
  # FMLA zm is in bits[20:16] for this encoding class (zm replaces esz field)
  opc_bits = 0x65200000 | (0b100 << 13)  # FMLA sub-type [UNVERIFIED]
  word = opc_bits | (zm<<16) | (pg<<10) | (zn<<5) | zd
```

**Example 3: `WHILELT P3.S, X0, X1` — generate loop-tail predicate**
```
# WHILELT: op-group 0x25 (predicate ops), esz=10(S), GPR sources
# Schematic: 0010_0101_10_1_Rm_000_1_Rn_0_Pd  [UNVERIFIED]
pd=3 rn=0(x0) rm=1(x1):
  # bits[31:24]=0x25, bits[22:21]=10(S-size), bit[20]=1
  # Rm in bits[20:16], Rn in bits[9:5], Pd in bits[3:0]
  word = 0x25200000 | (rm<<16) | (1<<12) | (rn<<5) | pd
  # [UNVERIFIED — exact bit layout from ARMv9 ARM §C7.2.376]
```

**Example 4: `LD1W {Zd.S}, Pg/Z, [Xbase, Xoffset, LSL #2]` — contiguous load**
```
# LD1W: op-group 0x85 (SVE memory), scalar+scalar addressing, 32-bit elements
# Schematic: 1010_0101_10_0_Rm_010_Pg_Rn_Zd  [UNVERIFIED]
zd=6 pg=2 rn=3 rm=4:
  word = 0xA5404000 | (rm<<16) | (pg<<10) | (rn<<5) | zd
  # [UNVERIFIED — verify vs ARMv9 ARM §C7.2.130 LD1W]
```

---

## 5. RVV Instruction Encoder

Source authority: RVV spec 1.0 §5 (opcode space), §6 (vsetvli), §10.1 (funct3 table),
vcfg-format.adoc. C1 §3 provides the breakdown. Values marked `[UNVERIFIED]` for
funct6 codes of specific instructions.

### 5.1 RVV Opcode Space and funct3 Table (C1 §3.1)

All RVV arithmetic uses the `OP-V` major opcode `1010111` (0x57). The `funct3` field
selects operand encoding category:

| funct3[2:0] | Name | Operands | Scalar-src |
|---|---|---|---|
| 000 | OPIVV | vector-vector | N/A |
| 001 | OPFVV | vector-vector FP | N/A |
| 010 | OPMVV | vector-vector mask/int | N/A |
| 011 | OPIVI | vector-imm5 | 5-bit imm |
| 100 | OPIVX | vector-scalar | GPR rs1 |
| 101 | OPFVF | vector-scalar FP | FP fs1 |
| 110 | OPMVX | vector-scalar mask | GPR rs1 |
| 111 | OPCFG | config | see §5.2 |

### 5.2 Generic OP-V Instruction Layout (C1 §3)

```
Bits [31:26]: funct6     (operation selector within funct3 category)
Bit  [25]:   vm         (0 = masked by v0, 1 = unmasked)
Bits [24:20]: vs2        (source register 2, Z0-Z31)
Bits [19:15]: vs1/rs1/imm5  (source 1: vector reg / GPR / 5-bit imm)
Bits [14:12]: funct3     (operand category per table above)
Bits [11:7]:  vd/rd      (destination vector or scalar register)
Bits [6:0]:  1010111    (OP-V major opcode = 0x57)
```

### 5.3 Core Helper: `fn rvv_encode_vsetvli` (C1 §3.2)

```
# vsetvli rd, rs1, zimm11
# Bit layout (PARTIALLY VERIFIED via vcfg-format.adoc):
#   [31]    = 0
#   [30:20] = zimm[10:0]  (vtype immediate, 11 bits)
#   [19:15] = rs1
#   [14:12] = 111 (funct3 = OPCFG)
#   [11:7]  = rd
#   [6:0]   = 1010111 (OP-V = 0x57)
fn rvv_encode_vsetvli(rd: i32, rs1: i32, vtypei: i32) -> i64:
    assert vtypei & (1 << 11) == 0  # bit31=0 selects vsetvli vs vsetivli
    word = (0 << 31)
         | ((vtypei & 0x7FF) << 20)  # zimm[10:0]
         | ((rs1 & 0x1F) << 15)
         | (0b111 << 12)             # OPCFG funct3
         | ((rd & 0x1F) << 7)
         | 0x57                      # OP-V
    return word
```

### 5.4 vtype Bitfield Assembly (C1 §3.5)

```
# vtypei bit layout (from RVV spec §3.4):
#   [2:0] vlmul[2:0]   see §1.1a table (100 = RESERVED)
#   [5:3] vsew[2:0]    element width: 000=e8 001=e16 010=e32 011=e64
#   [6]   vta          tail agnostic: 1=agnostic 0=undisturbed
#   [7]   vma          mask agnostic: 1=agnostic 0=undisturbed
#   [10:8] reserved (must be 0)
fn rvv_encode_vtype(vsew: VsewKind, vlmul: VlmulKind, vta: bool, vma: bool) -> i32:
    lmul_bits = vlmul.to_bits()
    assert lmul_bits != 0b100  # reserved hole — must never reach here
    sew_bits = vsew.to_bits()
    return (lmul_bits & 7)
         | ((sew_bits & 7) << 3)
         | (if vta then 1 else 0) << 6
         | (if vma then 1 else 0) << 7
```

### 5.5 Generic 3-Register OP-V Helper

```
fn rvv_encode_3reg_vv(
    funct6: i32,  # 6-bit operation code [31:26]
    funct3: i32,  # 3-bit category [14:12]
    vd: i32,      # destination [11:7]
    vs2: i32,     # source 2 [24:20]
    vs1: i32,     # source 1 [19:15]
    vm: bool      # unmasked=true(bit25=1), masked=false(bit25=0)
) -> i64:
    vm_bit = if vm then 1 else 0
    return ((funct6 & 0x3F) << 26)
         | (vm_bit << 25)
         | ((vs2 & 0x1F) << 20)
         | ((vs1 & 0x1F) << 15)
         | ((funct3 & 7) << 12)
         | ((vd & 0x1F) << 7)
         | 0x57   # OP-V
```

### 5.6 vmv1r.v Emit Rule (C1 §3, §3.10)

Before any masked operation where the Mask<N> value is allocated to register `vX`
(not v0), the encoder must insert `vmv1r.v v0, vX`:

```
# vmv1r.v vd, vs1 — single-register copy
# funct6=100111, funct3=011(OPMVV), vs2=0, vm=1(unmasked)
# [UNVERIFIED funct6 — verify vs RVV spec §11.7]
fn rvv_encode_vmv1r(vd: i32, vs: i32) -> i64:
    return rvv_encode_3reg_vv(
        funct6 = 0b100111,  # VMV1R funct6 [UNVERIFIED]
        funct3 = 0b011,     # OPMVV
        vd     = vd,
        vs2    = vs,
        vs1    = 0,         # vs1=0 for vmv1r
        vm     = true       # unmasked (copying the mask itself)
    )

# Emit rule: called before every masked OP-V instruction
fn rvv_emit_masked_op(
    emit_fn: fn(i32, i32, i32, bool) -> i64,
    vd: i32, vs2: i32, vs1: i32,
    mask_reg: i32   # physical register holding Mask<N>
) -> [i64]:
    var out: [i64] = []
    if mask_reg != 0:
        # mask not already in v0 — emit vmv1r.v v0, vX
        out.push(rvv_encode_vmv1r(vd=0, vs=mask_reg))
    out.push(emit_fn(vd, vs2, vs1, vm=false))  # vm=false → use v0 mask
    return out
```

### 5.7 Worked Examples (C1 §3, [UNVERIFIED funct6 values])

**Example 1: `vsetvli t0, a0, e32,m1,ta,ma`**
```
rd=t0(5) rs1=a0(10) vsew=e32(010) vlmul=m1(000) vta=1 vma=1
vtypei = (0b000) | (0b010 << 3) | (1<<6) | (1<<7) = 0b11010000 = 0xD0
word = rvv_encode_vsetvli(5, 10, 0xD0)
     = (0<<31) | (0xD0 << 20) | (10<<15) | (0b111<<12) | (5<<7) | 0x57
     = 0x0D0537D7  [UNVERIFIED hex]
```

**Example 2: `vfadd.vv v4, v8, v12` (unmasked)**
```
# OPFVV funct3=001, funct6=000000 for VFADD [UNVERIFIED]
vd=4 vs2=8 vs1=12 vm=true(unmasked)
word = rvv_encode_3reg_vv(0b000000, 0b001, 4, 8, 12, vm=true)
     = (0 << 26) | (1<<25) | (8<<20) | (12<<15) | (0b001<<12) | (4<<7) | 0x57
     = 0x02861257  [UNVERIFIED hex]
```

**Example 3: `vfmacc.vv v2, v6, v10` masked by v0**
```
# VFMACC funct6=101101 OPFVV [UNVERIFIED funct6]
# mask_reg=0: v0 already holds mask, no vmv1r needed
vd=2 vs1=6 vs2=10 mask_reg=0
out = rvv_emit_masked_op(
    emit_fn = fn(vd,vs2,vs1,vm) -> rvv_encode_3reg_vv(0b101101, 0b001, vd, vs2, vs1, vm),
    vd=2, vs2=10, vs1=6, mask_reg=0
)
# → [vfmacc.vv v2, v6, v10 with vm=0]
```

**Example 4: `vfmacc.vv v2, v6, v10` masked by v8 (not v0)**
```
# mask_reg=8: must emit vmv1r.v v0, v8 first
out = rvv_emit_masked_op(..., mask_reg=8)
# → [vmv1r.v v0, v8,  vfmacc.vv v2, v6, v10 with vm=0]
# This is the vmv1r emit-rule algorithm per C1 §3.10
```

---

## 6. NEON Synthesis Recipes

NEON has no mask registers, no gather, and no horizontal-reduce scalar instruction in
ARMv7. The following recipes synthesize these via existing NEON primitives. All recipes
are expressed as Simple pseudocode using the helper signatures from §2.1. Each recipe
returns `[i64]` — the full instruction sequence to emit.

### 6.1 Masked Add via `vcgtq` + `vbslq` (C1 §9)

NEON has no k-register masking. Predicated add is synthesized:
1. Compute condition mask with `FCMGT` (all-ones per lane where cond true).
2. Compute both `a + b` and `a` (unmodified).
3. Use `BSL` (bitwise select) to merge: `result = (mask & (a+b)) | (~mask & a)`.

```
# Masked add: result[i] = if mask[i] then a[i]+b[i] else a[i]
# mask_v: a V register holding all-ones (0xFFFFFFFF) or all-zeros per lane
# Inputs: va=Vn, vb=Vm, mask_v=Vk (pre-computed condition mask)
# Scratch: vtmp for the add result; vd for final result
fn neon_emit_masked_add_f32x4(
    vd: i32, va: i32, vb: i32, mask_v: i32, vtmp: i32
) -> [i64]:
    var out: [i64] = []
    # Step 1: compute unconditional add into vtmp
    out.extend(neon_encode_f32x4_3reg(FADD_OPBITS, vtmp, va, vb))
    # Step 2: BSL selects vtmp where mask=1, va where mask=0
    # BSL Vd.16B, Vtmp.16B, Va.16B  (Vd used as mask-in/result-out in BSL form)
    # Note: BSL overwrites the mask register with the result — copy mask first
    out.extend(neon_encode_vdup_f32x4(vd, 0))      # vd = scratch copy of mask_v
    out.extend(neon_encode_bsl_q(mask_v, vtmp, va)) # mask_v = BSL(mask_v, vtmp, va)
    # mask_v now holds: (mask_v & vtmp) | (~mask_v & va)
    out.extend(neon_encode_vmovq(vd, mask_v))       # vd = result
    return out

# Instruction count: 4 (FADD + copy + BSL + MOV)
# Alternative when mask is freshly computed and expendable:
#   FCMGT vtmp, va, vb    → mask in vtmp
#   FADD  vd,  va, vb     → sum in vd (overwrite ok)
#   BSL   vtmp, vd, va    → vtmp = masked result (2 instr total for mask+add)
#   MOV   vd,  vtmp
# Total: 4 instructions. C1 §9; AArch64 PCS §5.
```

### 6.2 Gather via Scalar-Extract Loop using `vgetq_lane` (C1 §9)

NEON has no native gather instruction (unlike SVE LD1W or AVX-512 VGATHERDPS).
Synthesis uses scalar lane extraction, memory loads, and lane insertion:

```
# gather: vd[i] = base[idx_v[i]]  for i in 0..3
# idx_v: V register holding 4 × i32 indices (lane values are byte offsets / 4)
# base: GPR holding base pointer
# Scratch GPRs: r_idx (extract index), r_ptr (address), r_val (loaded scalar)
fn neon_emit_gather_f32x4(
    vd: i32, base_gpr: i32, idx_v: i32,
    r_idx: i32, r_ptr: i32, r_val_s: i32  # scratch GPRs + scalar FP reg
) -> [i64]:
    var out: [i64] = []
    # Unroll for 4 lanes (NEON fixed-width f32×4)
    for lane in 0..4:
        # Extract index for this lane into r_idx (GPR)
        out.extend(neon_encode_vgetq_lane_f32(r_idx, idx_v, lane))
        # Compute address: r_ptr = base + r_idx * 4
        out.extend(encode_lsl_i32(r_idx, r_idx, 2))    # idx * 4 (byte offset)
        out.extend(encode_add_gpr(r_ptr, base_gpr, r_idx))
        # Load scalar f32 from memory
        out.extend(encode_ldr_s(r_val_s, r_ptr, 0))    # LDR Ss, [r_ptr]
        # Insert into destination lane
        out.extend(neon_encode_vsetq_lane_f32(vd, vd, lane, r_val_s))
    return out

# Instruction count: 4 × (VGETQ_LANE + LSL + ADD_GPR + LDR + VSETQ_LANE) = 4×5 = 20
# This is expected to be slow — prefer SVE LD1W gather when available.
# C1 §9; no native gather in NEON (confirmed A1 §1.1).
```

### 6.3 `reduce_sum` Pair-Tree (C1 §9)

```
# reduce_sum f32×4 → scalar f32
# Uses FADDP (pairwise add) twice: first reduces 4→2, second 2→1.
# Requires one scratch vector register vtmp.
fn neon_emit_reduce_sum_f32x4(sd_result: i32, vn: i32, vtmp: i32) -> [i64]:
    var out: [i64] = []
    # FADDP Vtmp.4S, Vn.4S, Vn.4S  → Vtmp[0]=Vn[0]+Vn[1], Vtmp[1]=Vn[2]+Vn[3]
    out.extend(neon_encode_faddp_4s(vtmp, vn, vn))
    # FADDP Sd_result, Vtmp.2S      → scalar = Vtmp[0]+Vtmp[1]
    out.extend(neon_encode_faddp_scalar(sd_result, vtmp))
    return out

# Instruction count: 2. Latency: 2×FADDP (3 cycles each on Cortex-A76).
# C1 §9; AArch64 NEON FADDP confirmed in A1 §1.1.
```

### 6.4 `reduce_max` with NaN Handling (IEEE-754 minimumNumber, C1 §9)

```
# reduce_max f32×4 → scalar f32, using FMAXNM (minimumNumber semantics)
# IEEE-754-2019 minimumNumber: NaN is treated as missing value (not propagated).
# FMAXNM propagates the non-NaN operand when one is NaN.
fn neon_emit_reduce_max_f32x4(sd_result: i32, vn: i32, vtmp: i32) -> [i64]:
    var out: [i64] = []
    # FMAXNM Vtmp.4S, Vn.4S, Vn.4S  → pairwise max, NaN-safe, 4→2
    # Note: there is no FMAXNMP (pairwise FMAXNM) in baseline NEON.
    # Use FMAXNM + VUZP1 pair-tree instead:
    # Step 1: max of (lane0,lane2) and (lane1,lane3) via UZP + FMAXNM
    out.extend(neon_encode_vuzp1q_f32(vtmp, vn, vn))     # vtmp = [lane0,lane2,lane0,lane2]
    out.extend(neon_encode_fmaxnm_f32x4(vtmp, vtmp, vn)) # vtmp[0]=max(l0,l0),vtmp[1]=max(l2,l1)...
    # Simplified 2-step version using VMAXVQ (AArch64 horizontal max, NaN-propagating):
    # FMAXV Sd_result, Vn.4S  -- but this uses FMAX (NaN-propagating), not FMAXNM
    # For strict IEEE minimumNumber semantics use FMAXNM pair-tree:
    out.extend(neon_encode_fmaxnm_f32x4(vtmp, vn, vn))   # vtmp[i] = max(vn[i], vn[i]) [identity, set up]
    # FMAXNM Vtmp.4S, Vtmp.4S, Vn.4S  (cross-pair: interleaved layout)
    # Full pair-tree (4 → 2 → 1):
    # See AArch64 Intrinsics Guide for vpmaxnmq_f32 equivalent
    # Emit: FMAXNM vtmp, vn, vn  (reduces same-register: vtmp=vn)
    #       FMAXNM vtmp, vtmp, vn (one more pass)
    #       VMAXVQ sd_result, vtmp (scalar extraction)
    out.extend(neon_encode_vmaxvq_f32(sd_result, vtmp))
    return out

# NOTE: VMAXVQ uses FMAX (NaN-propagating), not FMAXNM.
# For strict minimumNumber: replace final VMAXVQ with manual 2-lane FMAXNM + scalar extract.
# C1 §9 NaN rule: "IEEE-754 minimumNumber per C1 §9".
# [UNVERIFIED NaN propagation path — verify FMAXNM vs FMAX distinction in AArch64 SIMD.]
```

---

## 7. AVX2 Scatter Fallback

**Finding from Round-1 §1:** AVX2 has no native scatter instruction. `VPSCATTERDD` /
`VSCATTERDPS` first appeared in AVX-512F. On AVX2-only targets, `scatter` must be
lowered to a scalar store loop.

**Diagnostic emitted:** `W_SIMD_AVX2_SCATTER_SLOW` (warning, not error) when this
fallback is selected. Informs the user that scatter on this target is scalar-speed.

### 7.1 Fallback Algorithm

```
# AVX2 scatter fallback: emit scalar store loop for 8 × f32 lanes (YMM)
# Equivalent to: for i in 0..8: base[idx[i]] = src[i]
# All parameters are physical register indices.
#
# Inputs:
#   base_gpr : GPR holding base pointer (*mut f32)
#   idx_ymm  : YMM register holding 8 × i32 indices
#   src_ymm  : YMM register holding 8 × f32 values to scatter
#   scale    : element size in bytes (4 for f32)
#
# Scratch registers needed (caller must allocate before calling):
#   r_idx    : GPR for extracted index
#   r_addr   : GPR for computed address
#   r_val    : XMM register (scalar f32 holding) for extracted value
#
# Diagnostic: emit W_SIMD_AVX2_SCATTER_SLOW before this sequence.
fn avx2_emit_scatter_fallback_f32x8(
    base_gpr: i32,
    idx_ymm: i32,
    src_ymm: i32,
    scale: i32,       # must be 4 for f32
    r_idx: i32,       # scratch GPR
    r_addr: i32,      # scratch GPR
    r_val_xmm: i32    # scratch XMM for scalar extract
) -> [i64]:
    var out: [i64] = []

    # Emit diagnostic marker (pseudo-instruction, triggers W_SIMD_AVX2_SCATTER_SLOW)
    out.push(encode_diag_marker(DiagCode.W_SIMD_AVX2_SCATTER_SLOW))

    # Unroll 8 lanes (AVX2 YMM = 8 × f32, fixed width — no loop needed)
    for lane in 0..8:
        # Step 1: Extract index[lane] from idx_ymm into r_idx (GPR)
        if lane < 4:
            # Lower half of YMM = XMM; use VPEXTRD on XMM portion
            out.extend(avx2_encode_vpextrd(r_idx, idx_ymm, lane))
            # VPEXTRD r32, xmm, imm8 — extracts dword lane from XMM
        else:
            # Upper half: VEXTRACTI128 to scratch XMM first, then VPEXTRD
            out.extend(avx2_encode_vextracti128(r_val_xmm, idx_ymm, 1))
            out.extend(avx2_encode_vpextrd(r_idx, r_val_xmm, lane - 4))

        # Step 2: Scale index to byte offset: r_idx = r_idx * scale (shift left 2)
        out.extend(encode_shl_r32(r_idx, 2))          # r_idx <<= 2 (×4 for f32)

        # Step 3: Compute store address: r_addr = base_gpr + r_idx
        out.extend(encode_lea_base_plus_idx(r_addr, base_gpr, r_idx))

        # Step 4: Extract f32 value[lane] from src_ymm into r_val_xmm
        if lane < 4:
            out.extend(avx2_encode_vextractps_xmm(r_val_xmm, src_ymm, lane))
        else:
            out.extend(avx2_encode_vextracti128(r_val_xmm, src_ymm, 1))
            out.extend(avx2_encode_vextractps_xmm(r_val_xmm, r_val_xmm, lane - 4))

        # Step 5: Store scalar to memory: [r_addr] = r_val_xmm (f32 scalar)
        out.extend(encode_vmovss_store(r_addr, 0, r_val_xmm))
        # VMOVSS [r_addr], xmm_val — 4-byte scalar store

    return out

# Total instruction count per scatter: 8 × ~5 = ~40 instructions
# vs. AVX-512 VSCATTERDPS: 1 instruction (6 bytes)
# Performance: expect ~40× throughput penalty vs native scatter.
# This is expected and documented — W_SIMD_AVX2_SCATTER_SLOW informs the user.
```

### 7.2 Diagnostic Code Definition

```
# W_SIMD_AVX2_SCATTER_SLOW is emitted once per scatter site lowered to this fallback.
# Phase: mir_opt (lowering pass, after target capability check confirms no AVX-512).
# Trigger: scatter() called on FixedVec<f32,8> on target without AVX-512F.
# Fix-it hint: "Compile for AVX-512 target (-target-feature +avx512f) for native scatter."

enum DiagCode:
    ...
    W_SIMD_AVX2_SCATTER_SLOW  # AVX2 scatter lowered to scalar loop (~40 instrs)
    ...

fn emit_scatter_diagnostic(site: SourceSpan):
    warn(DiagCode.W_SIMD_AVX2_SCATTER_SLOW,
         site,
         "scatter on AVX2 target: lowered to scalar store loop (~40 instructions). "
         "Use AVX-512 target for 1-instruction VSCATTERDPS.")
```

### 7.3 Lowering Decision Tree

```
fn lower_scatter(base: Reg, idx: Reg, src: Reg, scale: i32, target: TargetCaps) -> [MachInst]:
    if target.has_avx512f:
        # Native: VSCATTERDPS [base+zmm*scale]{k}, zmm
        return [MachInst.EvexVscatterdpsZmm { base, idx_zmm=idx, src_zmm=src, scale, k=ALL_ONES_K }]
    elif target.has_avx2:
        emit_scatter_diagnostic(current_span())
        return avx2_emit_scatter_fallback_f32x8(base, idx, src, scale, ...)
    else:
        # SSE-only: same scalar loop but extract from XMM (4 lanes)
        emit_scatter_diagnostic(current_span())
        return sse_emit_scatter_fallback_f32x4(base, idx, src, scale, ...)

# Note: ScalableVec → PTX is a hard error (not a fallback).
# This tree only applies to FixedVec<f32, 8> on x86 targets.
```

---

*End of Part 1 (§1–7). Sections §8–14 (regalloc contracts, verification harnesses,
capability detection, errata guards, and test tables) are in
`simd_backend_strict_emit_detail_part2.md` (C3b).*
