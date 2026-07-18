<!-- claude-arch -->
# Architecture: SIMD Backend Strict-Emit Op Tables

This document specifies the strict-emit backend ABI for each SIMD target in the Simple compiler: the MachInst opcode families, physical register contracts, encoder helper signatures, per-ISA op tables mapping the abstract `Vector` trait to native opcodes, synthesis recipes for missing native ops, register allocation contracts, verification patterns, cross-target golden-test fixtures, and a first-wave stub list. It is the companion document to `simd_unified_architecture.md` (B1, type system) and `simd_rollout_plan.md` (B3, phasing). Do not re-derive the type-system design or milestone ordering here.

---

## Table of Contents

1. MachInst Extension Contract
2. Per-ISA Op Tables
   - 2.1 NEON / AArch64 ASIMD
   - 2.2 x86 SSE2/SSE4 (128-bit)
   - 2.3 x86 AVX2 (256-bit)
   - 2.4 x86 AVX-512 (512-bit)
   - 2.5 ARM SVE2 (scalable)
   - 2.6 RVV 1.0 (scalable)
   - 2.7 NVIDIA PTX (warp/32)
   - 2.8 SPIR-V Vulkan (subgroup)
3. Synthesis Tables for Missing Native Opcodes
4. Register Allocation Contracts
5. Encoder Helper Inventory
6. Strict-Emit Verification
7. Cross-Target Test Fixtures
8. Future Opcodes (Not First Wave)

---

## 1. MachInst Extension Contract

### 1.1 New MachRegKind Variants

Existing: `MachRegKind.Neon128` (arm_neon.spl:21, physical_reg pattern). New variants required:

| Variant | Width | Backing ISA | Notes |
|---------|-------|-------------|-------|
| `MachRegKind.Neon128` | 128b fixed | AArch64 ASIMD | Already exists; V0–V31 |
| `MachRegKind.Zmm` | 512b fixed | AVX-512 | ZMM0–ZMM31 |
| `MachRegKind.Avx512Mask` | 64b fixed | AVX-512 k-regs | k0–k7; k0 hardwired all-ones |
| `MachRegKind.Sve` | VL-bit scalable | ARM SVE2 | Z0–Z31; VL runtime |
| `MachRegKind.SvePred` | (VL/8)-bit scalable | ARM SVE2 | P0–P15; P15 reserved |
| `MachRegKind.Rvv` | VLEN×LMUL scalable | RVV 1.0 | V0–V31; LMUL grouping |
| `MachRegKind.RvvMask` | VLEN/8 scalable | RVV 1.0 | v0 only; aliased from Rvv |

PTX and SPIR-V use virtual/SSA register models; no new `MachRegKind` variants are needed for them. The existing text/word-stream emitter pattern suffices — register names are informational labels in the emitted text, not allocator-binding physical slots.

### 1.2 New MachInst Opcode Families

Each family maps to a group of `MachInst` tagged-union variants. Naming mirrors the existing pattern (`SimdFaddF32x4`, etc. in mir_instructions.spl:88–116):

| Family prefix | Target | Example variants |
|---------------|--------|-----------------|
| `SimdZmm*` | AVX-512 | `SimdZmmAddF32x16`, `SimdZmmMaskAddF32x16`, `SimdZmmScatterF32` |
| `SimdSve*` | SVE2 | `SimdSveAddF32`, `SimdSveGatherF32`, `SimdSvePredSetWhilelt` |
| `SimdRvv*` | RVV 1.0 | `SimdRvvSetVli`, `SimdRvvAddF32`, `SimdRvvMaskAddF32` |
| `SimdPtx*` | PTX | `SimdPtxAddF32`, `SimdPtxShflSyncIdx`, `SimdPtxPredSet` |
| `SimdSpirv*` | SPIR-V | `SimdSpirvVectorAdd`, `SimdSpirvSubgroupReduce`, `SimdSpirvShuffle` |

AVX-512 uses EVEX prefix encoding; arm_neon.spl and x86_64_simd.spl use fixed-32-bit and VEX-prefix patterns respectively. EVEX is a 4-byte prefix replacing VEX for 512-bit, k-mask, and embedded-rounding ops.

### 1.3 Encoder Helper Signatures (Pattern Reference)

From arm_neon.spl:71:
```
fn neon_encode_f32x4_3reg(opcode_bits: i64, qd: i32, qn: i32, qm: i32) -> [i64]
```

From x86_64_simd.spl:152:
```
fn _encode_simd_3op_ymm(dest: i32, src1: i32, src2: i32,
                         mmmmm: i32, w: i32, pp: i32, opcode: i32) -> [i64]
```

New helpers mirror this pattern — low-level binary encoders returning `[i64]` instruction words:

```
# arm_neon.spl extensions
fn neon_encode_3reg_pred(opcode_bits: i64, qd: i32, qn: i32, qm: i32,
                          mask_vec: i32) -> [i64]   # synthesized via BSL

# x86_64_avx512.spl (new file)
fn evex_encode_3op_zmm(dest: i32, src1: i32, src2: i32,
                        k_mask: i32, zeroing: bool,
                        mmm: i32, w: i32, pp: i32, opcode: i32) -> [i64]
fn evex_encode_scatter_zmm(base: i32, idx: i32, src: i32,
                            k_mask: i32, scale: i32, opcode: i32) -> [i64]

# arm_sve2.spl (new file)
fn sve_encode_3reg_pred(opcode_bits: i64, zd: i32, pg: i32,
                         zn: i32, zm: i32) -> [i64]
fn sve_encode_2reg_pred(opcode_bits: i64, zd: i32, pg: i32, zn: i32) -> [i64]
fn sve_encode_gather_ld(opcode_bits: i64, zd: i32, pg: i32,
                         base: i32, zoffset: i32) -> [i64]

# riscv_rvv.spl (new file)
fn rvv_encode_vsetvli(rd: i32, rs1: i32, vtypei: i32) -> i64
fn rvv_encode_3reg_vv(opcode_bits: i64, vd: i32, vs2: i32,
                       vs1: i32, vm: bool) -> i64
fn rvv_encode_3reg_vx(opcode_bits: i64, vd: i32, vs2: i32,
                       rs1: i32, vm: bool) -> i64
fn rvv_encode_load_stride(opcode_bits: i64, vd: i32, rs1: i32,
                           rs2: i32, vm: bool) -> i64
fn rvv_encode_gather(opcode_bits: i64, vd: i32, vs2: i32,
                      rs1: i32, vm: bool) -> i64
```

---

## 2. Per-ISA Op Tables

Column definitions:
- **Abstract op**: Vector trait method name (B1-owned; treat as opaque label here)
- **Type**: element type and lane count for this row
- **Native opcode(s)**: mnemonic / intrinsic. Spec citations in notes.
- **Encoder helper**: function from §1.3 or §5
- **Reg class**: MachRegKind variant
- **Mask/pred handling**: how inactive lanes are handled
- **Notes**: synthesis flag (S=synthesized, N=native), spec section

### 2.1 NEON / AArch64 ASIMD

Reference: ARM Architecture Reference Manual ARMv9-A, §C7 (SIMD/FP instruction set). ACLE §9 (NEON intrinsics), §11 (SVE). No native mask registers — all masked ops synthesized via BSL.

| Abstract op | Type | Native opcode(s) | Encoder helper | Reg class | Mask/pred handling | Notes |
|-------------|------|-----------------|----------------|-----------|-------------------|-------|
| splat | f32×4 | `DUP Vd.4S, Vn.S[0]` | neon_encode_f32x4_3reg | Neon128 | — | N; ARMv9 §C7.2.47 |
| splat | i32×4 | `DUP Vd.4S, Rn` | neon_encode_f32x4_3reg | Neon128 | — | N; §C7.2.47 |
| splat | f64×2 | `DUP Vd.2D, Rn` | neon_encode_f64x2_3reg | Neon128 | — | N |
| load_aligned | f32×4 | `LDR Qd, [Rn]` | neon_encode_load_q | Neon128 | — | N; NEON has no alignment fault for Q |
| load_unaligned | f32×4 | `LD1 {Vd.4S}, [Rn]` | neon_encode_ld1 | Neon128 | — | N; LD1 tolerates unaligned |
| store_aligned | f32×4 | `STR Qd, [Rn]` | neon_encode_store_q | Neon128 | — | N |
| store_unaligned | f32×4 | `ST1 {Vd.4S}, [Rn]` | neon_encode_st1 | Neon128 | — | N |
| gather | f32×4 | — (no native) | — | Neon128 | — | S: scalar loop, 4× LDR Ss + INS |
| scatter | f32×4 | — (no native) | — | Neon128 | — | S: 4× UMOV + STR |
| add | f32×4 | `FADD Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg (0x4E20D400) | Neon128 | S: vbslq blend post-add | N; arm_neon.spl:138 |
| sub | f32×4 | `FSUB Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg (0x4EA0D400) | Neon128 | S: vbslq | N; arm_neon.spl:145 |
| mul | f32×4 | `FMUL Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg (0x6E20DC00) | Neon128 | S: vbslq | N; arm_neon.spl:152 |
| fma | f32×4 | `FMLA Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg (0x4E20CC00) | Neon128 | S: vbslq | N; arm_neon.spl:159 |
| fnmadd | f32×4 | `FMLS Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg (0x4EA0CC00) | Neon128 | S: vbslq | N; §C7.2.85 |
| abs | f32×4 | `FABS Vd.4S, Vn.4S` | neon_encode_f32x4_2reg | Neon128 | S: vbslq | N; §C7.2.1 |
| neg | f32×4 | `FNEG Vd.4S, Vn.4S` | neon_encode_f32x4_2reg | Neon128 | S: vbslq | N; §C7.2.100 |
| min | f32×4 | `FMIN Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg | Neon128 | S: vbslq | N; §C7.2.93 |
| max | f32×4 | `FMAX Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg | Neon128 | S: vbslq | N; §C7.2.90 |
| and | i32×4 | `AND Vd.16B, Vn.16B, Vm.16B` | neon_encode_i32x4_3reg | Neon128 | S: vbslq | N; §C7.2.10 |
| or | i32×4 | `ORR Vd.16B, Vn.16B, Vm.16B` | neon_encode_i32x4_3reg | Neon128 | S: vbslq | N; §C7.2.110 |
| xor | i32×4 | `EOR Vd.16B, Vn.16B, Vm.16B` | neon_encode_i32x4_3reg | Neon128 | S: vbslq | N; §C7.2.51 |
| andnot | i32×4 | `BIC Vd.16B, Vn.16B, Vm.16B` | neon_encode_i32x4_3reg | Neon128 | S: vbslq | N; §C7.2.18 |
| shl | i32×4 | `SHL Vd.4S, Vn.4S, #imm` | neon_encode_shl_imm | Neon128 | S: vbslq | N; §C7.2.167 |
| shr_logical | i32×4 | `USHR Vd.4S, Vn.4S, #imm` | neon_encode_shr_imm | Neon128 | S: vbslq | N; §C7.2.228 |
| shr_arith | i32×4 | `SSHR Vd.4S, Vn.4S, #imm` | neon_encode_shr_imm | Neon128 | S: vbslq | N; §C7.2.193 |
| cmp_eq | f32×4 | `FCMEQ Vd.4S, Vn.4S, Vm.4S` | neon_encode_f32x4_3reg | Neon128 | produces lane-mask vector | N; §C7.2.58 |
| cmp_lt | f32×4 | `FCMGT Vd.4S, Vm.4S, Vn.4S` | neon_encode_f32x4_3reg | Neon128 | swap operands for LT | N; §C7.2.62 |
| cmp_le | f32×4 | `FCMGE Vd.4S, Vm.4S, Vn.4S` | neon_encode_f32x4_3reg | Neon128 | swap operands for LE | N; §C7.2.60 |
| mask_select | f32×4 | `BSL Vd.16B, Vn.16B, Vm.16B` | neon_encode_bsl | Neon128 | mask in Vd (destructive) | N; §C7.2.22 |
| reduce_sum | f32×4 | `FADDP; FADDP` | neon_encode_faddp | Neon128 | — | S: 2× pairwise; §C7.2.55 |
| reduce_max | f32×4 | `FMAXV Sd, Vn.4S` | neon_encode_fmaxv | Neon128 | — | N; §C7.2.92 |
| reduce_min | f32×4 | `FMINV Sd, Vn.4S` | neon_encode_fminv | Neon128 | — | N; §C7.2.95 |
| reduce_and | i32×4 | `ANDV Bd, Vn.16B` + extend | neon_encode_andv | Neon128 | — | S: ANDV then UMOV; §C7.2.11 |
| reduce_or | i32×4 | `ORV Bd, Vn.16B` + extend | neon_encode_orv | Neon128 | — | S: ORV then UMOV |
| permute | f32×4 | `TBL Vd.16B, {Vn.16B}, Vm.16B` | neon_encode_tbl | Neon128 | — | N; byte-indexed; §C7.2.217 |
| shuffle | f32×4 | `TBL Vd.16B, {Vn.16B}, Vm.16B` | neon_encode_tbl | Neon128 | — | N; static idx→const Vm |
| broadcast_lane | f32×4 | `DUP Vd.4S, Vn.S[idx]` | neon_encode_dup_lane | Neon128 | — | N; §C7.2.47 |
| interleave_lo | f32×4 | `ZIP1 Vd.4S, Vn.4S, Vm.4S` | neon_encode_zip1 | Neon128 | — | N; §C7.2.236 |
| interleave_hi | f32×4 | `ZIP2 Vd.4S, Vn.4S, Vm.4S` | neon_encode_zip2 | Neon128 | — | N; §C7.2.237 |

### 2.2 x86 SSE2/SSE4 (128-bit XMM)

Reference: Intel Architecture Software Developer's Manual Vol 2 (SDM). SSE2 = base; SSE4.1 adds BLENDVPS, DPPS, INSERT/EXTRACT. Reg class `Xmm` maps to `MachRegKind.Xmm` (existing, x86_64_simd.spl). No k-mask regs.

| Abstract op | Type | Native opcode(s) | Encoder helper | Reg class | Mask/pred handling | Notes |
|-------------|------|-----------------|----------------|-----------|-------------------|-------|
| splat | f32×4 | `SHUFPS xmm, xmm, 0x00` | _encode_simd_shufps | Xmm | — | N; SDM SHUFPS |
| splat | i32×4 | `PSHUFD xmm, xmm, 0x00` | _encode_simd_pshufd | Xmm | — | N; SDM PSHUFD |
| load_aligned | f32×4 | `MOVAPS xmm, [mem]` | _encode_simd_movaps_load | Xmm | — | N; 16-byte alignment required |
| load_unaligned | f32×4 | `MOVUPS xmm, [mem]` | _encode_simd_movups_load | Xmm | — | N |
| store_aligned | f32×4 | `MOVAPS [mem], xmm` | _encode_simd_movaps_store | Xmm | — | N |
| store_unaligned | f32×4 | `MOVUPS [mem], xmm` | _encode_simd_movups_store | Xmm | — | N |
| gather | f32×4 | — | — | Xmm | — | S: 4× scalar MOVSS + INSERTPS |
| scatter | f32×4 | — | — | Xmm | — | S: 4× EXTRACTPS + MOV |
| add | f32×4 | `ADDPS xmm, xmm` | _encode_simd_3op_xmm (0x58) | Xmm | S: ANDPS/ANDNPS/ORPS blend | N; SDM ADDPS |
| sub | f32×4 | `SUBPS xmm, xmm` | _encode_simd_3op_xmm (0x5C) | Xmm | S | N |
| mul | f32×4 | `MULPS xmm, xmm` | _encode_simd_3op_xmm (0x59) | Xmm | S | N |
| fma | f32×4 | `MULPS` + `ADDPS` | two helpers | Xmm | S | S: no FMA in SSE2; FMA3 requires AVX |
| fnmadd | f32×4 | `MULPS` + `SUBPS` | two helpers | Xmm | S | S |
| abs | f32×4 | `ANDPS xmm, mask_sign` | _encode_simd_andps | Xmm | S | S: mask = 0x7FFFFFFF×4 |
| neg | f32×4 | `XORPS xmm, sign_bits` | _encode_simd_xorps | Xmm | S | S: sign_bits = 0x80000000×4 |
| min | f32×4 | `MINPS xmm, xmm` | _encode_simd_3op_xmm (0x5D) | Xmm | S | N |
| max | f32×4 | `MAXPS xmm, xmm` | _encode_simd_3op_xmm (0x5F) | Xmm | S | N |
| and | i32×4 | `PAND xmm, xmm` | _encode_simd_pand | Xmm | S | N; SDM PAND |
| or | i32×4 | `POR xmm, xmm` | _encode_simd_por | Xmm | S | N |
| xor | i32×4 | `PXOR xmm, xmm` | _encode_simd_pxor | Xmm | S | N |
| andnot | i32×4 | `PANDN xmm, xmm` | _encode_simd_pandn | Xmm | S | N; SDM PANDN — note operand order |
| shl | i32×4 | `PSLLD xmm, imm8` | _encode_simd_pslld | Xmm | S | N |
| shr_logical | i32×4 | `PSRLD xmm, imm8` | _encode_simd_psrld | Xmm | S | N |
| shr_arith | i32×4 | `PSRAD xmm, imm8` | _encode_simd_psrad | Xmm | S | N |
| cmp_eq | f32×4 | `CMPEQPS xmm, xmm` | _encode_simd_cmpps | Xmm | produces lane-mask | N; imm=0 |
| cmp_lt | f32×4 | `CMPLTPS xmm, xmm` | _encode_simd_cmpps | Xmm | — | N; imm=1 |
| cmp_le | f32×4 | `CMPLEPS xmm, xmm` | _encode_simd_cmpps | Xmm | — | N; imm=2 |
| mask_select | f32×4 | `BLENDVPS xmm, xmm, xmm0` | _encode_simd_blendvps | Xmm | mask in XMM0 (implicit) | N; SSE4.1; SDM BLENDVPS |
| mask_select | f32×4 | `ANDPS`+`ANDNPS`+`ORPS` triplet | three helpers | Xmm | explicit 3-op | S: SSE2 fallback if no SSE4.1 |
| reduce_sum | f32×4 | `HADDPS xmm,xmm`×2 | _encode_simd_haddps | Xmm | — | S: SSE3; or SHUFPS+ADDPS×2 |
| reduce_max | f32×4 | `SHUFPS`+`MAXPS`×2 | two helpers | Xmm | — | S: tree reduction |
| reduce_min | f32×4 | `SHUFPS`+`MINPS`×2 | two helpers | Xmm | — | S: tree reduction |
| reduce_and | i32×4 | `PAND`+`PSHUFD`+`PAND` | two helpers | Xmm | — | S: tree |
| reduce_or | i32×4 | `POR`+`PSHUFD`+`POR` | two helpers | Xmm | — | S: tree |
| permute | f32×4 | `SHUFPS xmm,xmm,imm8` | _encode_simd_shufps | Xmm | — | N; compile-time imm only; 2-src form |
| shuffle | i32×4 | `PSHUFD xmm,xmm,imm8` | _encode_simd_pshufd | Xmm | — | N; within-vector |
| broadcast_lane | f32×4 | `SHUFPS xmm,xmm,imm8` | _encode_simd_shufps | Xmm | — | N; imm encodes lane |
| interleave_lo | f32×4 | `UNPCKLPS xmm, xmm` | _encode_simd_unpcklps | Xmm | — | N; SDM UNPCKLPS |
| interleave_hi | f32×4 | `UNPCKHPS xmm, xmm` | _encode_simd_unpckhps | Xmm | — | N |

### 2.3 x86 AVX2 (256-bit YMM)

Reference: Intel SDM Vol 2, VEX-encoded SIMD. AVX2 adds integer 256-bit ops and gather. **No scatter** (first appears in AVX-512). Encoder base: `_encode_simd_3op_ymm` (x86_64_simd.spl:152).

| Abstract op | Type | Native opcode(s) | Encoder helper | Reg class | Mask/pred handling | Notes |
|-------------|------|-----------------|----------------|-----------|-------------------|-------|
| splat | f32×8 | `VBROADCASTSS ymm, [mem]` | _encode_vbroadcastss | Ymm | — | N |
| splat | i32×8 | `VPBROADCASTD ymm, xmm` | _encode_vpbroadcastd | Ymm | — | N; AVX2 |
| load_aligned | f32×8 | `VMOVAPS ymm, [mem]` | _encode_vmovaps_load | Ymm | — | N; 32-byte align |
| load_unaligned | f32×8 | `VMOVUPS ymm, [mem]` | _encode_vmovups_load | Ymm | — | N |
| store_aligned | f32×8 | `VMOVAPS [mem], ymm` | _encode_vmovaps_store | Ymm | — | N |
| store_unaligned | f32×8 | `VMOVUPS [mem], ymm` | _encode_vmovups_store | Ymm | — | N |
| gather | f32×8 | `VGATHERDPS ymm, [base+ymm*s], ymm` | _encode_vgatherdps | Ymm | mask ymm; cleared on read | N; SDM VGATHERDPS |
| scatter | f32×8 | — | — | Ymm | — | S: scalar loop; see §3 |
| add | f32×8 | `VADDPS ymm, ymm, ymm` | _encode_vaddps_ymm (x86_64_simd.spl:167) | Ymm | S: vblendvps | N |
| sub | f32×8 | `VSUBPS ymm, ymm, ymm` | _encode_vsubps_ymm | Ymm | S | N |
| mul | f32×8 | `VMULPS ymm, ymm, ymm` | _encode_vmulps_ymm | Ymm | S | N |
| fma | f32×8 | `VFMADD213PS ymm, ymm, ymm` | _encode_vfmadd213ps | Ymm | S | N; FMA3 (AVX2 subset) |
| fnmadd | f32×8 | `VFNMADD213PS ymm, ymm, ymm` | _encode_vfnmadd213ps | Ymm | S | N |
| abs | f32×8 | `VANDPS ymm, ymm, abs_mask` | _encode_vandps | Ymm | S | S: mask = 0x7FFFFFFF×8 |
| neg | f32×8 | `VXORPS ymm, ymm, sign_bits` | _encode_vxorps | Ymm | S | S |
| min | f32×8 | `VMINPS ymm, ymm, ymm` | _encode_vminps | Ymm | S | N |
| max | f32×8 | `VMAXPS ymm, ymm, ymm` | _encode_vmaxps | Ymm | S | N |
| and | i32×8 | `VPAND ymm, ymm, ymm` | _encode_vpand | Ymm | S | N |
| or | i32×8 | `VPOR ymm, ymm, ymm` | _encode_vpor | Ymm | S | N |
| xor | i32×8 | `VPXOR ymm, ymm, ymm` | _encode_vpxor | Ymm | S | N |
| andnot | i32×8 | `VPANDN ymm, ymm, ymm` | _encode_vpandn | Ymm | S | N; note operand order |
| shl | i32×8 | `VPSLLD ymm, ymm, imm8` | _encode_vpslld | Ymm | S | N |
| shr_logical | i32×8 | `VPSRLD ymm, ymm, imm8` | _encode_vpsrld | Ymm | S | N |
| shr_arith | i32×8 | `VPSRAD ymm, ymm, imm8` | _encode_vpsrad | Ymm | S | N |
| cmp_eq | f32×8 | `VCMPEQPS ymm, ymm, ymm` | _encode_vcmpps | Ymm | produces lane-mask ymm | N; imm=0 |
| cmp_lt | f32×8 | `VCMPLTPS ymm, ymm, ymm` | _encode_vcmpps | Ymm | — | N; imm=1 |
| cmp_le | f32×8 | `VCMPLEPS ymm, ymm, ymm` | _encode_vcmpps | Ymm | — | N; imm=2 |
| mask_select | f32×8 | `VBLENDVPS ymm, ymm, ymm, ymm` | _encode_vblendvps | Ymm | mask in 4th ymm arg | N; AVX |
| reduce_sum | f32×8 | `VHADDPS`×2 + `VADDPS` | three helpers | Ymm | — | S: across 256-bit lanes |
| reduce_max | f32×8 | `VPERM2F128`+`VMAXPS`+tree | multiple | Ymm | — | S |
| reduce_min | f32×8 | `VPERM2F128`+`VMINPS`+tree | multiple | Ymm | — | S |
| reduce_and | i32×8 | `VPERM2I128`+`VPAND`+tree | multiple | Ymm | — | S |
| reduce_or | i32×8 | `VPERM2I128`+`VPOR`+tree | multiple | Ymm | — | S |
| permute | f32×8 | `VPERMPS ymm, ymm, ymm` | _encode_vpermps | Ymm | — | N; AVX2 §C.4 |
| shuffle | i32×8 | `VPERMD ymm, ymm, ymm` | _encode_vpermd | Ymm | — | N |
| broadcast_lane | f32×8 | `VBROADCASTSS ymm, xmm` | _encode_vbroadcastss_xmm | Ymm | — | N; lane 0 only; other lanes need VSHUFPS first |
| interleave_lo | f32×8 | `VUNPCKLPS ymm, ymm, ymm` | _encode_vunpcklps | Ymm | — | N; interleaves within 128b halves |
| interleave_hi | f32×8 | `VUNPCKHPS ymm, ymm, ymm` | _encode_vunpckhps | Ymm | — | N |

### 2.4 x86 AVX-512 (512-bit ZMM)

Reference: Intel SDM Vol 2, EVEX-encoded instructions. AVX-512F required. k0 = all-ones sentinel. EVEX prefix: 4 bytes (62 P0 P1 P2 opcode). Zeroing vs. merge masking selected by bit P2[7] (z-bit).

| Abstract op | Type | Native opcode(s) | Encoder helper | Reg class | Mask/pred handling | Notes |
|-------------|------|-----------------|----------------|-----------|-------------------|-------|
| splat | f32×16 | `VBROADCASTSS zmm, xmm` | evex_encode_broadcast | Zmm | k-mask | N; AVX-512F |
| splat | i32×16 | `VPBROADCASTD zmm, xmm` | evex_encode_broadcast | Zmm | k-mask | N |
| load_aligned | f32×16 | `VMOVAPS zmm{k}{z}, [mem]` | evex_encode_3op_zmm | Zmm | k-merge or k-zero | N; 64-byte align |
| load_unaligned | f32×16 | `VMOVUPS zmm{k}{z}, [mem]` | evex_encode_3op_zmm | Zmm | k-mask | N |
| store_aligned | f32×16 | `VMOVAPS [mem]{k}, zmm` | evex_encode_3op_zmm | Zmm | k-mask stores | N |
| store_unaligned | f32×16 | `VMOVUPS [mem]{k}, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| gather | f32×16 | `VGATHERDPS zmm{k}, [base+zmm*s]` | evex_encode_gather_zmm | Zmm | k-mask cleared per lane | N; AVX-512F |
| scatter | f32×16 | `VSCATTERDPS [base+zmm*s]{k}, zmm` | evex_encode_scatter_zmm | Zmm | k-mask | N; first x86 native scatter |
| add | f32×16 | `VADDPS zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-merge (z=0) or k-zero (z=1) | N |
| sub | f32×16 | `VSUBPS zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| mul | f32×16 | `VMULPS zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| fma | f32×16 | `VFMADD213PS zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| fnmadd | f32×16 | `VFNMADD213PS zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| abs | f32×16 | `VANDPS zmm, zmm, abs_mask_zmm` | evex_encode_3op_zmm | Zmm | k-mask | S: no VABSPS; mask = 0x7FFFFFFF×16 |
| neg | f32×16 | `VXORPS zmm, zmm, sign_zmm` | evex_encode_3op_zmm | Zmm | k-mask | S |
| min | f32×16 | `VMINPS zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| max | f32×16 | `VMAXPS zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| and | i32×16 | `VPANDD zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N; AVX-512F DQ |
| or | i32×16 | `VPORD zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| xor | i32×16 | `VPXORD zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| andnot | i32×16 | `VPANDND zmm{k}{z}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| shl | i32×16 | `VPSLLD zmm{k}{z}, zmm, imm8` | evex_encode_shift_zmm | Zmm | k-mask | N |
| shr_logical | i32×16 | `VPSRLD zmm{k}{z}, zmm, imm8` | evex_encode_shift_zmm | Zmm | k-mask | N |
| shr_arith | i32×16 | `VPSRAD zmm{k}{z}, zmm, imm8` | evex_encode_shift_zmm | Zmm | k-mask | N |
| cmp_eq | f32×16 | `VCMPEQPS k, zmm, zmm` | evex_encode_cmp_zmm | Avx512Mask | produces k-reg | N; result type changes to Avx512Mask |
| cmp_lt | f32×16 | `VCMPLTPS k, zmm, zmm` | evex_encode_cmp_zmm | Avx512Mask | — | N |
| cmp_le | f32×16 | `VCMPLEPS k, zmm, zmm` | evex_encode_cmp_zmm | Avx512Mask | — | N |
| mask_select | f32×16 | `VBLENDMPS zmm{k}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask selects src1 vs src2 | N; AVX-512F |
| reduce_sum | f32×16 | `VREDUCESS`... or `VADDPS` tree | evex_encode_reduce | Zmm | — | N; `_mm512_reduce_add_ps` §11.11 |
| reduce_max | f32×16 | `VREDUCEPS`... or tree | evex_encode_reduce | Zmm | — | N |
| reduce_min | f32×16 | tree via `VMINPS` + `VPERM2F128`-style | multiple | Zmm | — | S: tree; hardware reduce in AVX-512DQ |
| reduce_and | i32×16 | `VPANDD` tree | multiple | Zmm | — | S: tree |
| reduce_or | i32×16 | `VPORD` tree | multiple | Zmm | — | S: tree |
| permute | f32×16 | `VPERMPS zmm{k}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N; full 512-bit cross-lane |
| shuffle | i32×16 | `VPERMD zmm{k}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |
| broadcast_lane | f32×16 | `VBROADCASTSS zmm, xmm` | evex_encode_broadcast | Zmm | — | N |
| interleave_lo | f32×16 | `VUNPCKLPS zmm{k}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N; interleaves within 128b chunks |
| interleave_hi | f32×16 | `VUNPCKHPS zmm{k}, zmm, zmm` | evex_encode_3op_zmm | Zmm | k-mask | N |

### 2.5 ARM SVE2 (Scalable)

Reference: ARM Architecture Reference Manual ARMv9-A, §C11–C16 (SVE). ACLE SVE2 §11. Default predication: `_z` (zero-inactive). P15 reserved per ACLE convention. `vscale` = VL/128 in multiples of 128-bit.

| Abstract op | Type | Native opcode(s) | Encoder helper | Reg class | Mask/pred handling | Notes |
|-------------|------|-----------------|----------------|-----------|-------------------|-------|
| splat | f32/vl | `DUP Zd.S, Rn` | sve_encode_2reg_pred | Sve | pg-all-true implied | N; ARMv9 §C11.4.68 |
| splat | i32/vl | `DUP Zd.S, Rn` | sve_encode_2reg_pred | Sve | — | N |
| load_aligned | f32/vl | `LD1W Zd.S, Pg/Z, [Rn]` | sve_encode_load | Sve | Pg governs; _z zero-fill | N; §C11.4.117 |
| load_unaligned | f32/vl | `LD1W Zd.S, Pg/Z, [Rn]` | sve_encode_load | Sve | same; SVE tolerates unaligned | N |
| store_aligned | f32/vl | `ST1W Zd.S, Pg, [Rn]` | sve_encode_store | Sve | Pg governs; inactive = no-op | N; §C11.4.218 |
| store_unaligned | f32/vl | `ST1W Zd.S, Pg, [Rn]` | sve_encode_store | Sve | same | N |
| gather | f32/vl | `LD1W Zd.S, Pg/Z, [Rn, Zm.S, SXTW]` | sve_encode_gather_ld | Sve | Pg governs | N; §C11.4.105 |
| scatter | f32/vl | `ST1W Zd.S, Pg, [Rn, Zm.S, SXTW]` | sve_encode_scatter_st | Sve | Pg governs | N; §C11.4.201 |
| add | f32/vl | `FADD Zd.S, Pg/M, Zn.S, Zm.S` | sve_encode_3reg_pred | Sve | _z default (emit Pg/Z form) | N; §C11.4.91 |
| sub | f32/vl | `FSUB Zd.S, Pg/M, Zn.S, Zm.S` | sve_encode_3reg_pred | Sve | _z | N |
| mul | f32/vl | `FMUL Zd.S, Pg/M, Zn.S, Zm.S` | sve_encode_3reg_pred | Sve | _z | N |
| fma | f32/vl | `FMLA Zd.S, Pg/M, Zn.S, Zm.S` | sve_encode_3reg_pred | Sve | _z | N; §C11.4.100 |
| fnmadd | f32/vl | `FMLS Zd.S, Pg/M, Zn.S, Zm.S` | sve_encode_3reg_pred | Sve | _z | N |
| abs | f32/vl | `FABS Zd.S, Pg/M, Zn.S` | sve_encode_2reg_pred | Sve | _z | N; §C11.4.79 |
| neg | f32/vl | `FNEG Zd.S, Pg/M, Zn.S` | sve_encode_2reg_pred | Sve | _z | N |
| min | f32/vl | `FMIN Zd.S, Pg/M, Zn.S, Zm.S` | sve_encode_3reg_pred | Sve | _z | N |
| max | f32/vl | `FMAX Zd.S, Pg/M, Zn.S, Zm.S` | sve_encode_3reg_pred | Sve | _z | N |
| and | i32/vl | `AND Zd.D, Zn.D, Zm.D` (unpred) | sve_encode_3reg_unpred | Sve | unpredicated bitwise | N; §C11.4.9 |
| or | i32/vl | `ORR Zd.D, Zn.D, Zm.D` | sve_encode_3reg_unpred | Sve | unpredicated | N |
| xor | i32/vl | `EOR Zd.D, Zn.D, Zm.D` | sve_encode_3reg_unpred | Sve | unpredicated | N |
| andnot | i32/vl | `BIC Zd.D, Zn.D, Zm.D` | sve_encode_3reg_unpred | Sve | unpredicated | N |
| shl | i32/vl | `LSL Zd.S, Pg/M, Zn.S, #imm` | sve_encode_shift_pred | Sve | _z | N |
| shr_logical | i32/vl | `LSR Zd.S, Pg/M, Zn.S, #imm` | sve_encode_shift_pred | Sve | _z | N |
| shr_arith | i32/vl | `ASR Zd.S, Pg/M, Zn.S, #imm` | sve_encode_shift_pred | Sve | _z | N |
| cmp_eq | f32/vl | `FCMPEQ Pd.S, Pg/Z, Zn.S, Zm.S` | sve_encode_cmp_pred | SvePred | result in P-reg | N; §C11.4.88 |
| cmp_lt | f32/vl | `FCMLT Pd.S, Pg/Z, Zn.S, Zm.S` | sve_encode_cmp_pred | SvePred | P-reg | N |
| cmp_le | f32/vl | `FCMLE Pd.S, Pg/Z, Zn.S, Zm.S` | sve_encode_cmp_pred | SvePred | P-reg | N |
| mask_select | f32/vl | `SEL Zd.S, Pg, Zn.S, Zm.S` | sve_encode_sel | Sve | Pg selects Zn vs Zm | N; §C11.4.178 |
| reduce_sum | f32/vl | `FADDA Sd, Pg, Sd, Zn.S` | sve_encode_reduce_pred | Sve | ordered reduce | N; §C11.4.90 |
| reduce_max | f32/vl | `FMAXV Sd, Pg, Zn.S` | sve_encode_reduce_pred | Sve | — | N |
| reduce_min | f32/vl | `FMINV Sd, Pg, Zn.S` | sve_encode_reduce_pred | Sve | — | N |
| reduce_and | i32/vl | `ANDV Bd, Pg, Zn.B` | sve_encode_reduce_pred | Sve | — | N |
| reduce_or | i32/vl | `ORV Bd, Pg, Zn.B` | sve_encode_reduce_pred | Sve | — | N |
| permute | f32/vl | `TBL Zd.S, {Zn.S}, Zm.S` | sve_encode_tbl | Sve | — | N; full VL indexed; §C11.4.226 |
| shuffle | f32/vl | `TBL Zd.S, {Zn.S}, Zm.S` | sve_encode_tbl | Sve | static idx→const Zm | N |
| broadcast_lane | f32/vl | `DUP Zd.S, Zn.S[imm]` | sve_encode_dup_idx | Sve | — | N; §C11.4.68 |
| interleave_lo | f32/vl | `ZIP1 Zd.S, Zn.S, Zm.S` | sve_encode_zip1 | Sve | — | N; §C11.4.235 |
| interleave_hi | f32/vl | `ZIP2 Zd.S, Zn.S, Zm.S` | sve_encode_zip2 | Sve | — | N |

### 2.6 RVV 1.0 (Scalable)

Reference: RISC-V V Extension 1.0 specification, §7 (config), §8–§11 (arith), §12 (load/store), §13 (permute), §14 (reduction). Default LMUL=1, SEW=32. Mask source: v0 only. `vmv1r.v v0, vX` emitted before each masked op.

| Abstract op | Type | Native opcode(s) | Encoder helper | Reg class | Mask/pred handling | Notes |
|-------------|------|-----------------|----------------|-----------|-------------------|-------|
| splat | f32/vl | `vfmv.v.f vd, fs1` | rvv_encode_3reg_vx | Rvv | vm=1 (unmasked) | N; V §11.16 |
| splat | i32/vl | `vmv.v.x vd, rs1` | rvv_encode_3reg_vx | Rvv | vm=1 | N; V §11.15 |
| load_aligned | f32/vl | `vle32.v vd, (rs1)` + vsetvli | rvv_encode_load_stride | Rvv | vm=0 + vmv1r for mask | N; V §7.4 |
| load_unaligned | f32/vl | `vle32.v vd, (rs1)` | rvv_encode_load_stride | Rvv | same | N; no alignment fault |
| store_aligned | f32/vl | `vse32.v vs3, (rs1)` | rvv_encode_store | Rvv | vm=0 | N |
| store_unaligned | f32/vl | `vse32.v vs3, (rs1)` | rvv_encode_store | Rvv | vm=0 | N |
| gather | f32/vl | `vluxei32.v vd, (rs1), vs2` | rvv_encode_gather | Rvv | vm=0 | N; V §7.7 (indexed unordered) |
| scatter | f32/vl | `vsuxei32.v vs3, (rs1), vs2` | rvv_encode_scatter | Rvv | vm=0 | N; V §7.7 |
| add | f32/vl | `vfadd.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0; emit vmv1r pre-op | N; V §13.2 |
| sub | f32/vl | `vfsub.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0 | N |
| mul | f32/vl | `vfmul.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0 | N |
| fma | f32/vl | `vfmadd.vv vd, vs1, vs2` | rvv_encode_3reg_vv | Rvv | vm=0 | N; V §13.6 (vd = vd*vs1+vs2) |
| fnmadd | f32/vl | `vfnmadd.vv vd, vs1, vs2` | rvv_encode_3reg_vv | Rvv | vm=0 | N |
| abs | f32/vl | `vfsgnjx.vv vd, vs2, vs2` | rvv_encode_3reg_vv | Rvv | vm=0 | N; sign-inject same src; V §13.11 |
| neg | f32/vl | `vfsgnjn.vv vd, vs2, vs2` | rvv_encode_3reg_vv | Rvv | vm=0 | N |
| min | f32/vl | `vfmin.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0 | N; V §13.4 |
| max | f32/vl | `vfmax.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0 | N |
| and | i32/vl | `vand.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0 | N; V §11.1 |
| or | i32/vl | `vor.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0 | N |
| xor | i32/vl | `vxor.vv vd, vs2, vs1` | rvv_encode_3reg_vv | Rvv | vm=0 | N |
| andnot | i32/vl | `vnot.v` (pseudo) + AND | rvv_encode_vnot + and | Rvv | vm=0 | S: `vxor.vi vt,vs2,-1` then `vand.vv` |
| shl | i32/vl | `vsll.vx vd, vs2, rs1` | rvv_encode_3reg_vx | Rvv | vm=0 | N; V §11.3 |
| shr_logical | i32/vl | `vsrl.vx vd, vs2, rs1` | rvv_encode_3reg_vx | Rvv | vm=0 | N |
| shr_arith | i32/vl | `vsra.vx vd, vs2, rs1` | rvv_encode_3reg_vx | Rvv | vm=0 | N |
| cmp_eq | f32/vl | `vmfeq.vv vd, vs2, vs1` | rvv_encode_3reg_vv | RvvMask | result in vd as mask | N; V §13.13 |
| cmp_lt | f32/vl | `vmflt.vv vd, vs2, vs1` | rvv_encode_3reg_vv | RvvMask | — | N |
| cmp_le | f32/vl | `vmfle.vv vd, vs2, vs1` | rvv_encode_3reg_vv | RvvMask | — | N |
| mask_select | f32/vl | `vmerge.vvm vd, vs2, vs1, v0` | rvv_encode_3reg_vv | Rvv | v0 governs; emit vmv1r | N; V §11.15 |
| reduce_sum | f32/vl | `vfredusum.vs vd, vs2, vs1` | rvv_encode_reduce | Rvv | vm=0; result in vd[0] | N; V §14.3 |
| reduce_max | f32/vl | `vfredmax.vs vd, vs2, vs1` | rvv_encode_reduce | Rvv | — | N |
| reduce_min | f32/vl | `vfredmin.vs vd, vs2, vs1` | rvv_encode_reduce | Rvv | — | N |
| reduce_and | i32/vl | `vredand.vs vd, vs2, vs1` | rvv_encode_reduce | Rvv | vm=0 | N; V §14.1 |
| reduce_or | i32/vl | `vredor.vs vd, vs2, vs1` | rvv_encode_reduce | Rvv | vm=0 | N |
| permute | f32/vl | `vrgather.vv vd, vs2, vs1` | rvv_encode_gather | Rvv | vm=0 | N; V §15.4 |
| shuffle | i32/vl | `vrgather.vv vd, vs2, vs1` | rvv_encode_gather | Rvv | static idx in vs1 | N |
| broadcast_lane | f32/vl | `vrgather.vi vd, vs2, imm` | rvv_encode_3reg_vi | Rvv | vm=0; uimm5 idx | N |
| interleave_lo | f32/vl | `vslideup.vx` + `vrgather` | two helpers | Rvv | vm=0 | S: no native interleave; §15.3 |
| interleave_hi | f32/vl | `vslidedown.vx` + `vrgather` | two helpers | Rvv | vm=0 | S |

### 2.7 NVIDIA PTX (Warp/32)

Reference: NVIDIA PTX ISA Reference 8.x. §5 (types), §8.2 (predicate regs), §9.7 (vector ops). Warp = 32 threads; each thread executes scalar; "vector" semantics come from all threads in a warp executing in lockstep. No physical vector register file — warp-level coordination via predicate regs and shfl.sync. PTX is SSA text; no physical register allocator.

> **Trait scoping (reconciles with B1 §7.4 — read before consuming this table):**
> The "Abstract op" column here mixes two B1 traits because PTX is the join point of both:
>
> - **Per-thread elementwise ops** (`splat`, `load_*`, `store_*`, `gather`, `scatter`, `add`, `sub`, `mul`, `fma`, `fnmadd`, `abs`, `neg`, `min`, `max`, `and`/`or`/`xor`/`andnot`, `shl`/`shr_*`, `cmp_*`, `mask_select`) lower from the regular `Vector` trait — each thread executes the scalar PTX op on its own data, and "lane count = 1 per thread, 32 threads = 1 warp" is the implicit packing. These rows are how `FixedVec<T,N>` ops bottom out when a kernel is launched: the compiler strip-mines the `N` lanes across the warp's 32 threads.
> - **Cross-lane / warp-collective ops** (`reduce_sum`, `reduce_max`, `reduce_min`, `reduce_and`, `reduce_or`, `permute`, `shuffle`, `broadcast_lane`, `interleave_lo`, `interleave_hi`) lower from the **`WarpVec<T>` extension trait** (B1 §7.3). They have no `Vector`-trait analog because their semantics are warp-scoped — the result depends on what other threads in the warp hold. A user who writes `Vector::reduce_sum` on a CUDA target is rejected at type-check; they must `WarpVec::warp_reduce_sum` explicitly, per B1's "no implicit warp coercion" rule.
>
> `ScalableVec<T>` has **no PTX rows** by design (B1 §7.4 finding 4: `SubgroupSize` portability gap). Any attempt to lower `ScalableVec<T>` to a CUDA target is a hard semantic error, not a synthesis fallback.

| Abstract op | Type | PTX instruction | Emit helper | Reg class | Mask/pred handling | Notes |
|-------------|------|----------------|-------------|-----------|-------------------|-------|
| splat | f32 (all lanes) | `mov.f32 %fd, val;` | ptx_emit_mov | virtual | — | each thread holds scalar; splat = uniform mov |
| splat | i32 | `mov.b32 %rd, val;` | ptx_emit_mov | virtual | — | N |
| load_aligned | f32 | `ld.global.f32 %fd, [%rd];` | ptx_emit_ld_global | virtual | `@%p setp` guard | N; PTX §8.7 |
| load_unaligned | f32 | `ld.global.f32 %fd, [%rd];` | ptx_emit_ld_global | virtual | same | N; PTX no separate unaligned op |
| store_aligned | f32 | `st.global.f32 [%rd], %fd;` | ptx_emit_st_global | virtual | `@%p` guard | N |
| store_unaligned | f32 | `st.global.f32 [%rd], %fd;` | ptx_emit_st_global | virtual | same | N |
| gather | f32 | `ld.global.f32 %fd, [%rd+offset];` | ptx_emit_gather | virtual | `@%p` | N; thread-local offsets differ; natural gather |
| scatter | f32 | `st.global.f32 [%rd+offset], %fd;` | ptx_emit_scatter | virtual | `@%p` | N |
| add | f32 | `add.f32 %fd, %fa, %fb;` | ptx_emit_binop | virtual | `@%p` | N |
| sub | f32 | `sub.f32 %fd, %fa, %fb;` | ptx_emit_binop | virtual | `@%p` | N |
| mul | f32 | `mul.f32 %fd, %fa, %fb;` | ptx_emit_binop | virtual | `@%p` | N |
| fma | f32 | `fma.rn.f32 %fd, %fa, %fb, %fc;` | ptx_emit_fma | virtual | `@%p` | N; PTX §9.7.6 |
| fnmadd | f32 | `fma.rn.f32 %fd, neg(%fa), %fb, %fc;` | ptx_emit_fma_neg | virtual | `@%p` | S: negate via neg() modifier |
| abs | f32 | `abs.f32 %fd, %fa;` | ptx_emit_unop | virtual | `@%p` | N |
| neg | f32 | `neg.f32 %fd, %fa;` | ptx_emit_unop | virtual | `@%p` | N |
| min | f32 | `min.f32 %fd, %fa, %fb;` | ptx_emit_binop | virtual | `@%p` | N |
| max | f32 | `max.f32 %fd, %fa, %fb;` | ptx_emit_binop | virtual | `@%p` | N |
| and | b32 | `and.b32 %rd, %ra, %rb;` | ptx_emit_binop | virtual | `@%p` | N |
| or | b32 | `or.b32 %rd, %ra, %rb;` | ptx_emit_binop | virtual | `@%p` | N |
| xor | b32 | `xor.b32 %rd, %ra, %rb;` | ptx_emit_binop | virtual | `@%p` | N |
| andnot | b32 | `not.b32 %t, %rb;` + `and.b32` | two ptx_emit | virtual | `@%p` | S |
| shl | b32 | `shl.b32 %rd, %ra, %rb;` | ptx_emit_shift | virtual | `@%p` | N |
| shr_logical | b32 | `shr.u32 %rd, %ra, %rb;` | ptx_emit_shift | virtual | `@%p` | N |
| shr_arith | b32 | `shr.s32 %rd, %ra, %rb;` | ptx_emit_shift | virtual | `@%p` | N |
| cmp_eq | f32 | `setp.eq.f32 %p, %fa, %fb;` | ptx_emit_setp | pred-virtual | result in %p reg | N; §8.2 |
| cmp_lt | f32 | `setp.lt.f32 %p, %fa, %fb;` | ptx_emit_setp | pred-virtual | — | N |
| cmp_le | f32 | `setp.le.f32 %p, %fa, %fb;` | ptx_emit_setp | pred-virtual | — | N |
| mask_select | f32 | `selp.f32 %fd, %fa, %fb, %p;` | ptx_emit_selp | virtual | %p selects a vs b | N; §9.3 |
| reduce_sum | f32 | `shfl.sync.down.b32` tree | ptx_emit_warp_reduce | virtual | warp-level | N; §9.7.11 shfl tree |
| reduce_max | f32 | `shfl.sync.down.b32` + `max.f32` tree | ptx_emit_warp_reduce | virtual | warp-level | S: shfl + max tree |
| reduce_min | f32 | `shfl.sync.down.b32` + `min.f32` tree | ptx_emit_warp_reduce | virtual | warp-level | S: shfl + min tree |
| reduce_and | b32 | `shfl.sync.down.b32` + `and.b32` tree | ptx_emit_warp_reduce | virtual | warp-level | S |
| reduce_or | b32 | `shfl.sync.down.b32` + `or.b32` tree | ptx_emit_warp_reduce | virtual | warp-level | S |
| permute | f32 | `shfl.sync.idx.b32 %fd, %fa, %rb, 0x1f;` | ptx_emit_shfl | virtual | mask=0x1f full warp | N; §9.7.11 |
| shuffle | f32 | `shfl.sync.idx.b32` with const lane | ptx_emit_shfl | virtual | — | N |
| broadcast_lane | f32 | `shfl.sync.idx.b32 %fd, %fa, lane_id, 0x1f;` | ptx_emit_shfl | virtual | lane_id = const | N |
| interleave_lo | f32 | `shfl.sync` + conditional select | ptx_emit_shfl + selp | virtual | warp mask | S |
| interleave_hi | f32 | `shfl.sync` + conditional select | ptx_emit_shfl + selp | virtual | warp mask | S |

### 2.8 SPIR-V Vulkan (Subgroup)

Reference: SPIR-V Specification 1.6 §3.37 (opcodes), §3.42 (capabilities). Vulkan 1.3 `VK_KHR_shader_subgroup_extended_types`. Each SPIR-V instruction encodes as a 32-bit word header + operand words. No physical registers — SSA %id values. Subgroup ops require `SubgroupSize` capability. Vector types = `OpTypeVector`.

| Abstract op | Type | SPIR-V instruction | Emit helper | Reg class | Mask/pred handling | Notes |
|-------------|------|--------------------|-------------|-----------|-------------------|-------|
| splat | f32×N | `OpCompositeConstruct` (N copies) | spirv_emit_composite_construct | virtual | — | N; SPIR-V §3.42.11 |
| splat | scalar→vec | `OpVectorSplat` (ext) or Construct | spirv_emit_splat | virtual | — | S: no single-op; use OpCompositeConstruct |
| load_aligned | f32×N | `OpLoad` %vec_type %ptr | spirv_emit_load | virtual | `OpSelect` post-load | N; §3.42.8 |
| load_unaligned | f32×N | `OpLoad` | spirv_emit_load | virtual | same | N |
| store_aligned | f32×N | `OpStore` %ptr %val | spirv_emit_store | virtual | `OpSelect` mask | N |
| store_unaligned | f32×N | `OpStore` | spirv_emit_store | virtual | same | N |
| gather | f32×N | loop of `OpAccessChain` + `OpLoad` | spirv_emit_gather_loop | virtual | `OpSelect` | S: no native gather in base SPIR-V |
| scatter | f32×N | loop of `OpAccessChain` + `OpStore` | spirv_emit_scatter_loop | virtual | `OpSelect` | S |
| add | f32×N | `OpFAdd` %res %a %b | spirv_emit_binop | virtual | `OpSelect` blend | N |
| sub | f32×N | `OpFSub` | spirv_emit_binop | virtual | `OpSelect` | N |
| mul | f32×N | `OpFMul` | spirv_emit_binop | virtual | `OpSelect` | N |
| fma | f32×N | `OpExtInst GLSL.std.450 Fma` | spirv_emit_glsl_ext | virtual | `OpSelect` | N; GLSL.std.450 §26 |
| fnmadd | f32×N | `OpExtInst GLSL.std.450 Fma` (neg a) | spirv_emit_glsl_ext | virtual | `OpSelect` | S: negate first operand |
| abs | f32×N | `OpExtInst GLSL.std.450 FAbs` | spirv_emit_glsl_ext | virtual | `OpSelect` | N; §43 |
| neg | f32×N | `OpFNegate` | spirv_emit_unop | virtual | `OpSelect` | N |
| min | f32×N | `OpExtInst GLSL.std.450 FMin` | spirv_emit_glsl_ext | virtual | `OpSelect` | N |
| max | f32×N | `OpExtInst GLSL.std.450 FMax` | spirv_emit_glsl_ext | virtual | `OpSelect` | N |
| and | i32×N | `OpBitwiseAnd` | spirv_emit_binop | virtual | `OpSelect` | N |
| or | i32×N | `OpBitwiseOr` | spirv_emit_binop | virtual | `OpSelect` | N |
| xor | i32×N | `OpBitwiseXor` | spirv_emit_binop | virtual | `OpSelect` | N |
| andnot | i32×N | `OpNot` + `OpBitwiseAnd` | two spirv_emit | virtual | `OpSelect` | S |
| shl | i32×N | `OpShiftLeftLogical` | spirv_emit_shift | virtual | `OpSelect` | N |
| shr_logical | i32×N | `OpShiftRightLogical` | spirv_emit_shift | virtual | `OpSelect` | N |
| shr_arith | i32×N | `OpShiftRightArithmetic` | spirv_emit_shift | virtual | `OpSelect` | N |
| cmp_eq | f32×N | `OpFOrdEqual` → bool vec | spirv_emit_cmp | virtual | — | N; §3.42.16 |
| cmp_lt | f32×N | `OpFOrdLessThan` | spirv_emit_cmp | virtual | — | N |
| cmp_le | f32×N | `OpFOrdLessThanEqual` | spirv_emit_cmp | virtual | — | N |
| mask_select | f32×N | `OpSelect` %cond %true %false | spirv_emit_select | virtual | bool vector condition | N |
| reduce_sum | f32 (scalar out) | `OpGroupNonUniformFAdd Reduce` | spirv_emit_subgroup_reduce | virtual | SubgroupSize | N; Vulkan `VK_KHR_shader_subgroup` |
| reduce_max | f32 | `OpGroupNonUniformFMax Reduce` | spirv_emit_subgroup_reduce | virtual | SubgroupSize | N |
| reduce_min | f32 | `OpGroupNonUniformFMin Reduce` | spirv_emit_subgroup_reduce | virtual | SubgroupSize | N |
| reduce_and | i32 | `OpGroupNonUniformBitwiseAnd Reduce` | spirv_emit_subgroup_reduce | virtual | SubgroupSize | N |
| reduce_or | i32 | `OpGroupNonUniformBitwiseOr Reduce` | spirv_emit_subgroup_reduce | virtual | SubgroupSize | N |
| permute | f32×N | `OpGroupNonUniformShuffle` | spirv_emit_subgroup_shuffle | virtual | SubgroupSize | N; runtime index |
| shuffle | f32×N | `OpVectorShuffle` (compile-time) | spirv_emit_vector_shuffle | virtual | — | N; indices in instruction |
| broadcast_lane | f32×N | `OpGroupNonUniformBroadcast` | spirv_emit_subgroup_broadcast | virtual | SubgroupSize | N |
| interleave_lo | f32×N | `OpVectorShuffle` even indices | spirv_emit_vector_shuffle | virtual | — | S: compile-time shuffle |
| interleave_hi | f32×N | `OpVectorShuffle` odd indices | spirv_emit_vector_shuffle | virtual | — | S |

---

## 3. Synthesis Tables for Missing Native Opcodes

### 3.1 NEON: Masked Arithmetic (no native mask register)

All masked ops follow this template (Survey §5.4):
```
# masked_add(a, b, mask) → result
t  = op(a, b)          # e.g., FADD Vt.4S, Va.4S, Vb.4S
result = BSL(mask, t, a)  # BSL Vd.16B, Vt.16B, Va.16B
                           # BSL: Vd[i] = (mask[i]=1) ? Vt[i] : Va[i]
```
Cost: 1 extra NEON instruction per masked op. `mask` is a full-width lane-mask vector (0xFF...FF per active lane) from a prior `cmp` op.

### 3.2 NEON: Gather (no native indexed load)
```
# gather(base, indices[4]) → Vec4f
t0 = LDR Ss0, [base + indices[0]*4]
t1 = LDR Ss1, [base + indices[1]*4]
t2 = LDR Ss2, [base + indices[2]*4]
t3 = LDR Ss3, [base + indices[3]*4]
INS Vd.S[0], Ws0
INS Vd.S[1], Ws1
INS Vd.S[2], Ws2
INS Vd.S[3], Ws3
```
Cost: 4 scalar loads + 4 INS = 8 instructions. Cannot avoid on AArch64 ASIMD without SVE.

### 3.3 NEON: Scatter
```
# scatter(base, indices[4], data)
UMOV Ws0, Vd.S[0]; STR Ws0, [base + indices[0]*4]
UMOV Ws1, Vd.S[1]; STR Ws1, [base + indices[1]*4]
UMOV Ws2, Vd.S[2]; STR Ws2, [base + indices[2]*4]
UMOV Ws3, Vd.S[3]; STR Ws3, [base + indices[3]*4]
```

### 3.4 NEON: reduce_sum f32×4
```
FADDP Vt.4S, Vs.4S, Vs.4S   # pairwise add → 2 sums in lo half
FADDP Sd, Vt.2S              # pairwise add → scalar result
```
Total: 2 instructions.

### 3.5 SSE2/SSE3: reduce_sum f32×4
SSE3 path (preferred):
```
HADDPS xmm0, xmm0    # [a+b, c+d, a+b, c+d]
HADDPS xmm0, xmm0    # [a+b+c+d, ...]
```
SSE2 fallback:
```
SHUFPS xmm1, xmm0, 0x4E   # [c, d, a, b]
ADDPS  xmm0, xmm1          # [a+c, b+d, ...]
SHUFPS xmm1, xmm0, 0x11   # [b+d, a+c, ...]
ADDPS  xmm0, xmm1          # [a+b+c+d, ...]
```

### 3.6 SSE2/SSE4: mask_select
SSE4.1 path (preferred):
```
BLENDVPS xmmd, xmms, XMM0    # XMM0 implicit mask operand
```
SSE2 fallback (3-op and/andnot/or triplet):
```
ANDPS  xmm_t,    mask, a       # t = mask & a (true-lanes)
ANDNPS xmm_mask, mask, b       # ~mask & b    (false-lanes)
ORPS   xmm_r,  xmm_t, xmm_mask  # result
```

### 3.7 AVX2: Scatter (no native)
```
# scatter(base, ymm_indices, ymm_data, scale=4) for f32×8
# Extract and store 8 lanes:
for i in 0..8:
  VPEXTRD eax, ymm_data_xmm_lo_or_hi, i%4    # or VEXTRACTF128 first
  MOV [base + index[i]*scale], eax
```
VPEXTRD handles 4 lanes per XMM half; emit `VEXTRACTF128` to get upper 128b first.

### 3.8 AVX2: reduce_sum f32×8
```
VEXTRACTF128 xmm1, ymm0, 1    # upper 128b
VADDPS       xmm0, xmm0, xmm1 # fold 256→128
VHADDPS      xmm0, xmm0, xmm0 # pairwise
VHADDPS      xmm0, xmm0, xmm0 # scalar result in xmm0[0]
```

### 3.9 RVV: andnot
```
vxor.vi vt, vs2, -1    # ~vs2 (all-ones xor)
vand.vv vd, vt, vs1    # vd = ~vs2 & vs1
```

### 3.10 RVV: mask register pressure (vmv1r strategy)
Before any `vm=0` instruction where `Mask<N>` is in register `vX` (not v0):
```
vmv1r.v v0, vX    # move mask into v0; one cycle on all known RVV impls
<masked op>       # uses v0 implicitly
```
Emit `vmv1r.v v0, vX` inline; a future optimizer pass may hoist/coalesce repeated vmv1r within a basic block.

### 3.11 RVV: interleave_lo / interleave_hi
No native zip/interleave. Synthesize with vrgather:
```
# interleave_lo(va, vb) for element type e32, vl lanes
# Build index vector: [0, vl, 1, vl+1, 2, vl+2, ...]
# Store va and vb in adjacent vector-reg group (e.g., v2=va, v4=vb, then treat as 2-group)
# Use vrgather.vv with the index vector
vsetvli t0, ..., e32, m2    # double LMUL to address both regs
# construct index via viota.m or vmv.v.i + vslideup
vrgather.vv vd, vsrc_group, vidx
```
This is non-trivial; a simpler fallback is scalar extraction loop.

### 3.12 SPIR-V: Gather / Scatter
No base SPIR-V instruction for indexed gather from a raw buffer. Map via SSBO (storage buffer):
```
# gather(base_ptr, indices[N]) for each lane i:
%elem_ptr = OpAccessChain %ptr_type %base_ptr %index_i
%val      = OpLoad %f32 %elem_ptr
```
Emit as a straight-line sequence of N `OpAccessChain`+`OpLoad` pairs within the shader. For variable runtime indices, unroll or use a loop construct (OpLoopMerge).

### 3.13 PTX: Warp-level reduce_sum (shfl tree)
```
# 5-stage binary tree for 32-lane warp
.reg .f32 %t;
shfl.sync.down.b32 %t|%p, %val, 16, 0x1f, 0xffffffff;
add.f32 %val, %val, %t;
shfl.sync.down.b32 %t|%p, %val, 8, 0x1f, 0xffffffff;
add.f32 %val, %val, %t;
shfl.sync.down.b32 %t|%p, %val, 4, 0x1f, 0xffffffff;
add.f32 %val, %val, %t;
shfl.sync.down.b32 %t|%p, %val, 2, 0x1f, 0xffffffff;
add.f32 %val, %val, %t;
shfl.sync.down.b32 %t|%p, %val, 1, 0x1f, 0xffffffff;
add.f32 %val, %val, %t;
# %val in lane 0 holds the sum
```
Replace `add.f32` with `max.f32` / `min.f32` / `and.b32` / `or.b32` for other reductions.

---

## 4. Register Allocation Contracts

### 4.1 NEON / AArch64 ASIMD
- Registers: V0–V31 as 128-bit Q-registers (arm_neon.spl, `MachRegKind.Neon128`).
- Encoding: `physical_reg(MachRegKind.Neon128, id)` where `id` ∈ [0,31].
- Caller-saved: V0–V7 (AArch64 ABI); callee-saved: V8–V15 (low 64b); V16–V31 temp.
- No mask register. Mask values are held in any Vn (lane-mask vector).
- **File:** `src/compiler/70.backend/backend/native/arm_neon.spl` (existing).

### 4.2 x86 SSE2/SSE4
- Registers: XMM0–XMM15 (x86-64 ABI).
- Encoding: `xmm_to_index` pattern (x86_64_simd.spl, existing).
- `MachRegKind.Xmm` (existing or to be confirmed in mach_inst.spl).
- BLENDVPS uses XMM0 implicit; allocator must pin mask operand to XMM0 at BLENDVPS use sites.
- **File:** `src/compiler/70.backend/backend/native/x86_64_simd.spl` (existing, SSE section).

### 4.3 x86 AVX2
- Registers: YMM0–YMM15 (x86-64); YMM16–YMM31 added by AVX-512.
- Encoding: `ymm_to_index` (x86_64_simd.spl:167 pattern).
- `MachRegKind.Ymm` (existing or to be confirmed).
- **File:** `src/compiler/70.backend/backend/native/x86_64_simd.spl` (existing, AVX2 section).

### 4.4 x86 AVX-512
- Data registers: ZMM0–ZMM31 (`MachRegKind.Zmm`, new).
- Mask registers: k0–k7 (`MachRegKind.Avx512Mask`, new). **k0 hardwired all-ones — never allocate k0 for a Mask<N> value; reserve as "no mask" sentinel.**
- Allocatable mask regs: k1–k7 (7 allocatable mask registers).
- Encoding: `zmm_to_index(id)` (new, range 0–31); `kmask_to_index(id)` (range 1–7).
- **New file:** `src/compiler/70.backend/backend/native/x86_64_avx512.spl`.

### 4.5 ARM SVE2
- Data registers: Z0–Z31 (`MachRegKind.Sve`, new). Width = VL bits (runtime).
- Predicate registers: P0–P15 (`MachRegKind.SvePred`, new).
  - **P15 reserved** per ACLE §11.1 convention (do not allocate to user values).
  - P0–P14 allocatable (15 predicate registers).
  - p0 conventional "all-true" governing predicate for unconditional ops.
- Encoding: `sve_zreg_id(id)` → 5-bit field; `sve_preg_id(id)` → 4-bit field.
- `svcntw()` equivalent emitted as `RDVL` or `CNTW` instruction to query runtime VL.
- **New file:** `src/compiler/70.backend/backend/native/arm_sve2.spl`.

### 4.6 RVV 1.0
- Registers: V0–V31 (`MachRegKind.Rvv`, new). Width = VLEN×LMUL/SEW elements.
- **v0 reserved for mask operations** (source for `.vm=0` instructions). Allocate mask values to any vX, but emit `vmv1r.v v0, vX` before masked use (§3.10).
- LMUL grouping rules:
  - LMUL=1: any V0–V31 (each register independent).
  - LMUL=2: V0,V2,V4,...,V30 (even-aligned pairs).
  - LMUL=4: V0,V4,V8,V12,V16,V20,V24,V28.
  - LMUL=8: V0,V8,V16,V24.
  - Fractional LMUL (mf2, mf4, mf8): any register; occupies sub-register.
- Default: LMUL=1 (B1 architectural decision). Backend emits `vsetvli t0, a0, e32, m1, ta, ma` at each loop prolog.
- **New file:** `src/compiler/70.backend/backend/native/riscv_rvv.spl`.

### 4.7 NVIDIA PTX
- PTX is SSA / virtual register model. No physical allocation at emit time.
- Register types: `.reg .f32`, `.reg .b32`, `.reg .pred` (1-bit predicate, `%pX`).
- `.v2` and `.v4` packed types for ld/st only (e.g., `ld.global.v4.f32 {%f0,%f1,%f2,%f3}, [%rd]`).
- The CUDA assembler (ptxas) performs physical allocation.
- **File:** `src/compiler/70.backend/backend/cuda/ptx_builder.spl` (extend, see §5).

### 4.8 SPIR-V Vulkan
- SSA %id values; no physical registers.
- Vector types declared once with `OpTypeVector`.
- Subgroup ops require `OpCapability GroupNonUniform` + specific sub-capability per op family.
- **File:** `src/compiler/70.backend/backend/vulkan/spirv_builder.spl` (extend, see §5).

---

## 5. Encoder Helper Inventory

### 5.1 `arm_neon.spl` — Extensions (existing file)

Extend with helpers for ops not yet in the 383-line file:

```
fn neon_encode_f32x4_2reg(opcode_bits: i64, qd: i32, qn: i32) -> [i64]
fn neon_encode_bsl(qd: i32, qt: i32, qn: i32) -> [i64]         # BSL blend
fn neon_encode_dup_lane(qd: i32, qn: i32, idx: i32) -> [i64]   # DUP Vd.4S, Vn.S[idx]
fn neon_encode_tbl(qd: i32, qn: i32, qm: i32) -> [i64]         # TBL byte-table
fn neon_encode_zip1(qd: i32, qn: i32, qm: i32) -> [i64]        # ZIP1
fn neon_encode_zip2(qd: i32, qn: i32, qm: i32) -> [i64]        # ZIP2
fn neon_encode_faddp(qd: i32, qn: i32) -> [i64]                 # FADDP pairwise
fn neon_encode_fmaxv(sd: i32, qn: i32) -> [i64]                 # FMAXV scalar result
fn neon_encode_fminv(sd: i32, qn: i32) -> [i64]                 # FMINV
fn neon_encode_andv(bd: i32, qn: i32) -> [i64]                  # ANDV
fn neon_encode_orv(bd: i32, qn: i32) -> [i64]                   # ORV
fn neon_encode_shl_imm(qd: i32, qn: i32, imm: i32) -> [i64]
fn neon_encode_shr_imm(qd: i32, qn: i32, imm: i32, arith: bool) -> [i64]
fn neon_encode_ld1(qd: i32, rn: i32) -> [i64]
fn neon_encode_st1(qn: i32, rn: i32) -> [i64]
fn neon_encode_3reg_pred(opcode_bits: i64, qd: i32, qn: i32, qm: i32,
                          mask: i32) -> [i64]  # emits op + BSL
```

### 5.2 `x86_64_simd.spl` — Split Rationale

The file is 411 lines covering SSE+AVX2. Recommendation: **keep monolithic for SSE+AVX2** (they share VEX prefix logic and the file is manageable), and create a **separate new file for AVX-512** due to the qualitatively different EVEX encoding. Splitting SSE from AVX2 would fragment shared helper `_encode_simd_3op_xmm` / `_encode_simd_3op_ymm`.

Add to existing `x86_64_simd.spl`:
```
fn _encode_simd_blendvps(dest: i32, src: i32, mask_xmm0: i32) -> [i64]
fn _encode_simd_shufps(dest: i32, src1: i32, src2: i32, imm: i32) -> [i64]
fn _encode_simd_pshufd(dest: i32, src: i32, imm: i32) -> [i64]
fn _encode_vgatherdps(dest: i32, base: i32, vidx: i32, mask: i32, scale: i32) -> [i64]
fn _encode_vbroadcastss(dest: i32, src: i32) -> [i64]
fn _encode_vpermps(dest: i32, idx: i32, src: i32) -> [i64]
fn _encode_vblendvps(dest: i32, src1: i32, src2: i32, mask: i32) -> [i64]
fn _encode_vfmadd213ps(dest: i32, src1: i32, src2: i32) -> [i64]
fn _encode_vfnmadd213ps(dest: i32, src1: i32, src2: i32) -> [i64]
```

### 5.3 NEW `x86_64_avx512.spl`

```
fn evex_encode_3op_zmm(dest: i32, src1: i32, src2: i32,
                        k_mask: i32, zeroing: bool,
                        mmm: i32, w: i32, pp: i32, opcode: i32) -> [i64]
fn evex_encode_shift_zmm(dest: i32, src: i32, imm: i32,
                          k_mask: i32, zeroing: bool, opcode: i32) -> [i64]
fn evex_encode_cmp_zmm(k_dest: i32, src1: i32, src2: i32, imm: i32) -> [i64]
fn evex_encode_gather_zmm(dest: i32, base: i32, vidx: i32,
                           k_mask: i32, scale: i32) -> [i64]
fn evex_encode_scatter_zmm(base: i32, vidx: i32, src: i32,
                            k_mask: i32, scale: i32) -> [i64]
fn evex_encode_broadcast(dest: i32, src: i32, k_mask: i32) -> [i64]
fn evex_encode_reduce(dest: i32, src: i32, imm: i32) -> [i64]  # VREDUCEPS
fn zmm_to_index(reg: MachReg) -> i32
fn kmask_to_index(reg: MachReg) -> i32   # asserts != 0
```

### 5.4 NEW `arm_sve2.spl`

```
fn sve_encode_3reg_pred(opcode_bits: i64, zd: i32, pg: i32,
                         zn: i32, zm: i32) -> [i64]
fn sve_encode_3reg_unpred(opcode_bits: i64, zd: i32,
                           zn: i32, zm: i32) -> [i64]
fn sve_encode_2reg_pred(opcode_bits: i64, zd: i32, pg: i32, zn: i32) -> [i64]
fn sve_encode_cmp_pred(opcode_bits: i64, pd: i32, pg: i32,
                        zn: i32, zm: i32) -> [i64]
fn sve_encode_sel(zd: i32, pg: i32, zn: i32, zm: i32) -> [i64]
fn sve_encode_gather_ld(opcode_bits: i64, zd: i32, pg: i32,
                         base: i32, zoffset: i32) -> [i64]
fn sve_encode_scatter_st(opcode_bits: i64, zt: i32, pg: i32,
                          base: i32, zoffset: i32) -> [i64]
fn sve_encode_load(opcode_bits: i64, zd: i32, pg: i32, rn: i32) -> [i64]
fn sve_encode_store(opcode_bits: i64, zt: i32, pg: i32, rn: i32) -> [i64]
fn sve_encode_reduce_pred(opcode_bits: i64, sd: i32, pg: i32, zn: i32) -> [i64]
fn sve_encode_tbl(zd: i32, zn: i32, zm: i32) -> [i64]
fn sve_encode_dup_idx(zd: i32, zn: i32, imm: i32) -> [i64]
fn sve_encode_zip1(zd: i32, zn: i32, zm: i32) -> [i64]
fn sve_encode_zip2(zd: i32, zn: i32, zm: i32) -> [i64]
fn sve_encode_shift_pred(opcode_bits: i64, zd: i32, pg: i32,
                          zn: i32, imm: i32) -> [i64]
fn sve_encode_whilelt(pd: i32, rn: i32, rm: i32) -> [i64]  # loop predicate setup
fn sve_zreg_id(reg: MachReg) -> i32
fn sve_preg_id(reg: MachReg) -> i32
```

### 5.5 NEW `riscv_rvv.spl`

```
fn rvv_encode_vsetvli(rd: i32, rs1: i32, vtypei: i32) -> i64
fn rvv_encode_vsetvl(rd: i32, rs1: i32, rs2: i32) -> i64     # dynamic SEW/LMUL
fn rvv_encode_3reg_vv(opcode_bits: i64, vd: i32, vs2: i32,
                       vs1: i32, vm: bool) -> i64
fn rvv_encode_3reg_vx(opcode_bits: i64, vd: i32, vs2: i32,
                       rs1: i32, vm: bool) -> i64
fn rvv_encode_3reg_vi(opcode_bits: i64, vd: i32, vs2: i32,
                       imm5: i32, vm: bool) -> i64
fn rvv_encode_load_stride(opcode_bits: i64, vd: i32, rs1: i32,
                           rs2: i32, vm: bool) -> i64
fn rvv_encode_store_stride(opcode_bits: i64, vs3: i32, rs1: i32,
                            rs2: i32, vm: bool) -> i64
fn rvv_encode_gather(opcode_bits: i64, vd: i32, rs1: i32,
                      vs2: i32, vm: bool) -> i64    # vluxei32.v
fn rvv_encode_scatter(opcode_bits: i64, vs3: i32, rs1: i32,
                       vs2: i32, vm: bool) -> i64   # vsuxei32.v
fn rvv_encode_reduce(opcode_bits: i64, vd: i32, vs2: i32,
                      vs1: i32, vm: bool) -> i64
fn rvv_encode_vmv1r(vd: i32, vs2: i32) -> i64       # mask copy to v0
fn rvv_encode_vnot(vd: i32, vs2: i32, vm: bool) -> i64  # vxor.vi -1
fn rvv_vtype_imm(sew: i32, lmul: i32, ta: bool, ma: bool) -> i32
fn rvv_vreg_id(reg: MachReg) -> i32
```

### 5.6 `ptx_builder.spl` — Extensions (existing file, 538 lines)

Add to the existing PTX builder:
```
fn ptx_emit_mov(dest: text, ty: text, val: text) -> text
fn ptx_emit_binop(dest: text, op: text, ty: text, a: text, b: text) -> text
fn ptx_emit_unop(dest: text, op: text, ty: text, a: text) -> text
fn ptx_emit_fma(dest: text, a: text, b: text, c: text, rnd: text) -> text
fn ptx_emit_fma_neg(dest: text, a: text, b: text, c: text) -> text
fn ptx_emit_setp(pred: text, cmp: text, ty: text, a: text, b: text) -> text
fn ptx_emit_selp(dest: text, ty: text, a: text, b: text, p: text) -> text
fn ptx_emit_shfl(dest: text, mode: text, src: text, lane: text) -> text
fn ptx_emit_warp_reduce(dest: text, op: text, ty: text, src: text,
                         mask: text) -> text   # emits 5-stage shfl tree
fn ptx_emit_ld_global_v4(dests: [text; 4], ty: text, ptr: text) -> text  # .v4 packed ld
fn ptx_emit_st_global_v4(srcs: [text; 4], ty: text, ptr: text) -> text
fn ptx_emit_gather(dest: text, ty: text, base: text, offset: text,
                    pred: text) -> text
fn ptx_emit_scatter(base: text, offset: text, src: text, ty: text,
                     pred: text) -> text
fn ptx_emit_shift(dest: text, op: text, ty: text, a: text, b: text) -> text
fn ptx_fresh_freg() -> text    # allocate fresh %fd_N
fn ptx_fresh_pred() -> text    # allocate fresh %p_N
```

### 5.7 `spirv_builder.spl` — Extensions (existing file, 601 lines)

Add:
```
fn spirv_emit_composite_construct(result_id: i32, type_id: i32,
                                   components: [i32]) -> [i32]   # word stream
fn spirv_emit_splat(result_id: i32, type_id: i32, scalar_id: i32,
                     n: i32) -> [i32]
fn spirv_emit_vector_shuffle(result_id: i32, type_id: i32,
                              v1: i32, v2: i32, indices: [i32]) -> [i32]
fn spirv_emit_glsl_ext(result_id: i32, type_id: i32,
                        ext_set_id: i32, inst: i32,
                        operands: [i32]) -> [i32]   # GLSL.std.450 ops
fn spirv_emit_subgroup_reduce(result_id: i32, type_id: i32,
                               scope_id: i32, op: i32,
                               value_id: i32) -> [i32]  # OpGroupNonUniform*
fn spirv_emit_subgroup_shuffle(result_id: i32, type_id: i32,
                                scope_id: i32, value_id: i32,
                                id_id: i32) -> [i32]
fn spirv_emit_subgroup_broadcast(result_id: i32, type_id: i32,
                                  scope_id: i32, value_id: i32,
                                  lane_id: i32) -> [i32]
fn spirv_emit_select(result_id: i32, type_id: i32,
                      cond: i32, t: i32, f: i32) -> [i32]
fn spirv_emit_cmp(result_id: i32, opcode: i32, a: i32, b: i32) -> [i32]
fn spirv_emit_binop(result_id: i32, type_id: i32, opcode: i32,
                     a: i32, b: i32) -> [i32]
fn spirv_emit_unop(result_id: i32, type_id: i32, opcode: i32, a: i32) -> [i32]
fn spirv_emit_shift(result_id: i32, type_id: i32, opcode: i32,
                     base: i32, shift: i32) -> [i32]
fn spirv_emit_gather_loop(result_ids: [i32], type_id: i32,
                           base_ptr_id: i32, index_ids: [i32]) -> [i32]
fn spirv_emit_scatter_loop(base_ptr_id: i32, index_ids: [i32],
                            value_ids: [i32]) -> [i32]
fn spirv_declare_capability(cap: i32)    # idempotent, deduplicates
fn spirv_declare_subgroup_capabilities()  # GroupNonUniform + arithmetic
```

---

## 6. Strict-Emit Verification

### 6.1 Pattern

The existing pattern (arm_neon.spl + x86_64_simd.spl) has no inline unit tests; verification is through the build bootstrap. The strict-emit verification pattern to establish for new backends is:

Each encoder helper is tested with known operands against an expected byte sequence (or text sequence for PTX/SPIR-V). A test case provides:
1. Fixed input operand IDs (register numbers, immediates).
2. Expected output: exact `[i64]` instruction words (or text string for PTX; `[i32]` word stream for SPIR-V).
3. Assertion: `assert(emit_fn(args) == expected)`.

Example for NEON (mirrors arm_neon.spl:138 structure):
```
# test: neon_encode_f32x4_3reg for FADD q0, q0, q1
let words = neon_encode_f32x4_3reg(0x4E20D400, 0, 0, 1)
assert(words[0] == 0x4E21D400i64)   # Vd=0, Vn=0, Vm=1 inserted
```

Example for AVX-512:
```
# test: evex_encode_3op_zmm for VADDPS zmm0{k1}, zmm1, zmm2
let words = evex_encode_3op_zmm(0, 1, 2, 1, false, 0b00001, 0, 0b01, 0x58)
# verify EVEX prefix bytes: P0=0x62, P1, P2, P3 then opcode 0x58
assert(words[0] == expected_evex_word)
```

Example for PTX:
```
let s = ptx_emit_binop("%f0", "add.f32", "f32", "%f1", "%f2")
assert(s == "add.f32 %f0, %f1, %f2;")
```

Example for SPIR-V:
```
let words = spirv_emit_binop(5, 10, SpvOpFAdd, 3, 4)
# words should be: [header_word, type_id, result_id, a_id, b_id]
assert(words[0] == ((5 << 16) | SpvOpFAdd))
assert(words[1] == 10)  # type
assert(words[2] == 5)   # result
```

### 6.2 Test Location

Tests live adjacent to the emitter file using the project's `.spec.spl` pattern:
- `src/compiler/70.backend/backend/native/arm_neon.spec.spl`
- `src/compiler/70.backend/backend/native/x86_64_simd.spec.spl`
- `src/compiler/70.backend/backend/native/x86_64_avx512.spec.spl` (new)
- `src/compiler/70.backend/backend/native/arm_sve2.spec.spl` (new)
- `src/compiler/70.backend/backend/native/riscv_rvv.spec.spl` (new)
- `src/compiler/70.backend/backend/cuda/ptx_builder.spec.spl` (extend)
- `src/compiler/70.backend/backend/vulkan/spirv_builder.spec.spl` (extend)

Each spec file tests all encoder helpers for the corresponding emitter. For backends with byte-level output (NEON, AVX-512, SVE2, RVV), assertions compare exact hex instruction words. For PTX and SPIR-V, assertions compare string content and word-stream structure.

---

## 7. Cross-Target Test Fixtures

### 7.1 Kernel Definitions

Five kernels covering the core operation categories:

| Kernel | Description | Key ops exercised |
|--------|-------------|-------------------|
| `saxpy` | `y[i] += alpha * x[i]` | splat, load, fma, store |
| `dot` | `acc += x[i] * y[i]`, then reduce | load, mul, add, reduce_sum |
| `hcompare` | `mask[i] = a[i] > b[i]`, then masked store | cmp_lt (flipped), mask_select, store |
| `gather_add` | `z[i] = x[indices[i]] + y[i]` | gather, load, add, store |
| `masked_store` | `if mask[i]: out[i] = in[i]` | load, cmp, mask_select, store |

### 7.2 Target Count

The strict-emit golden matrix covers 7 CPU/GPU targets. SPIR-V is included but golden format is SPIR-V disassembly (spirv-dis output) rather than raw bytes, due to word-stream format requiring a dissassembler for human-readable verification. This is the recommended resolution for the §2 asymmetry (8 op-tables vs. 7 goldens): SSE2 and SSE4 are treated as one target (`sse`) in goldens; SPIR-V goldens use text format not byte format.

Target list for goldens: `neon`, `sse`, `avx2`, `avx512`, `sve2`, `rvv`, `ptx`.

Total fixtures: 5 kernels × 7 targets = **35 golden files**.

### 7.3 Golden File Layout

```
test/backend/simd_strict_emit/
  neon/
    saxpy.golden          # byte sequence as hex words, one per line
    dot.golden
    hcompare.golden
    gather_add.golden
    masked_store.golden
  sse/
    saxpy.golden
    ...
  avx2/
    ...
  avx512/
    ...
  sve2/
    ...
  rvv/
    ...
  ptx/
    saxpy.golden          # PTX text (human-readable .ptx snippet)
    ...
```

### 7.4 Golden Format

- **CPU backends (neon, sse, avx2, avx512, sve2, rvv):** One hex 32-bit instruction word per line, prefixed with address offset: `0000: 4E21D400` (NEON FADD). Comment lines `#` allowed.
- **PTX backend:** Plain PTX text snippet (`.func` body only, no headers). One instruction per line as emitted by `ptx_builder.spl`.
- **SPIR-V backend (reference, not in the 35):** SPIR-V disassembly via `spirv-dis` of the relevant function.

### 7.5 Verification Mechanism

The golden test runner (to be wired into `bin/simple test`):
1. Emit the kernel for the target using the strict-emit emitter.
2. Diff output against the `.golden` file byte-for-byte (or line-by-line for PTX).
3. On mismatch: print hex diff with symbolic mnemonic decode.
4. Golden files are regenerated with `bin/simple test --update-goldens`.

---

## 8. Future Opcodes (Not First Wave)

These ops should be reserved in the trait surface as stubs returning a compile-time error or falling back to scalar, but are not required in the first emit pass.

| Op | Description | Primary target(s) | Spec reference |
|----|-------------|------------------|----------------|
| `aes_enc` | AES encryption round | x86 (AESNI), AArch64 (crypto) | Intel SDM AESENC; ARMv9 §C7.2.3 |
| `aes_dec` | AES decryption round | x86 (AESNI), AArch64 (crypto) | Intel SDM AESDEC |
| `dot4i8` | 4-way i8 dot product accumulate | AVX-512VNNI, AArch64 SDOT | Intel SDM VPDPBSSD; §C7.2.47 |
| `dot4u8` | 4-way u8 dot product accumulate | AVX-512VNNI, AArch64 UDOT | Intel SDM VPDPBUSD |
| `bf16_fma` | BF16 GEMM accumulate | AVX-512BF16, AArch64 BF16, PTX mma | Intel SDM VDPBF16PS; ARMv9 §C7.2.27; PTX §9.7.14 |
| `mma_f16` | 16×16 FP16 tensor core GEMM | PTX `mma.sync.aligned.m16n8k16.row.col.f32.f16.f16.f32` | PTX ISA 8.x §9.7.14 |
| `mma_tf32` | TF32 tensor core GEMM | PTX `mma.sync...tf32` | PTX ISA §9.7.14.8 |
| `mma_i8` | INT8 tensor core GEMM | PTX `mma.sync...s8.s8` | PTX ISA §9.7.14.6 |
| `compress` | Pack active lanes to low positions | AVX-512 (`VCOMPRESSPS`), SVE2 (`svcompact`) | Intel SDM VCOMPRESSPS; ARMv9 §C11.4.38 |
| `expand` | Scatter into mask-selected positions | AVX-512 (`VEXPANDPS`), SVE2 (`svexpand`) | Intel SDM VEXPANDPS |
| `popcount` | Count set bits per lane | AVX-512VPOPCNTDQ, AArch64 CNT | Intel SDM VPOPCNTD; §C7.2.36 |
| `cvt_f16_f32` | F32 ↔ F16 conversion | AVX-512FP16, AArch64 FCVT, NEON-FP16 | Intel SDM VCVTPS2PH; §C7.2.44 |
| `svcompact_f32` | SVE2 compress with predicate | SVE2 only | ARMv9 §C11.4.38 |
| `barrier_cluster` | Cross-warp cluster barrier | PTX SM90+ | PTX ISA §9.7.12.2 |
| `cooperative_matrix` | SPIR-V cooperative matrix ops | SPIR-V + Vulkan | SPIR-V `SPV_KHR_cooperative_matrix` |
| `subgroup_rotate` | Subgroup rotate by delta | SPIR-V + Vulkan 1.3.229+ | SPIR-V `GroupNonUniformRotateKHR` |
| `i8x16_mul_add` | i8 multiply-accumulate | AVX-512VNNI, NEON SMLAL | Intel SDM VPDPBSSD; §C7.2.184 |

---

*End of document.*
