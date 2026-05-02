<!-- claude-design -->
# Design: SIMD Test Catalog (Round 2 — Intensive)

**TL;DR:** Exhaustive test specifications for the SIMD backend rollout (B3). Covers
six tiers: T1 per-encoder-helper unit tests (~423 cases across ~136 helpers), T1 MIR-pass
and diagnostic unit tests (~120 cases), T2 pass-pipeline integration (192 cases, 8
kernels × 8 targets × 3 modes), T3 cross-target equivalence (10 kernels × 7 CPU
targets), T4 byte-level golden tests (40, 5 kernels × 8 targets), T5 fuzz tests (25
named errata seeds + 100K random iterations), and T6 perf gates (5 CPU targets +
CUDA). Phase gating and rollout milestones live in the companion doc
`simd_rollout_plan_v2.md` (C4a). All tests run in compiled mode; interpreter-mode
false-greens are a known project hazard (see project memory
`feedback_compile_mode_false_greens.md`).

---

<!-- sections appended below -->

## Table of Contents

1. [Test Taxonomy and Tiers](#1-test-taxonomy-and-tiers)
2. [T1 — Encoder Unit-Test Catalog](#2-t1--encoder-unit-test-catalog)
3. [T1 — MIR Opt-Pass Unit Tests](#3-t1--mir-opt-pass-unit-tests)
4. [T1 — Type-Check + Diagnostics Unit Tests](#4-t1--type-check--diagnostics-unit-tests)
5. [T2 — Integration-Test Matrix](#5-t2--integration-test-matrix)
6. [T3 — Cross-Target Equivalence Matrix](#6-t3--cross-target-equivalence-matrix)
7. [T4 — Strict-Emit Golden Tests](#7-t4--strict-emit-golden-tests)
8. [T5 — Fuzz Tests](#8-t5--fuzz-tests)
9. [T6 — Perf Gates](#9-t6--perf-gates)
10. [GPU/CUDA and Vulkan End-to-End Tests](#10-gpucuda-and-vulkan-end-to-end-tests)
11. [Test-Runner Integration](#11-test-runner-integration)
12. [Test-Tier Dependency Graph and Gating Policy](#12-test-tier-dependency-graph-and-gating-policy)
13. [Pre-Flight Infrastructure Tasks](#13-pre-flight-infrastructure-tasks)
14. [Open Test-Side Questions](#14-open-test-side-questions)

---

## 1. Test Taxonomy and Tiers

### 1.1 Tier Overview

| Tier | Name | Root path | Naming convention | Runner | Gating policy |
|------|------|-----------|-------------------|--------|---------------|
| T1 | Unit | `test/unit/compiler/` | `<module>_spec.spl` | `bin/simple test test/unit/` | Blocks T2; must be green before integration |
| T2 | Integration | `test/feature/simd/` | `<kernel>/<target>_<mode>_spec.spl` | `bin/simple test test/feature/simd/` | Blocks T3 on host |
| T3 | Cross-target equivalence | `test/cross_target/simd/` | `<kernel>_equiv_spec.spl` | QEMU wrapper script per target | Blocks merge after M3/M4 |
| T4 | Strict-emit goldens | `test/backend/simd_strict_emit/` | `<target>/<kernel>.golden` | `bin/simple test test/backend/` | SPOT-CHECK dev; MANDATORY at each phase exit |
| T5 | Fuzz | `test/fuzz/simd/` | `<dimension>_fuzz_spec.spl` | `bin/simple test test/fuzz/` (nightly CI) | Nightly, not per-PR |
| T6 | Perf gates | `test/perf/simd/` | `<target>_<kernel>_gate_spec.spl` | `bin/simple test test/perf/` (weekly + on-demand) | Weekly + blocks release |

### 1.2 Compiled-Mode Requirement

Every gating test MUST run with the compiled binary, not the interpreter. Invocation
pattern: `bin/simple build && bin/simple test --mode=compiled <path>`. The interpreter
produces false-greens for unresolved `std.spec` calls and for `it`-block variable
mutations (project memory: `feedback_compile_mode_false_greens.md`,
`feedback_interpreter_test_limits.md`).

### 1.3 Spec-File Template

All test files use the spipe template from `.claude/templates/spipe_template.spl`.
BDD-style: `describe` + `it` blocks. No `skip()` without explicit approval. No
`TODO→NOTE` conversions (project rule: implement or delete).

### 1.4 Tier Counts (Summary)

| Tier | Cases | Notes |
|------|-------|-------|
| T1 encoder | ~423 | ~136 helpers × 3 (happy/boundary/error) + ~15 extra k0/errata guard tests |
| T1 MIR pass | ~65 | 5 pass files, 8–20 tests each |
| T1 diagnostic | ~66 | 33 codes × 2 (negative + positive) |
| T2 integration | 192 | 8 kernels × 8 targets × 3 modes |
| T3 equivalence | 70 | 10 kernels × 7 CPU targets |
| T4 goldens | 40 | 5 kernels × 8 targets |
| T5 fuzz seeds | 25 targeted + 100K random | 12 errata + 13 V-series UNVERIFIED |
| T6 perf gates | 15 | 5 targets × 3 kernels (SAXPY, fma, reduce_sum) |
| **Total** | **~1000** | |

---

## 2. T1 — Encoder Unit-Test Catalog

**Path scheme:** `test/unit/compiler/backend/native/<target>/<helper_name>_spec.spl`

**Per-helper rule:** minimum 3 tests — H (happy-path canonical encode), B (boundary
register indices, edge immediates), E (error/guard — negative where an assertion or
diagnostic fires). Column format: `H: <brief>; B: <brief>; E: <brief>`.

**Naming pattern example (arm_neon):**
```
it("H: neon_encode_fmla_f32x4 q0,q1,q2 emits FMLA V0.4S,V1.4S,V2.4S bytes")
it("B: neon_encode_fmla_f32x4 q31,q31,q31 high-register indices")
it("E: neon_encode_fmla_f32x4 invalid lane > 31 asserts ICE")
```

### 2.1 `arm_neon.spl` — ~30 helpers → ~90 tests

| Helper | H | B | E |
|--------|---|---|---|
| `neon_encode_f32x4_3reg` (existing ref) | canonical q0,q1,q2 → correct opword | q31,q30,q29 max-index | opc out-of-range assert |
| `neon_encode_faddp_4s` | FADDP V0.4S bytes match C1 §9 | q16 high-bank | lane-count mismatch param |
| `neon_encode_faddp_scalar` | FADDP Sd,Vn.2S scalar reduce | Vn=v31 | dest not scalar assert |
| `neon_encode_vgetq_lane_f32` | MOV W0,V1.S[0] byte-correct | lane=3 boundary | lane=4 OOB assert |
| `neon_encode_vsetq_lane_f32` | INS V0.S[2],W5 byte-correct | lane=3, Wm=w30 | lane=5 OOB assert |
| `neon_encode_bsl_q` | BSL V0.16B,V1.16B,V2.16B | all high regs | non-16B width param |
| `neon_encode_fcmgt_f32x4` | FCMGT V0.4S all-lanes-gt | q15,q16 cross-bank | inverted operands (vclt swap, C1 §6-K) |
| `neon_encode_fcmge_f32x4` | FCMGE V0.4S | q31 | inverted operand order |
| `neon_encode_fmaxnm_f32x4` | FMAXNM V0.4S IEEE minNum | q0,q0 self | NaN-propagation NM vs FMAX |
| `neon_encode_fminnm_f32x4` | FMINNM V0.4S | q0,q0 self | NaN-propagation NM vs FMIN |
| `neon_encode_fmax_f32x4` | FMAX V0.4S NaN-propagating | q31 high | NaN both args → NaN out |
| `neon_encode_fmin_f32x4` | FMIN V0.4S | q31 | NaN propagation vs FMINNM |
| `neon_encode_vdup_f32x4` | DUP V0.4S,W3 splat GPR | W30 boundary | non-GPR src assert |
| `neon_encode_vdup_lane_f32x4` | DUP V0.4S,V1.S[1] lane dup | lane=3 max | lane=4 OOB |
| `neon_encode_vld1q_f32` | LD1 {V0.4S},[X0] unit-load | base=x28 | misaligned hint flag |
| `neon_encode_vst1q_f32` | ST1 {V0.4S},[X0] unit-store | base=x28 | src=invalid reg |
| `neon_encode_vld1q_f32_post` | LD1 post-index GPR offset 16 | offset=0 | negative offset assert |
| `neon_encode_vst1q_f32_post` | ST1 post-index GPR offset 16 | stride=4 | stride=0 guard |
| `neon_encode_vzip1q_f32` | ZIP1 V0.4S even-lane interleave | q15,q16 | mismatched element size |
| `neon_encode_vuzp1q_f32` | UZP1 V0.4S deinterleave | q31 | width mismatch |
| `neon_encode_vtrn1q_f32` | TRN1 V0.4S transpose-even | q31 | non-4S size |
| `neon_encode_qtbl1q_u8` | TBL V0.16B,{V1.16B},V2.16B byte-shuffle | high regs | table_len != 16 |
| `neon_encode_vaddvq_f32` | FADDV S0,V1.4S horiz reduce | Vn=v31 | dest not scalar |
| `neon_encode_vmaxvq_f32` | FMAXV S0,V1.4S horiz max | Vn=v31 | dest not scalar |
| `neon_encode_fmla_f32x4` | FMLA V0.4S accumulate | q31,q30,q29 | non-FP type assert |
| `neon_encode_masked_add_f32x4` (synth) | FCMGT+BSL recipe produces expected 3-inst sequence | all-zero mask | mask lane-count mismatch |
| `neon_encode_gather_f32x4` (synth §6.2) | scalar-extract loop emits N load instrs | N=4 lanes | N=0 degenerate |
| `neon_encode_reduce_sum_f32x4` (synth §6.3) | FADDP pair-tree produces scalar | tmp=q31 | tmp==src alias guard |
| `neon_encode_reduce_max_f32x4` (synth) | FMAXP tree produces scalar | src=q0 | src aliased dest |
| `neon_encode_scatter_f32x4` (synth §6.2) | scalar-store loop emits N store instrs | N=4 | idx_v==base alias |

### 2.2 `x86_64_sse.spl` + `x86_64_avx2.spl` — ~25 helpers → ~75 tests

| Helper | H | B | E |
|--------|---|---|---|
| `sse_encode_addps_xmm` | ADDPS xmm0,xmm1 REX/no-REX bytes | xmm15 dest | src==dest allowed (no error) |
| `sse_encode_mulps_xmm` | MULPS xmm0,xmm1 bytes | xmm15 | dst > 15 assert |
| `sse_encode_sqrtps_xmm` | SQRTPS xmm0,xmm1 bytes | xmm15 | invalid encoding param |
| `sse_encode_movaps_xmm` | MOVAPS xmm0,xmm1 aligned | xmm15 | non-aligned hint flag |
| `sse_encode_movups_xmm` | MOVUPS xmm0,xmm1 | xmm8 REX prefix | reg > 15 assert |
| `sse_encode_cmpps_xmm` | CMPPS imm8=0x11 (LT_OQ, C1 §9.1) | imm8=0 | imm8 > 31 assert |
| `sse_encode_blendvps_xmm` | BLENDVPS dest,src,XMM0 (implicit) | src=xmm15 | explicit mask reg != xmm0 assert |
| `avx2_encode_vaddps_ymm` | VADDPS ymm0,ymm1,ymm2 VEX bytes | ymm15 | ymm > 15 assert |
| `avx2_encode_vmulps_ymm` | VMULPS ymm VEX bytes | ymm15 | VEX.L!=1 assert |
| `avx2_encode_vsubps_ymm` | VSUBPS ymm | ymm15 | param type mismatch |
| `avx2_encode_vdivps_ymm` | VDIVPS ymm | ymm15 | param type mismatch |
| `avx2_encode_vfmadd213ps_ymm` | VFMADD213PS form-213 bytes | ymm15 | form mismatch (G-04 per C3b) |
| `avx2_encode_vfmadd132ps_ymm` | VFMADD132PS form-132 | ymm15 | wrong acc position |
| `avx2_encode_vfmadd231ps_ymm` | VFMADD231PS form-231 | ymm15 | wrong acc position |
| `avx2_encode_vblendvps_ymm` | VBLENDVPS 4-op VEX | ymm15 all | 3-op form misuse |
| `avx2_encode_vcmpps_ymm` | VCMPPS ymm imm8=0x11 | imm8=0 | imm8 > 31 |
| `avx2_encode_vperm2f128` | VPERM2F128 imm8=0x01 lane-swap | imm8=0x31 | imm8 reserved bits |
| `avx2_encode_vpermd` | VPERMD ymm by index vector | all-same idx | idx > 7 (out-of-lane) |
| `avx2_encode_vpshufb` | VPSHUFB ymm byte-shuffle mask | all-zero mask | mask > 16B lane |
| `avx2_encode_vgatherdps_ymm` | VGATHERDPS mask cleared per lane sequence | single lane | base==idx alias (C1 §6-A) |
| `avx2_encode_vbroadcastss_ymm` | VBROADCASTSS ymm,xmm splat | xmm15 src | dst not ymm |
| `avx2_encode_vmovaps_ymm` | VMOVAPS ymm,ymm aligned | ymm15 | non-32B alignment hint |
| `avx2_encode_vmovups_ymm_load` | VMOVUPS ymm,[mem] unaligned load | disp=0x7F | disp overflow |
| `avx2_encode_vmovups_ymm_store` | VMOVUPS [mem],ymm store | disp=0x7F | disp overflow |
| `avx2_scatter_fallback` | scalar loop emits 8 store instrs for ymm | scale=4 | scale not in {1,2,4,8} |

### 2.3 `x86_64_avx512.spl` — ~25 helpers → ~75 tests (+3 dedicated k0-regalloc tests)

Note: every helper using a kreg operand gets an extra k0-guard test (error case = k0
passed in; triggers G-01 per C3b §13). In addition, three dedicated regalloc-level tests
live in `test/unit/compiler/backend/native/x86_64/k0_reservation_spec.spl`:

- `regalloc_never_assigns_k0` — runs register allocator over a masked kernel, asserts
  k0 never appears in the output allocation map.
- `avx512_allocator_init_reserves_k0` — checks allocator init sequence marks k0 as
  permanently reserved (unavailable for virtual-reg assignment).
- `k0_evex_emit_ice_message_format` — passes k0 directly to `evex_encode_3op_zmm`,
  verifies the ICE message contains "k0 is reserved; use k1..k7" (not a silent wrong
  encoding).

| Helper | H | B | E (includes k0-guard where kmasked) |
|--------|---|---|---|
| `evex_encode_3op_zmm` | VADDPS zmm1{k1},zmm2,zmm3 bytes (C1 §1.7 example) | zmm31,k7 | k0 passed → G-01 assert |
| `evex_encode_2op_zmm` | VSQRTPS zmm0,zmm1 EVEX unary | zmm31 | k0 guard |
| `evex_encode_broadcast_zmm` | VBROADCASTSS zmm0,xmm1 b=1 set | xmm15 | src not xmm |
| `evex_encode_gather_zmm` | VGATHERDPS zmm0{k1},[base+zmm2*4] | scale=8 | k0 → G-01; base==idx |
| `evex_encode_scatter_zmm` | VSCATTERDPS [base+zmm2*4]{k1},zmm0 | scale=8 | k0 → G-01+G-07 conflict guard |
| `evex_encode_fmadd_zmm` | VFMADD213PS zmm1{k1}{z} bytes (C1 §1.7) | form=132 | wrong acc placement → G-04 |
| `evex_encode_cmp_zmm_to_k` | VCMPPS zmm,zmm,imm8=0x11 → k1 | k7 dest | k0 dest guard |
| `evex_encode_kmov` | KMOVW k1,k2 | k7,k0 src | dest k0 → G-01 |
| `evex_encode_kop` | KANDN k1,k2,k3 | KNOT k7 | k0 any operand |
| `evex_encode_perm_zmm` | VPERMT2PS zmm0{k1}{z},zmm1,zmm2 | zmm31 | k0 guard |
| `evex_encode_3op_zmm_sae` | VFMADD213PS {rn-sae} L'L=00,b=1 in P2 | {ru-sae} mode | invalid SaeMode enum |
| `evex_encode_vaddps` | VADDPS zmm0,zmm1,zmm2 convenience wrapper | k7,z=true | k0 guard |
| `evex_encode_vmulps` | VMULPS zmm | k7 | k0 guard |
| `evex_encode_vsubps` | VSUBPS zmm | k7 | k0 guard |
| `evex_encode_vdivps` | VDIVPS zmm | k7 | k0 guard |
| `evex_encode_vmovaps_load` | VMOVAPS zmm{k}{z},[mem] 64B aligned | disp=0 | k0; misalign assert in debug |
| `evex_encode_vmovaps_store` | VMOVAPS [mem]{k},zmm | disp=max | k0 guard |
| `evex_encode_vmovups_load` | VMOVUPS zmm,[mem] unaligned | large disp | k0 guard |
| `evex_encode_vmovups_store` | VMOVUPS [mem],zmm | large disp | k0 guard |
| `evex_encode_vcvt_zmm` | VCVTPS2PD zmm0,ymm1 | VCVTPD2PS | unsupported conv pair |
| `evex_encode_vpandd` | VPANDD zmm integer AND | k7 | k0 guard |
| `evex_encode_vpord` | VPORD zmm | k7 | k0 guard |
| `evex_encode_vpxord` | VPXORD zmm | k7 | k0 guard |
| `evex_encode_vmaxps` | VMAXPS zmm NaN-check (C1 §9.2) | k7 | k0 guard |
| `evex_encode_vminps` | VMINPS zmm NaN-check | k7 | k0 guard |

### 2.4 `arm_sve2.spl` — ~25 helpers → ~75 tests

| Helper | H | B | E |
|--------|---|---|---|
| `sve_encode_3reg_pred` | generic FADD Zd.S,Pg/M,Zn.S,Zm.S bits | z31,p7 max | pg > 15 assert |
| `sve_encode_2reg_pred` | FABS Zd.S,Pg/M,Zn.S bits | z31,p7 | pg > 15 |
| `sve_encode_ptrue` | PTRUE P0.S,ALL (pattern=0x1F) bits | p7, esz=3 | invalid pattern > 0x1F |
| `sve_encode_whilelt` | WHILELT P0.S,X0,X1 bits | p7,x30 | p0 dest (valid, no error) |
| `sve_encode_whilelo` | WHILELO P0.S,X0,X1 unsigned | p7 | esz mismatch |
| `sve_encode_ld1w_contiguous` | LD1W {Z0.S},P0/Z,[X0,X1,LSL#2] | z31,p7 | unaligned offset |
| `sve_encode_st1w_contiguous` | ST1W {Z0.S},P0,[X0,X1,LSL#2] | z31,p7 | pg > 15 |
| `sve_encode_gather_ld1w` | LD1W gather [Xbase,Z0.S,UXTW#2] | z31 offset | zoffset type wrong |
| `sve_encode_scatter_st1w` | ST1W scatter [Xbase,Z0.S,UXTW#2] | z31 | SME streaming guard G-06 |
| `sve_encode_fadd_s_pred` | FADD Zd.S,Pg/M bits exact | z31,p7 | apple-M guard G-03 |
| `sve_encode_fmla_s_pred` | FMLA Zd.S,Pg/M accumulator | z31 acc | acc mismatch operand |
| `sve_encode_fmul_s_pred` | FMUL Zd.S,Pg/M bits | z31,p7 | apple-M guard G-03 |
| `sve_encode_fsub_s_pred` | FSUB Zd.S,Pg/M | z31 | apple-M guard |
| `sve_encode_fdiv_s_pred` | FDIV Zd.S,Pg/M | z31 | apple-M guard |
| `sve_encode_fcmgt_s_pred` | FCMGT Pd.S,Pg/Z→predicate | p7 dest | dest not P-reg |
| `sve_encode_fmaxnm_s_pred` | FMAXNM Zd.S NaN-choice (C1 §9.2) | z31 | NaN-propagating FMAX used instead |
| `sve_encode_fminnm_s_pred` | FMINNM Zd.S | z31 | NaN contract mismatch |
| `sve_encode_sel` | SEL Zd.S,Pg — predicated blend | z31,p7 | pg > 15 |
| `sve_encode_incd` | INCD Xd,ALL increment | x30 | non-GP register |
| `sve_encode_cntw` | CNTW Xd reads element count | x30 | non-GP dest |
| `sve_encode_index` | INDEX Zd.S,W0,W1 iota | z31,w30 | step=0 (valid, no error) |
| `sve_encode_compact` | COMPACT Zd.S,Pg pack active | z31,p7 | pg > 15 |
| `sve_encode_ptest` | PTEST {Pg},Pn.B bits | p7 both | pg > 15 |
| `sve_encode_pnext` | PNEXT Pd.S,Pg advance | p7 | esz invalid |
| `sve_encode_pred_3op` (core §4.2) | verify against sve_encode_3reg_pred | z31,p15 | opc reserved range |

### 2.5 `riscv_v.spl` — ~16 helpers → ~48 tests (+12 vsetvli/lmul-alignment tests)

| Helper | H | B | E |
|--------|---|---|---|
| `rvv_encode_vsetvli` | vsetvli rd,rs1,vtypei bits exact (C1 §3.2) | rd=x31 | vtypei reserved bits set |
| `rvv_encode_vsetivli` | vsetivli with uimm5=15 | uimm=0 | uimm > 31 assert |
| `rvv_encode_vtype` | assemble vtypei e32/m1/ta/ma | m8 LMUL | LMUL=reserved(0b100) assert (C1 §3.5) |
| `rvv_encode_3reg_vv` | OPFVV template bits | vd=v31 | funct6 reserved |
| `rvv_encode_3reg_vx` | OPIVX GPR-scalar bits | vs2=v31,rs1=x31 | GPR index > 31 |
| `rvv_encode_3reg_vf` | OPFVF FP-scalar bits | fs1=f31 | non-FP reg assert |
| `rvv_encode_3reg_vi` | OPIVI imm5=15 bits | imm5=-16 (signed min) | imm5 > 15 |
| `rvv_encode_vfadd_vv` | vfadd.vv vd,vs2,vs1 bits | v31 all | non-FP type |
| `rvv_encode_vfsub_vv` | vfsub.vv bits | v31 | — |
| `rvv_encode_vfmul_vv` | vfmul.vv bits | v31 | — |
| `rvv_encode_vfdiv_vv` | vfdiv.vv bits | v31 | — |
| `rvv_encode_vfmacc_vv` | vfmacc.vv funct6=0b011000 (V-16 UNVERIFIED) | v31 | wrong funct6 assert |
| `rvv_encode_vfnmacc_vv` | vfnmacc.vv bits | v31 | funct6 check |
| `rvv_encode_vfmv_vf` | vfmv.v.f splat FP scalar | fs1=f31 | non-FP reg |
| `rvv_encode_vlw_v` | vle32.v unit-stride load | vd=v31,rs1=x31 | vm=0 without prior vmv1r (G-02) |
| `rvv_encode_vmv1r_before_masked_op` (G-02) | vmv1r.v v0,v<n> emitted before masked vle32.v | mask already in v0 → no extra emit | G-02 absent → ICE |

**Extra vsetvli/LMUL-alignment tests (12 tests):**
- `vsetvli_lmul1_saxpy`: LMUL=1 SAXPY correct vtype encoding
- `vsetvli_lmul2_saxpy`: LMUL=2 widened SAXPY (M7 `lmul_widen`)
- `vsetvli_lmul4_saxpy`: LMUL=4 widened
- `vsetvli_lmul8_boundary`: LMUL=8 boundary (all 8 regs consumed)
- `vsetvli_lmul_reserved_reject`: LMUL=reserved(4) → E_SIMD_BAD_LANES
- `vtype_vta_vma_bits`: vta=1,vma=1 agnostic tail/mask bits correct
- `vstart_zero_after_vsetvli`: G-05 guard asserts vstart=0 in debug
- `lmul_alignment_v0_v8`: LMUL=2 group starting at odd register → reject
- `lmul_alignment_v1_reject`: v1 as LMUL=2 dest → ICE
- `lmul_alignment_v8_accept`: v8 as LMUL=2 dest → OK
- `vfredosum_ordered`: vfredosum.vs ordered bit set (C1 §9.4)
- `vfredusum_unordered`: vfredusum.vs unordered tolerance note

### 2.6 `cuda/ptx_builder.spl` — ~10 helpers → ~30 tests

| Helper | H | B | E |
|--------|---|---|---|
| `ptx_emit_ld_global_f32` | `ld.global.f32 %f0,[%rd0]` text | %rd31 | non-global space assert |
| `ptx_emit_st_global_f32` | `st.global.f32 [%rd0],%f1` | large offset | addr space mismatch |
| `ptx_emit_fma_f32` | `fma.rn.f32 %f0,%f1,%f2,%f3` | all same reg | non-FP reg type |
| `ptx_emit_add_f32` | `add.f32 %f0,%f1,%f2` | %f127 | reg index > 127 assert |
| `ptx_emit_mul_f32` | `mul.f32` | %f127 | — |
| `ptx_emit_shfl_sync` | `shfl.sync.bfly.b32 %r0,%r1,16,0x1f,0xffffffff` (V-23 UNVERIFIED — self-mask C1 §6-G) | delta=0 | delta > 31 (E_WARP_DELTA_OOB) |
| `ptx_emit_bar_sync` | `bar.sync 0` | bar_id=15 | bar_id > 15 |
| `ptx_emit_setp_f32` | `setp.lt.f32 %p0,%f0,%f1` | pred=p63 | pred > 63 |
| `ptx_emit_selp_f32` | `selp.f32 %f0,%f1,%f2,%p0` | pred=p63 | pred > 63 |
| `ptx_emit_reduce_tree_f32` | 5-stage shfl.sync.bfly tree (B2 §3.13) — all 5 instrs present | warp_size=32 | self-mask 0xffffffff (G-08 self-exclusion) |

### 2.7 `vulkan/spirv_builder.spl` — ~5 helpers → ~15 tests

| Helper | H | B | E |
|--------|---|---|---|
| `spirv_emit_op_f_add` | `OpFAdd %float %id %a %b` word sequence | large id | non-float type id |
| `spirv_emit_op_f_mul` | `OpFMul` word sequence | large id | non-float type |
| `spirv_emit_op_load` | `OpLoad %float %id %ptr` | ptr id = max | non-pointer type |
| `spirv_emit_op_store` | `OpStore %ptr %val` | max ptr id | non-pointer type |
| `spirv_emit_op_composite_extract` | `OpCompositeExtract %float %id %vec 0` | index=3 | index >= lane-count |

---

## 3. T1 — MIR Opt-Pass Unit Tests

**Path scheme:** `test/unit/compiler/mir_opt/<pass_name>_spec.spl`
**Runner:** `bin/simple test test/unit/compiler/mir_opt/ --mode=compiled`

### 3.1 `simd_lowering.spl` (existing) — 14 tests

| Test name | What it checks | Rationale |
|-----------|---------------|-----------|
| `lowers_fixedvec_add_to_simd_add_f32x4` | `FixedVec<f32,4>::add` → `SimdAddF32x4` MIR opcode | C2 §8 MIR opcode table |
| `lowers_fixedvec_mul_to_simd_mul_f32x4` | `mul` → `SimdMulF32x4` | C2 §8 |
| `lowers_fixedvec_fma_to_simd_fma_f32x4` | `fma(a,b,c)` → `SimdFmaF32x4` | C2 §8 |
| `lowers_fixedvec_load_to_simd_load_f32x4` | `load_aligned` → `SimdLoadAlignedF32x4` | C2 §8 |
| `lowers_fixedvec_store_to_simd_store_f32x4` | `store_aligned` → `SimdStoreAlignedF32x4` | C2 §8 |
| `lowers_fixedvec_reduce_sum_to_simd_reduce` | `reduce_sum` → `SimdReduceSumF32x4` | C2 §8 |
| `lowers_fixedvec_mask_select_to_simd_blend` | `mask_select` → `SimdBlendF32x4` | C2 §5 |
| `lowers_scalablevec_fma_to_simd_fma_scalable` | `ScalableVec<f32>::fma` → scalable MIR op | C2 §4 |
| `lowers_broadcast_scalar_to_simd_splat` | `splat(x)` → `SimdSplatF32` | C2 §8 |
| `lowers_gather_to_simd_gather` | `gather` → `SimdGatherF32x4` | C2 §8 |
| `lowers_scatter_to_simd_scatter` | `scatter` → `SimdScatterF32x4` | C2 §8 |
| `lowers_fixedvec_shuffle_to_simd_shuffle` | `shuffle(ctrl)` runtime indices | C2 §1.1 |
| `lowers_fixedvec_permute_to_simd_permute` | `permute(ctrl)` compile-time const | C2 §1.1 `E_SIMD_CONST_REQUIRED` |
| `preserves_non_simd_ops_unchanged` | non-SIMD MIR nodes pass through unmodified | regression guard |

### 3.2 `lmul_widen.spl` (NEW, M7) — 10 tests

| Test name | What it checks | Rationale |
|-----------|---------------|-----------|
| `widens_lmul1_to_lmul2_for_saxpy` | LMUL=1 SAXPY MIR → LMUL=2 vsetvli emitted | C2 §4, C1 §3.5 |
| `widens_lmul1_to_lmul4_when_profitable` | LMUL=4 when loop body fits 4× throughput | C2 §4 |
| `does_not_widen_past_lmul8` | LMUL=8 cap enforced | C1 §3.5 LMUL limit |
| `alignment_guard_even_register_only` | LMUL=2 group must start at even vreg | C3b §8.4 |
| `alignment_guard_rejects_odd_vreg` | LMUL=2 starting at v1 → ICE (compile-time) | C3b §8.4 |
| `lmul_invariance_saxpy_output` | LMUL=1 and LMUL=2 produce identical float output for SAXPY | C1 §1.2 Correctness |
| `lmul_invariance_dot_output` | LMUL=1 and LMUL=2 identical for dot-product | C1 §1.2 |
| `no_widen_when_spill_pressure_high` | pass disables widening when vreg pressure > threshold | heuristic guard |
| `widen_pass_idempotent` | running pass twice produces same MIR | correctness invariant |
| `widen_handles_tail_loop_correctly` | tail iterations after vectorized body use LMUL=1 | C1 §3.8 vstart |

### 3.3 `predicate_promote.spl` (NEW, M2) — 8 tests

| Test name | What it checks | Rationale |
|-----------|---------------|-----------|
| `z_predication_fills_zero_inactive_lanes` | `_z` suffix → zero-fill on inactive lanes | C2 §5 |
| `x_predication_leaves_inactive_undef` | `_x` suffix → undef (performance path) | C2 §5 |
| `promotes_z_to_x_when_lanes_not_live` | liveness shows inactive lanes never read → promote `_z` to `_x` | C2 §5, W_SIMD_PRED_PROMOTE_HINT |
| `does_not_promote_when_inactive_lanes_live` | live inactive lane → no promotion | C2 §5 |
| `sve2_sel_emitted_for_z_predication` | `_z` → SEL+predicated-op pair (SVE2 C3a §2.4) | C3a §2.4 |
| `rvv_vm0_emitted_for_masked_op` | `_z` on RVV → vmv1r.v v0 + vm=0 (G-02) | C3b G-02 |
| `pass_is_off_by_default` | `_z` test passes with pass OFF; `_x` test passes with pass ON | C1 §1.2 Correctness |
| `promote_pass_idempotent` | double application unchanged | correctness |

### 3.4 `simd_split_unsupported.spl` (NEW, M1) — 10 tests

| Test name | What it checks | Rationale |
|-----------|---------------|-----------|
| `splits_f32x16_to_4xf32x4_on_sse2` | `FixedVec<f32,16>` on SSE2 target → 4× f32x4 ops | C2 §3 decision table |
| `splits_f32x8_to_2xf32x4_on_sse2` | `FixedVec<f32,8>` on SSE2 → 2× f32x4 | C2 §3 |
| `does_not_split_f32x4_on_sse2` | f32x4 native on SSE2 → no split | C2 §3 |
| `splits_i32x16_to_4xi32x4_on_sse4` | integer split | C2 §3 |
| `emits_w_simd_no_native_lowering_diagnostic` | split triggers `W_SIMD_NO_NATIVE_LOWERING` | C2 §9 |
| `emits_w_simd_scalar_fallback_for_f64x8_sse2` | f64x8 on SSE2 → scalar fallback + diagnostic | C2 §9 |
| `split_produces_same_output_as_native` | 4× f32x4 SAXPY = f32x16 SAXPY on reference | correctness oracle |
| `split_handles_non_pow2_count_gracefully` | remainder lanes handled | C1 §1.2 |
| `no_split_on_avx512_for_f32x16` | AVX-512 native → no split emitted | C2 §3 |
| `split_pass_idempotent` | double application unchanged | correctness |

### 3.5 `auto_vectorize_*.spl` (extending stubs, M6) — 16 tests

| Test name | Pattern | What it checks | Rationale |
|-----------|---------|---------------|-----------|
| `av_saxpy_elementwise_vectorized` | SAXPY `y[i]+=alpha*x[i]` | MIR contains `SimdFmaF32x*` | C1 §1.4 AV pattern 1 |
| `av_saxpy_loop_bounds_correct` | SAXPY loop | trip-count multiple of lanes | C1 §1.4 |
| `av_saxpy_tail_handled` | SAXPY non-multiple N | tail scalar loop emitted | C1 §1.4 |
| `av_dot_reduction_vectorized` | dot `acc+=x[i]*y[i]` | `SimdMulF32x*` + reduce MIR | C1 §1.4 AV pattern 2 |
| `av_dot_reduction_order_documented` | dot | tolerance comment in output MIR | C1 §9.4 |
| `av_typecast_copy_vectorized` | `dst[i]=f32(src[i])` | `SimdCvtI32F32x*` MIR | C1 §1.4 AV pattern 3 |
| `av_typecast_preserves_values` | typecast | output == scalar reference | correctness |
| `av_conditional_copy_vectorized` | `if cond[i]: dst[i]=src[i]` | `SimdBlend` MIR | C1 §1.4 AV pattern 4 |
| `av_conditional_copy_mask_correct` | conditional | mask values match scalar | correctness |
| `av_scalar_broadcast_multiply` | `y[i]=x[i]*k` | `SimdSplat` + `SimdMulF32x*` MIR | C1 §1.4 AV pattern 5 |
| `av_scalar_broadcast_splat_once` | broadcast mul | k splatted exactly once outside loop | efficiency |
| `av_no_vectorize_aliased_loop` | `y[i]=y[i-1]+x[i]` | loop NOT vectorized (dep) | negative / correctness |
| `av_no_vectorize_non_stride1` | stride != 1 loop | not vectorized or fallback | C2 §9 W_SIMD_HARDCODED_STRIDE |
| `av_mir_output_verifiable_via_desugar` | any AV pattern | `bin/simple desugar` shows SimdXxx MIR | C1 §1.4 trigger |
| `av_host_target_selects_preferred_width` | SAXPY on host | lane width = `simd_lanes_preferred<f32>()` | C2 §2 |
| `av_pass_idempotent` | any | double pass unchanged | correctness |

---

## 4. T1 — Type-Check + Diagnostics Unit Tests

**Path scheme:** `test/unit/compiler/semantics/simd_diagnostics_spec.spl`
(one file; each `it` block covers one code × one polarity)
**Rule:** every diagnostic code gets 1 negative test (triggers the code) + 1 positive
test (same construct, corrected — does NOT trigger). Per C2 §9.

### 4.1 Error Codes (E_SIMD_* and E_WARP_*)

| Code | Neg test name | Pos test name | C2 § |
|------|--------------|--------------|------|
| `E_SIMD_BAD_LANES` | `e_simd_bad_lanes_n3_triggers` | `e_simd_bad_lanes_n4_ok` | §9 |
| `E_SIMD_TYPE_MISMATCH` | `e_simd_type_mismatch_bool_triggers` | `e_simd_type_mismatch_f32_ok` | §9 |
| `E_SIMD_FLOAT_ONLY` | `e_simd_float_only_fma_on_i32_triggers` | `e_simd_float_only_fma_on_f32_ok` | §9 |
| `E_SIMD_INT_ONLY` | `e_simd_int_only_and_on_f32_triggers` | `e_simd_int_only_and_on_i32_ok` | §9 |
| `E_SIMD_LANE_MISMATCH` | `e_simd_lane_mismatch_mask4_vec8_triggers` | `e_simd_lane_mismatch_mask4_vec4_ok` | §9 |
| `E_SIMD_MASK_TYPE_MISMATCH` | `e_simd_mask_type_mismatch_f32_i32_triggers` | `e_simd_mask_type_mismatch_matching_ok` | §9 |
| `E_SIMD_ARRAY_LEN_MISMATCH` | `e_simd_array_len_from_array_2_into_4_triggers` | `e_simd_array_len_from_array_4_ok` | §9 |
| `E_SIMD_SLICE_TOO_SHORT` | `e_simd_slice_too_short_2_into_4_triggers` | `e_simd_slice_ok_4_into_4` | §9 |
| `E_SIMD_SHIFT_OOB` | `e_simd_shift_oob_count32_on_i32_triggers` | `e_simd_shift_count31_ok` | §9 |
| `E_SIMD_LANE_OOB` | `e_simd_lane_oob_lane8_on_4lane_triggers` | `e_simd_lane_ok_lane3_on_4lane` | §9 |
| `E_SIMD_TYPE_AMBIGUOUS` | `e_simd_type_ambiguous_splat0_no_ctx_triggers` | `e_simd_type_annotated_splat0_ok` | §9 |
| `E_SIMD_NO_LOWERING` | `e_simd_no_lowering_require_native_f64x16_sse2_triggers` | `e_simd_no_lowering_f32x4_sse2_ok` | §9 |
| `E_SIMD_PTX_NO_SCALABLE` | `e_simd_ptx_no_scalable_scalablevec_triggers` | `e_simd_ptx_fixedvec_ok` | §9 |
| `E_SIMD_FIXED_OVERFLOWS_SCALABLE` | `e_simd_fixed_overflows_n8_minlanes4_triggers` | `e_simd_fixed_n4_minlanes4_ok` | §9 |
| `E_SIMD_MASK_BITS_OOB` | `e_simd_mask_bits_oob_0xff_on_2lane_triggers` | `e_simd_mask_bits_0x3_on_2lane_ok` | §9 |
| `E_SIMD_NO_WIDEN_TYPE` | `e_simd_no_widen_i64x4_triggers` | `e_simd_widen_i32x4_ok` | §9 |
| `E_SIMD_NO_NARROW_TYPE` | `e_simd_no_narrow_i8x16_triggers` | `e_simd_narrow_i16x8_ok` | §9 |
| `E_SIMD_COMPILE_ONLY` | `e_simd_compile_only_ptx_preg_interp_triggers` | `e_simd_compile_only_in_compiled_ok` | §9 |
| `E_SIMD_CONST_REQUIRED` | `e_simd_const_required_permute_runtime_idx_triggers` | `e_simd_const_comptime_permute_ok` | §9 |
| `E_WARP_NOT_IN_KERNEL` | `e_warp_not_in_kernel_host_fn_triggers` | `e_warp_in_kernel_ok` | §9 |
| `E_WARP_NO_APPLE_M` | `e_warp_no_apple_m_target_apple_triggers` | `e_warp_no_apple_m_cuda_target_ok` | §9, G-03 |
| `E_WARP_DELTA_OOB` | `e_warp_delta_oob_32_triggers` | `e_warp_delta_31_ok` | §9 |
| `E_WARP_SELF_EXCLUDED` | `e_warp_self_excluded_mask_excludes_self_triggers` | `e_warp_self_included_ok` | §9 |
| `E_WARP_LANE_OOB` | `e_warp_lane_oob_32_triggers` | `e_warp_lane_31_ok` | §9 |
| `E_WARP_SIZE_RUNTIME_ONLY` | `e_warp_size_compiletime_const_triggers` | `e_warp_size_runtime_query_ok` | §9 |

### 4.2 Warning Codes (W_SIMD_* and W_WARP_*)

| Code | Neg test name | Pos test name | C2 § |
|------|--------------|--------------|------|
| `W_SIMD_SCALAR_FALLBACK` | `w_simd_scalar_fallback_f32x16_sse2_emits_warn` | `w_simd_no_fallback_f32x4_sse2_ok` | §9 |
| `W_SIMD_NO_NATIVE_LOWERING` | `w_simd_no_native_lowering_split_emits_warn` | `w_simd_native_lowering_avx512_ok` | §9 |
| `W_SIMD_HARDCODED_STRIDE` | `w_simd_hardcoded_stride_const_step_triggers` | `w_simd_lanes_stride_ok` | §9 |
| `W_SIMD_PRED_PROMOTE_HINT` | `w_simd_pred_promote_hint_x_promotion_emits_info` | `w_simd_pred_z_no_hint` | §9 |
| `W_SIMD_FIXED_EXCEEDS_MIN_LANES` | `w_simd_fixed_exceeds_n8_minlanes4_warns` | `w_simd_fixed_n4_minlanes4_ok` | §9 |
| `W_SIMD_MASK_BITS_OOB` | `w_simd_mask_bits_from_bits_beyond_lanes_warns` | `w_simd_mask_bits_valid_ok` | §9 |
| `W_WARP_SYNC_EMPTY_MASK` | `w_warp_sync_empty_mask_0_triggers` | `w_warp_sync_active_mask_ok` | §9 |
| `W_SIMD_FP16_AUTOPROMOTE` | `w_simd_fp16_autopromote_no_native_warns` | `w_simd_fp32_no_warn` | §9 |

---

## 5. T2 — Integration-Test Matrix

**Path scheme:** `test/feature/simd/<kernel>/<target>_<mode>_spec.spl`
**Runner:** `bin/simple test test/feature/simd/ --mode=compiled`
**Total:** 8 kernels × 8 targets × 3 modes = 192 cases

### 5.1 Kernels

| ID | Kernel | Description | Key MIR ops exercised |
|----|--------|-------------|----------------------|
| K1 | `saxpy` | `y[i] += alpha * x[i]` float32 N=1M | FMA, load, store |
| K2 | `dot` | `acc += x[i] * y[i]` → scalar | FMA, reduce_sum |
| K3 | `mat_vec` | 4×4 mat × vec4 | FMA, broadcast, shuffle |
| K4 | `hcompare` | horizontal compare: any lane > threshold | cmp, reduce_or |
| K5 | `gather_add` | `dst[i] = src[idx[i]] + bias` | gather, add |
| K6 | `masked_store` | store only active lanes | mask_select, store |
| K7 | `reduce_sum` | full-vector horizontal sum | reduce_sum |
| K8 | `permute_shuffle` | shuffle by compile-time ctrl | permute, shuffle |

### 5.2 Targets

| ID | Target triple | Backend file | QEMU required |
|----|--------------|--------------|---------------|
| TGT1 | `aarch64-unknown-linux-gnu` (NEON) | `arm_neon.spl` | No (if host is AArch64); Yes on x86 host |
| TGT2 | `x86_64-unknown-linux-gnu` SSE2/SSE4 | `x86_64_sse.spl` | No (if host is x86_64) |
| TGT3 | `x86_64-unknown-linux-gnu` AVX2 | `x86_64_avx2.spl` | No |
| TGT4 | `x86_64-unknown-linux-gnu` AVX-512 | `x86_64_avx512.spl` | `qemu-system-x86_64 -cpu Icelake-Server` if no HW |
| TGT5 | `aarch64-unknown-linux-gnu` SVE2 | `arm_sve2.spl` | `qemu-aarch64 -cpu max,sve2=on` |
| TGT6 | `riscv64-unknown-linux-gnu` RVV | `riscv_v.spl` | `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64` |
| TGT7 | PTX (CUDA SM_70+) | `cuda/ptx_builder.spl` | CUDA runtime OR skip if no GPU |
| TGT8 | SPIR-V (Vulkan 1.2) | `vulkan/spirv_builder.spl` | Vulkan validation layer + llvmpipe |

### 5.3 Modes

| Mode | Invocation | Purpose |
|------|-----------|---------|
| `interp` | `bin/simple test --mode=interp` | Smoke-check parse/type-check only; no execution assertion |
| `compile_debug` | `bin/simple build --debug && ./out` | Full compiled execution with assertions |
| `compile_release` | `bin/simple build --release && ./out` | Optimized; verify no perf regression vs debug |

### 5.4 Expected Output and Dependencies

For each `(Kn, TGTm, mode)` case:
- **interp**: file loads without type-error; no `it` execution (interpreter limit)
- **compile_debug**: output array matches scalar reference to within IEEE-754 round-trip
  tolerance (1 ULP for f32; exception: `reduce_sum` on RVV/SVE2 may differ by reduction
  order per C1 §9.4 — tolerance window = 4 ULP)
- **compile_release**: same output as debug; binary size and runtime within 110% of debug

**File path example:**
`test/feature/simd/saxpy/aarch64_neon_compile_debug_spec.spl`

**Dependencies per target:**
- TGT5 (SVE2): requires QEMU + `qemu-aarch64 -cpu max,sve2=on` available in PATH
- TGT6 (RVV): requires `qemu-system-riscv64` with vector extension
- TGT7 (PTX): requires `nvidia-smi` detects SM_70+ GPU OR test is tagged `@skip_no_gpu`
- TGT8 (SPIR-V): requires Vulkan loader + llvmpipe; tagged `@skip_no_vulkan` if absent

---

## 6. T3 — Cross-Target Equivalence Matrix

**Path scheme:** `test/cross_target/simd/<kernel>_equiv_spec.spl`
**Runner:** `scripts/test/simd_cross_target_runner.shs` (to be created, M3)
**Total:** 10 kernels × 7 CPU targets = 70 comparisons (GPU targets excluded — PTX/SPIR-V
non-comparable numerically due to warp semantics)

### 6.1 Kernels

The 8 from T2 plus:
- **K9** `reduce_min`: horizontal minimum across lanes
- **K10** `gather_bounded`: gather with index clamped to `[0, N-1]`

### 6.2 CPU Targets (7)

TGT1–TGT6 from §5.2 (NEON, SSE2, AVX2, AVX-512, SVE2, RVV) plus:
- **TGT0** `scalar` reference loop (always compiled on host) — the oracle

### 6.3 QEMU Runner Conventions

Mirrors `scripts/check-freebsd-bootstrap-qemu.shs` pattern. Per-target wrapper:

| Target | QEMU invocation | CPU flag |
|--------|----------------|---------|
| SVE2 | `qemu-aarch64 -cpu max,sve2=on` | `HWCAP2_SVE2` required |
| RVV | `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64` | `vlen=128` minimum |
| AVX-512 (no HW) | `qemu-system-x86_64 -cpu Icelake-Server` | `avx512f` feature flag |
| NEON (on x86 host) | `qemu-aarch64 -cpu max` | `HWCAP_ASIMD` |

Spike simulator fallback for RVV when QEMU cycle accuracy is insufficient:
`spike --isa=rv64gcv pk <binary>` (see §11 for invocation details).

### 6.4 Bit-Exactness Policy

| Kernel | Bit-exact? | Tolerance | Reason |
|--------|-----------|-----------|--------|
| K1 `saxpy` | Yes | 0 ULP | FMA result identical across ISAs for same inputs |
| K2 `dot` | No | 4 ULP | Reduction order varies: tree (AVX) vs pairwise (NEON) vs ordered (RVV `vfredosum`) per C1 §9.4 |
| K3 `mat_vec` | Yes | 0 ULP | Fixed sequence of FMAs, no reduction |
| K4 `hcompare` | Yes | N/A (boolean) | All ISAs use OQ (ordered-quiet) NaN semantics per C1 §9.1 |
| K5 `gather_add` | Yes | 0 ULP | Memory-index gather; no float reorder |
| K6 `masked_store` | Yes | 0 ULP | Predicated store; inactive lanes never written |
| K7 `reduce_sum` | No | 4 ULP | Tree vs sequential reduction per C1 §9.4 |
| K8 `permute_shuffle` | Yes | 0 ULP | Integer lane permutation; no FP |
| K9 `reduce_min` | No | N/A (exact for non-NaN) | NaN handling: minNum vs minimum per C1 §9.2; use NaN-free input to force bit-exact |
| K10 `gather_bounded` | Yes | 0 ULP | Bounded gather, no FP reduction |

**NaN inputs:** the cross-target harness always injects a NaN-free input set for
bit-exact kernels. A second pass uses inputs with one NaN in lane 0 to verify that
the non-NaN-propagating min/max behavior is documented (not asserted equal).

---

## 7. T4 — Strict-Emit Golden Tests

**Path scheme:** `test/backend/simd_strict_emit/<target>/<kernel>.golden`
**Diff runner:** `scripts/test/golden_diff.shs` — byte-by-byte for CPU targets; text
diff for PTX/SPIR-V. On mismatch: decode both sides via `llvm-objdump -d` (CPU) or
`spirv-dis` (SPIR-V) and print side-by-side mnemonics.

**Pinning rule:** every golden file header must cite:
```
# target: <triple>
# kernel: <name>
# primary-spec: <URL or doc reference>
# status: VERIFIED | UNVERIFIED | ERRATA-GUARDED
# c3-section: <C3a/C3b §>
```

### 7.1 Golden Grid (5 kernels × 8 targets = 40 goldens)

Round-1 B2 had 35 goldens (5 × 7 CPU). Round-2 adds 5 SPIR-V goldens as the 8th target.
C3b §10 provides 24 byte-level fixtures; the remaining 16 are new or extended here.

| Kernel | NEON | SSE2 | AVX2 | AVX-512 | SVE2 | RVV | PTX | SPIR-V |
|--------|------|------|------|---------|------|-----|-----|--------|
| `saxpy` | C3b §10 (existing) | C3b §10 | C3b §10 | C3b §10 EVEX (V-01 UNVERIFIED) | C3b §10 SVE2 (V-08 UNVERIFIED) | C3b §10 RVV (V-12 UNVERIFIED) | C3b §10 PTX text | NEW §7.2 |
| `dot` | C3b §10 | C3b §10 | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 |
| `mat_vec` | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 | NEW §7.2 |
| `reduce_sum` | C3b §10 | C3b §10 | C3b §10 | C3b §10 | NEW §7.2 | NEW §7.2 | C3b §10 (shfl.sync tree) | NEW §7.2 |
| `masked_store` | C3b §10 | C3b §10 | C3b §10 | C3b §10 (k-mask) | C3b §10 (SVE2 ST1W) | C3b §10 (RVV vm=0) | NEW §7.2 | NEW §7.2 |

**C3b §10 carries 24 byte-level fixtures.** The 16 NEW goldens are specified as:

### 7.2 New Golden Specifications (16 goldens)

Each new golden specifies: input MIR sketch, primary spec citation, expected encoding
status. Byte sequences are NOT duplicated here — they are authored in the golden files
themselves, pinned to the spec section cited.

| # | Target | Kernel | Primary spec | Status | Notes |
|---|--------|--------|-------------|--------|-------|
| G-25 | SPIR-V | saxpy | Vulkan SPIR-V 1.5 §3.32 OpFAdd/OpFMul | UNVERIFIED | OpFAdd + OpFMul word sequence |
| G-26 | SPIR-V | dot | SPIR-V 1.5 §3.32 OpDot | UNVERIFIED | OpDot convenience instruction |
| G-27 | SPIR-V | mat_vec | SPIR-V 1.5 OpMatrixTimesVector | UNVERIFIED | or OpFMul+OpFAdd expansion |
| G-28 | SPIR-V | reduce_sum | SPIR-V 1.5 OpGroupFAdd (subgroup) | UNVERIFIED | subgroup reduce |
| G-29 | SPIR-V | masked_store | SPIR-V 1.5 OpStore + pred select | UNVERIFIED | predicated write |
| G-30 | AVX2 | dot | Intel SDM VDPPS or VFMADD+tree | VERIFIED (errata §6-F) | VFMADD213PS tree |
| G-31 | AVX-512 | dot | Intel SDM VFMADD213PS EVEX | UNVERIFIED (V-01) | EVEX bytes unverified |
| G-32 | SVE2 | dot | ARMv9 ARM FMLA+FADDV | UNVERIFIED (V-08) | SVE2 32-bit words |
| G-33 | RVV | dot | RVV spec vfmacc+vfredusum | UNVERIFIED (V-12,V-16) | vfmacc funct6 unverified |
| G-34 | PTX | dot | PTX ISA §9 fma.rn.f32 + shfl.sync | UNVERIFIED (V-23) | shfl form unverified |
| G-35 | NEON | mat_vec | ARMv8 ARM FMLA V.4S lane form | VERIFIED | FMLA Vd.4S,Vn.4S,Vm.S[lane] |
| G-36 | SSE2 | mat_vec | Intel SDM SHUFPS+ADDPS | VERIFIED (B2 §3.5) | 4× SHUFPS+ADDPS |
| G-37 | SVE2 | reduce_sum | ARMv9 ARM FADDV vs FADDA | UNVERIFIED (V-08) | ordered vs unordered C1 §9.4 |
| G-38 | RVV | reduce_sum | RVV spec vfredosum | UNVERIFIED (V-12) | ordered reduction |
| G-39 | PTX | masked_store | PTX ISA §9 st.global.f32 + setp | UNVERIFIED (V-23) | pred-guarded store |
| G-40 | AVX-512 | mat_vec | Intel SDM VFMADD213PS EVEX | UNVERIFIED (V-01) | EVEX broadcast form |

---

## 8. T5 — Fuzz Tests

**Path scheme:** `test/fuzz/simd/<dimension>_fuzz_spec.spl`
**Runner:** `bin/simple test test/fuzz/simd/ --mode=compiled` (nightly CI only)
**Oracle:** scalar reference loop — same kernel, same inputs, computed without SIMD.
**Timeout:** 5 seconds per kernel invocation; hard-kill at 10 seconds.

### 8.1 Random Kernel Generator

Shape: `(load × N) → (op × M) → (store × N)` where:
- T drawn from `{f32, f64, i32, i64}`
- N drawn from `{2, 4, 8, 16}` (FixedVec) or `scalable` (ScalableVec on SVE2/RVV)
- Target drawn uniformly from `{NEON, SSE2, AVX2, AVX-512, SVE2, RVV}`
- Op chain: 1–4 ops from `{add, mul, fma, sub, min, max, mask_select, reduce_sum}`
- Inputs: random f32 in `[-1e6, 1e6]` (NaN-free for bit-exact kernels; NaN injected
  in 10% of iterations for NaN-tolerance kernels)

Default iteration count: **100,000** (env var `SIMD_FUZZ_ITERS` overrides).

```
test/fuzz/simd/random_kernel_fuzz_spec.spl
test/fuzz/simd/nan_injection_fuzz_spec.spl
test/fuzz/simd/scalable_vec_fuzz_spec.spl
```

### 8.2 Errata-Driven Targeted Seeds (12 seeds — C1 §6 items A–L)

Each C1 §6 errata item gets a dedicated fuzz seed that specifically exercises the
guarded code path. Seeds are deterministic (fixed `SIMD_FUZZ_SEED=<n>`).

| Seed | Errata ID | C1 § | Guard | What the seed exercises |
|------|-----------|------|-------|------------------------|
| FS-01 | 6-A (scatter conflict) | §6-A | G-07 | AVX-512 scatter with deliberately conflicting indices |
| FS-02 | 6-B (scatter mask-clear) | §6-B | G-07 | Each scatter lane clears its k-mask bit after write |
| FS-03 | 6-C (SVE2 streaming mode) | §6-C | G-06 | Emit SMSTART/SMSTOP boundary — asserts false (SME out-of-scope) |
| FS-04 | 6-D (vstart non-zero) | §6-D | G-05 | RVV after trap resume; vstart=0 assertion fires |
| FS-05 | 6-E (ZMM freq throttle) | §6-L | G-13 | AVX-512 on SKX emits W_ZMM_FREQ_THROTTLE |
| FS-06 | 6-F (FMA form mismatch) | §6-F | G-04 | All 3 FMA forms (132/213/231) × each target |
| FS-07 | 6-G (PTX self-mask) | §6-G | G-08 | `shfl.sync` with mask `0xffffffff` (self-included) |
| FS-08 | 6-H (Apple M WarpVec) | §6-H | G-03 | `WarpVec` call on Apple M target → E_WARP_NO_APPLE_M |
| FS-09 | 6-J (RVV v0 pressure) | §6-J | G-02 | Masked RVV op without prior `vmv1r.v v0` → ICE |
| FS-10 | 6-K (NEON cmp_gt swap) | §6-K | S-09 | FCMGT with operands reversed → correct semantics |
| FS-11 | 6-L (ZMM throttle on pre-SPR) | §6-L | G-13 | Warning emitted; output still correct |
| FS-12 | k0 reservation | §1.4 | G-01 | k0 passed to any EVEX kreg operand → assert ICE |

### 8.3 V-Series UNVERIFIED Encoder Seeds (13 seeds — C3b §14)

One targeted seed per major UNVERIFIED claim. Purpose: if the byte encoding is wrong,
the fuzz run produces a mismatched output vs the oracle, catching the bug before
the golden tests are pinned.

| Seed | V-ID | Claim at risk | Fuzz strategy |
|------|------|--------------|---------------|
| FS-13 | V-01 | EVEX P0/P1/P2 bit positions | Run SAXPY on AVX-512; disassemble output; compare mnemonic |
| FS-14 | V-02 | EVEX opcode map mm=10 for VFMADD | FMA kernel on AVX-512; check disassembly |
| FS-15 | V-03 | EVEX W=0 for f32 | f32 vs f64 FMA; check W bit in P0 |
| FS-16 | V-05 | EVEX L'L=10 for ZMM | ZMM load; check L'L in P2 |
| FS-17 | V-06 | EVEX P2 z-bit position | Masked-zero store; check z-bit |
| FS-18 | V-08 | SVE2 encoding bit-26 size field | SVE2 FADD; check size bits in word |
| FS-19 | V-09 | SVE2 pred field pg[3:0] position | SVE2 predicated op; check pg bits |
| FS-20 | V-12 | RVV funct3 position in opcode | RVV vfadd.vv; check funct3 |
| FS-21 | V-14 | RVV vm bit position | Masked RVV load; check vm=0 |
| FS-22 | V-16 | RVV vfmacc funct6=0b011000 | RVV FMA kernel; funct6 check |
| FS-23 | V-23 | PTX shfl.sync syntax | PTX reduce kernel; check PTX text output |
| FS-24 | V-38 | vstart/vsetvli ordering | RVV after simulated trap; vstart check |
| FS-25 | V-xx | NEON FADDP scalar reduce form | NEON horiz-sum; check encoding |

---

## 9. T6 — Perf Gates

**Path scheme:** `test/perf/simd/<target>_<kernel>_gate_spec.spl`
**Runner:** `bin/simple test test/perf/simd/ --mode=compiled` (weekly + on-demand)
**Regression policy:** per `doc/05_design/mcp_performance_regression_enforcement.md`:
- 5% throughput drop → gate FAILS (blocks PR)
- 10% throughput drop → blocks merge until root-caused

All thresholds below are derived from C1 §4 latency/throughput tables and marked
**NEEDS-VERIFICATION** where C1 itself marks them `[UNVERIFIED]`.

### 9.1 SAXPY Throughput Gates (N=10M f32 elements)

The criterion matches C1 §1.1: ≥ 95% of peak FMA throughput on the reference machine.
GFLOP/s figures are NEEDS-VERIFICATION until measured on target hardware.

| Target | Reference machine | C1 §4 TP basis | Gate (GFLOP/s) | Status |
|--------|-----------------|----------------|----------------|--------|
| AVX-512 (Sapphire Rapids) | Icelake-Server or SPR | 2 FMAs/cycle × 16 f32 × freq | ≥ 800 GFLOP/s | NEEDS-VERIFICATION |
| AVX2 (Skylake) | Skylake or later | 2 FMAs/cycle × 8 f32 × freq | ≥ 200 GFLOP/s | NEEDS-VERIFICATION |
| NEON (Apple M2 / Cortex-X3) | Neoverse N1 or Apple M-series | FMLA TP=0.25 cyc × 4 f32 × freq (C1 §4.3 UNVERIFIED) | ≥ 80 GFLOP/s | NEEDS-VERIFICATION |
| SVE2 (Cortex-A715, VL=128) | `qemu-aarch64 -cpu max,sve2=on` | FMLA TP=0.33 cyc × 4 f32 × freq (C1 §4.4 UNVERIFIED) | ≥ 40 GFLOP/s QEMU-model | NEEDS-VERIFICATION |
| RVV (SiFive P670, VLEN=128, LMUL=1) | `qemu-system-riscv64 -cpu rv64,v=true,vlen=128` | vfmacc TP=1 cyc/group (C1 §4.5 UNVERIFIED) | ≥ 20 GFLOP/s QEMU-model | NEEDS-VERIFICATION |

Note: QEMU cycle counts are approximations; flag if QEMU yields < 50% of theoretical
(C1 §1.1 policy). AMD Zen4 AVX-512 double-pumped behavior (C1 §4.2) is tracked as an
open question (§14-OQ-4).

### 9.2 Per-Op Latency Gates

Latency measured as single-op kernel execution time (N=1, repeated 1M times, median).

| Op | Target | C1 §4 latency | Max latency gate | Status |
|----|--------|--------------|-----------------|--------|
| FMA f32×4 | NEON (M2) | 4 cycles (C1 §4.3 UNVERIFIED) | ≤ 6 cycles | NEEDS-VERIFICATION |
| FMA f32×8 | AVX2 (Skylake) | 5 cycles (C1 §4.1) | ≤ 8 cycles | NEEDS-VERIFICATION |
| FMA f32×16 | AVX-512 (ICL/SPR) | 4 cycles (C1 §4.1) | ≤ 6 cycles | NEEDS-VERIFICATION |
| Gather f32×4 | NEON (synth) | ~10 cycles (scalar loop) | ≤ 20 cycles | NEEDS-VERIFICATION |
| Gather f32×8 | AVX2 | ~12 cycles (C1 §4.1) | ≤ 20 cycles | NEEDS-VERIFICATION |
| Gather f32×16 | AVX-512 | ~20 cycles (C1 §4.1) | ≤ 35 cycles | NEEDS-VERIFICATION |
| reduce_sum f32×4 | NEON | ~6 cycles FADDP tree | ≤ 10 cycles | NEEDS-VERIFICATION |
| reduce_sum f32×16 | AVX-512 | ~15 cycles software tree | ≤ 25 cycles | NEEDS-VERIFICATION |
| masked_store f32×16 | AVX-512 | ~5 cycles VMOVAPS{k} | ≤ 10 cycles | NEEDS-VERIFICATION |

### 9.3 Gate File Convention

Each gate spec records the baseline at time of first measurement (M7 exit):
```
# baseline_date: YYYY-MM-DD
# baseline_gflops: <measured>
# gate_gflops: <baseline * 0.95>
# machine: <hostname or QEMU config>
```
Gate comparison uses `to_be_greater_than(gate_gflops)` in the spec `it` block.

---

## 10. GPU/CUDA and Vulkan End-to-End Tests

**Path scheme:**
- CUDA: `test/e2e/simd/cuda/<kernel>_cuda_e2e_spec.spl`
- Vulkan: `test/e2e/simd/vulkan/<kernel>_vulkan_e2e_spec.spl`

### 10.1 CUDA / PTX End-to-End

**Kernel:** `matmul_tile` — 16×16 tile matmul using `WarpVec` FMA.

| Test name | What it checks | Gate condition |
|-----------|---------------|----------------|
| `cuda_matmul_tile_compiles_to_ptx` | PTX text output contains `fma.rn.f32` | compile-only; always runs |
| `cuda_matmul_tile_ptx_version_header` | PTX header lists `.version` matching pinned CUDA SDK | SDK pinning per B3 §6 |
| `cuda_matmul_tile_executes_on_sm70` | kernel launches and returns correct C matrix | requires `nvidia-smi` SM_70+; `@skip_no_gpu` otherwise |
| `cuda_matmul_tile_output_matches_reference` | tiled output == naive matmul reference | numeric correctness |
| `cuda_warp_vec_skip_on_apple_m` | `WarpVec` compile target=AppleM → `E_WARP_NO_APPLE_M` (SKIP, not FAIL) | C2 §9, G-03 |

**PTX SDK-version pinning:** every CUDA test file header includes:
```
# cuda_sdk_version: 11.8
# ptx_version: 7.8
# sm_target: sm_70
```
Version mismatch between pinned and detected CUDA triggers a test warning, not failure.

**Apple M divergence:** `WarpVec` tests targeting Apple M platforms are tagged
`@expected_skip(reason: "E_WARP_NO_APPLE_M — WarpVec unsupported on Apple M")`.
They MUST appear as SKIP in the test report, not as FAIL or PASS.

---

## 11. Test-Runner Integration

### 11.1 `bin/simple test` Routing

| Tier | Invocation | Notes |
|------|-----------|-------|
| T1 (all unit) | `bin/simple test test/unit/compiler/ --mode=compiled` | Runs encoder, MIR-pass, and diagnostic specs |
| T2 (integration) | `bin/simple test test/feature/simd/ --mode=compiled` | Uses host target by default; pass `--target=<triple>` for cross |
| T3 (equivalence) | `scripts/test/simd_cross_target_runner.shs` | Wraps QEMU per-target; calls `bin/simple test` internally |
| T4 (goldens) | `bin/simple test test/backend/simd_strict_emit/ --mode=compiled` | Golden diff via `scripts/test/golden_diff.shs` |
| T5 (fuzz) | `bin/simple test test/fuzz/simd/ --mode=compiled` (nightly only) | `SIMD_FUZZ_ITERS=100000` default |
| T6 (perf) | `bin/simple test test/perf/simd/ --mode=compiled` (weekly) | Requires `--perf` flag to enable; skipped by default |

All tiers feed `doc/08_tracking/test/test_result.md` via the existing test-result
auto-update path (`src/app/test_runner_new/`). SKIP entries for GPU/platform-unavailable
tests appear as `SKIP(reason)` in the report, not as PASS or FAIL.

### 11.2 QEMU Wrapper Invocations

`scripts/test/simd_cross_target_runner.shs` (to be created at M3) wraps:

```
# SVE2
qemu-aarch64 -cpu max,sve2=on -L /usr/aarch64-linux-gnu \
  ./out_aarch64/<kernel>_equiv

# RVV (QEMU)
qemu-system-riscv64 -nographic -machine virt \
  -cpu rv64,v=true,vlen=128,elen=64 \
  -kernel ./out_riscv64/<kernel>_equiv

# AVX-512 (no hardware)
qemu-system-x86_64 -cpu Icelake-Server \
  -kernel ./out_x86_64_avx512/<kernel>_equiv
```

### 11.3 Spike Simulator for RVV

When QEMU RVV is too slow for perf measurement or when vlen > 128 testing is needed:

```
spike --isa=rv64gcv --varch=vlen:256,elen:64 \
  pk ./out_riscv64/<kernel>
```

Spike is used for T6 RVV perf gates when QEMU cycle model is insufficient. Install
path: `scripts/setup/install_spike.shs` (to be created at M4).

### 11.4 PASS/FAIL Aggregation

- Aggregation script: `scripts/test/aggregate_simd_results.shs` (to be created at M1)
- Reads per-tier result files from `build/test/results/simd_t{1..6}_results.json`
- Writes summary to `doc/08_tracking/test/test_result.md` (auto-generated per project
  structure rules)
- Exit code 0 only if T1+T2 pass; T3 failure is non-blocking pre-M3; T5/T6 never block
  PR (nightly/weekly only)

---

## 12. Test-Tier Dependency Graph and Gating Policy

### 12.1 ASCII Dependency Diagram

```
  [T1 Unit]
      |
      | (must pass)
      v
  [T2 Integration — host targets]
      |
      | (must pass on host)
      v
  [T3 Cross-target Equivalence]   <-- requires QEMU runners (M3+)
      |
      | (required at M3/M4 phase exit)
      v
  [T4 Goldens] <-- spot-check during dev; MANDATORY at each phase exit
      |
  (independent nightly/weekly tracks)
      |
  [T5 Fuzz] --------> nightly CI only; failures open bugs, don't block PRs
  [T6 Perf] --------> weekly + on-demand; 5% drop blocks PR, 10% blocks merge
```

### 12.2 Per-Phase Gating (maps to C4a phases M0–M7)

| Phase | Required tiers | Gating tests |
|-------|---------------|--------------|
| M0 exit | T1 (MIR+diagnostic only) | All `test/unit/compiler/` green |
| M1 exit | T1 full + T4 (20 CPU goldens) | All encoder unit tests + 20 T4 goldens byte-exact |
| M2 exit | T1 + T2 (host targets) | predicate_promote T1 + T2 compile_debug on host |
| M3 exit | T1 + T2 + T3 (SVE2) + T4 (SVE2 goldens) | SVE2 QEMU T3 equivalence + 5 SVE2 T4 goldens |
| M4 exit | T1 + T2 + T3 (RVV) + T4 (RVV goldens) | RVV QEMU/Spike T3 + 5 RVV T4 goldens |
| M5 exit | T1 + T2 (PTX/SPIR-V) + T4 (GPU goldens) + §10 e2e | PTX/SPIR-V T4 text-exact + CUDA e2e |
| M6 exit | T1 (auto-vectorize) + T2 (AV patterns) | `bin/simple desugar` shows SimdXxx in 5 patterns |
| M7 exit | T1 + T2 + T3 + T4 (all 40) + T6 | LMUL invariance + 95% throughput perf gates |

### 12.3 Policy Notes

- T4 goldens marked UNVERIFIED are still mandatory at phase exit — they MUST match the
  emitted bytes, even if the bytes themselves are not yet primary-spec verified. The
  UNVERIFIED status tracks spec-verification debt, not test-passing debt.
- T5 fuzz failures discovered nightly become bugs in `doc/TODO.md` via
  `bin/simple todo-scan`; they do not block the current PR.
- T6 perf baselines are set once at M7 entry (first measurement); subsequent runs
  compare against that baseline per `mcp_performance_regression_enforcement.md`.

---

## 13. Pre-Flight Infrastructure Tasks

Tasks required BEFORE M0 can begin gating tests. Each has an owner category,
complexity estimate (S/M/L), and blocking phase.

| # | Task | Owner | Complexity | Blocking phase | Notes |
|---|------|-------|-----------|----------------|-------|
| I-01 | QEMU + SVE2 CI runner setup (`qemu-aarch64 -cpu max,sve2=on`) | infra | M | M3 | `scripts/setup/install_qemu_sve2.shs` |
| I-02 | QEMU + RVV CI runner (`qemu-system-riscv64 -cpu rv64,v=true,vlen=128`) | infra | M | M4 | May reuse FreeBSD QEMU infra patterns |
| I-03 | Spike RVV simulator install script | infra | S | M4 | Needed when QEMU cycle model insufficient for T6 |
| I-04 | AVX-512 QEMU runner (`-cpu Icelake-Server`) | infra | S | M1 | Only needed if no HW AVX-512 in CI |
| I-05 | PTX SDK-version pinning registry | backend-gpu | S | M5 | File `scripts/test/cuda_sdk_version_registry.shs` |
| I-06 | Vulkan validation layer + llvmpipe install | infra | M | M5 | `VK_LAYER_KHRONOS_validation` + Mesa llvmpipe |
| I-07 | Golden diff runner script (`scripts/test/golden_diff.shs`) | test | S | M1 | Byte-diff + disassembly decode on mismatch |
| I-08 | Cross-target QEMU wrapper script (`scripts/test/simd_cross_target_runner.shs`) | test | M | M3 | Per-target QEMU dispatch |
| I-09 | Perf-regression baseline measurement infra | test | L | M7 | Baseline JSON per target; compare at gate time |
| I-10 | SIMD result aggregation script (`scripts/test/aggregate_simd_results.shs`) | test | S | M1 | Feeds `doc/08_tracking/test/test_result.md` |
| I-11 | `llvm-objdump` / `spirv-dis` available in CI for golden mismatch decode | infra | S | M1 | Required for human-readable golden diff output |
| I-12 | Apple M detection in CI for `@expected_skip(E_WARP_NO_APPLE_M)` | infra | S | M5 | `uname -m` + `sysctl hw.optional.arm64` |

---

## 14. Open Test-Side Questions

The following items could not be fully pinned from C1/C2/C3 sources. Each needs a
concrete resolution before the relevant test tier is finalized.

| # | Question | Blocking tier | Resolution path |
|---|----------|--------------|-----------------|
| OQ-1 | **Exact GFLOP/s thresholds for T6 gates.** C1 §4.3 (Apple M) and §4.4 (SVE2 Cortex-A715) latency/TP numbers are explicitly `[UNVERIFIED]` training-data estimates. Thresholds in §9 are placeholder until measured on real hardware or authoritative microbenchmark. | T6 | Run SAXPY microbenchmark at M7 entry; set baseline from measurement; pin `gate_gflops = measured * 0.95`. |
| OQ-2 | **AMD Zen4 AVX-512 double-pump testing.** C1 §4.2 documents that Zen4 executes 512-bit AVX-512 as two 256-bit micro-ops. This may halve observed throughput vs Intel SKX. No Zen4 hardware is currently specified in CI. Should the T6 gate have a Zen4-specific lower threshold, or is Zen4 a separate optional gate? | T6 | Decision needed: add Zen4 CI runner or document as out-of-scope for M7. |
| OQ-3 | **Apple M OptionalSVE detection at runtime in CI.** `HWCAP_SVE` is always 0 on Apple M (C3b §8.3 note). The `@expected_skip(E_WARP_NO_APPLE_M)` skip machinery must detect Apple M at test-runner time, not just at compile time. Is `uname -m == arm64` + `sysctl hw.optional.arm64 == 1` the correct CI detection? | T3, T5 | Verify with an Apple M CI runner before M5. |
| OQ-4 | **RVV `vfredosum.vs` vs `vfredusum.vs` tolerance window.** §6.4 sets a 4 ULP tolerance for `reduce_sum` on RVV due to ordered vs unordered reduction (C1 §9.4). Is 4 ULP sufficient for all f32 N=10M inputs, or do pathological inputs (alternating sign, near-cancellation) require a larger window? | T3 | Run cross-target reduce_sum sweep with random sign-alternating inputs before M4 exit. |
| OQ-5 | **SPIR-V golden byte stability across Vulkan driver versions.** SPIR-V IR is platform-neutral, but spirv-tools version affects validation and `spirv-val` errors. Are the SPIR-V goldens (G-25..G-29) pinned to a specific spirv-tools version, or are they driver-agnostic at the IR word level? | T4 (SPIR-V goldens) | Pin `spirv-tools` version in `scripts/setup/install_spirv_tools.shs`; document in each golden header. |
| OQ-6 | **V-series UNVERIFIED encoder byte resolution timeline.** 13 V-series items (V-01..V-38 selected) remain unverified against primary specs (Intel SDM, ARMv9 ARM, RVV spec). If any V-series item is resolved as WRONG, the corresponding T4 golden must be re-baselined and the fuzz seed updated. Who owns V-series resolution, and what is the deadline relative to M1/M3/M4? | T4 | Assign V-01..V-07 to backend-cpu before M1 exit; V-08..V-11 before M3; V-12..V-22 before M4. |
| OQ-7 | **SVE2 streaming mode (SME) guard G-06 scope.** C3b G-06 asserts `false` for any SMSTART/SMSTOP emission ("SME streaming not supported"). Should T5 fuzz seed FS-03 be a PASS (assert fires, test expects ICE) or SKIP (SME out of scope)? Clarify in the test spec before M3. | T5 | Decide: if SME is permanently out-of-scope, FS-03 should be `@expected_skip`; if it will be added later, keep as ICE-assert test. |

### 10.2 Vulkan / SPIR-V End-to-End

**Kernel:** `add_vec` — elementwise f32 vector add as a compute shader.

| Test name | What it checks | Gate condition |
|-----------|---------------|----------------|
| `vulkan_add_vec_compiles_to_spirv` | SPIR-V binary is valid per `spirv-val` | compile-only |
| `vulkan_add_vec_executes_on_llvmpipe` | runs on Mesa llvmpipe Vulkan driver | requires Vulkan loader; `@skip_no_vulkan` |
| `vulkan_add_vec_output_matches_reference` | output buffer == scalar reference | numeric |
| `vulkan_add_vec_validation_layer_clean` | no Vulkan validation errors in output | VK_LAYER_KHRONOS_validation |

**Hardware-unavailable fallback:** when no Vulkan-capable GPU is detected, tests run on
Mesa llvmpipe (software renderer). Tests are not skipped — llvmpipe is the CI baseline.

