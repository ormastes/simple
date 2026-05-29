<!-- claude-design -->
# Design: SIMD Rollout Plan v2 (Round 2 — refined)

**TL;DR.** This document refines the Round-1 B3 plan (M0–M7, 794 lines) with phase-level
entry/exit criteria drawn from C2's diagnostic codes (C2 §9), concrete errata-guard
activation schedules (C3b §13 G-01..G-13), a file-by-file touch table derived from C3a's
helper inventory (~112 helpers across 7 backend files), and a tightened risk register
anchored to C1 §10 V-series unverified items. Two new phases M8 (mixed-precision) and M9
(tensor-core placeholder) are added beyond the B3 spine. For the companion test catalog
(golden fixtures, per-helper test cases, cross-target equivalence suites) see
`doc/05_design/simd_test_catalog.md` (C4b).

---

## Table of Contents

1. [Phase Shape — M0..M9](#1-phase-shape)
2. [File-by-File Touch List](#2-file-by-file-touch-list)
3. [Diagnostic-Code Rollout Schedule](#3-diagnostic-code-rollout-schedule)
4. [Errata-Guard Rollout Schedule](#4-errata-guard-rollout-schedule)
5. [Risk Register v2](#5-risk-register-v2)
6. [Sequencing Rationale v2](#6-sequencing-rationale-v2)
7. [Effort Summary v2](#7-effort-summary-v2)
8. [Open Questions / Followups v2](#8-open-questions--followups-v2)

---

## 1. Phase Shape

Phase dependency DAG (unchanged from B3 §8; M8 appended after M7):

```
M0 ──► M1 ──► M2 ──► M3 ──► M4 ──────────► M7 ──► M8
                └──────────► M5 ──► M6 ──► M7
M9 (placeholder — no predecessor required; scope-defined only)
```

---

### M0 — Type IR Foundations

**Purpose.** Replace the 19-line `00.common/simd_types.spl` stub with complete SIMD type
IR; define `Vector`/`Mask`/`WarpVec` trait stubs in `25.traits/`; introduce
`FixedVec<T,N>`, `ScalableVec<T>`, `FixedMask<N>`, `ScalableMask`; retire the 5
hardcoded scalar structs in `simd_vector_types.spl` behind back-compat aliases.

- **Inputs:** existing stubs (`simd_types.spl:1–19`, `simd_vector_types.spl:57,323,440`)
- **Outputs:** `00.common/simd_types.spl` (+250L), `25.traits/vector_traits.spl` (NEW 150L),
  `30.types/simd_vector_types.spl` (net −300L), `src/lib/nogc_sync_mut/simd/` (6 NEW files,
  ~400L total). Ref: C2 §3.2, B1 §2, B1 §8.2–8.3.
- **Owner workstream:** compiler-frontend, stdlib
- **Entry criteria:** no prior phase; repo must build (`bin/simple build` passes)
- **Exit criteria (compiled mode):**
  - `bin/simple build` passes with no new errors
  - `bin/simple desugar src/compiler/30.types/simd_vector_types.spl` emits `FixedVec<f32,4>`
    alias expanding to the old `Vec4f`
  - `bin/simple test test/types/simd_type_aliases.spl` passes in compiled mode
  - Zero `E_SIMD_BAD_LANES` or `E_SIMD_TYPE_MISMATCH` on well-formed inputs
- **Diagnostic codes activated:** `E_SIMD_BAD_LANES`, `E_SIMD_TYPE_MISMATCH` (C2 §9 Table 9-A,
  type-check phase). See §3.
- **Errata guards activated:** none (no backend emit in M0)
- **Estimated complexity:** M (B1 §8.2 net: ~610 lines gross, ~310 net after deletions)
- **Bootstrap rebuild required:** NO
- **Risks:** alias-expansion regression silently breaks existing Vec4f callers; mitigate by
  running the full existing simd test suite as part of exit gate.

---

### M1 — Fixed + Mask + AVX-512 Strict-Emit

**Purpose.** Type-check `FixedVec<T,N>` end-to-end; lift NEON, SSE2/SSE4, and AVX2 onto the
`Vector` trait; land `x86_64_avx512.spl` with EVEX encoder, k0 reserve guard (G-01), and
VFMADD form-select guard (G-04); activate type-check and mir_opt diagnostic codes from
C2 §9; add `MirInstKind::MaskOp`, `SimdGather`, `SimdScatter`, `SimdPermute`, `SimdShuffle`
variants.

- **Inputs:** M0 outputs
- **Outputs:** `35.semantics/simd_check.spl` (+120L), `40.mono/instantiation.spl` (+80L),
  `50.mir/mir_types.spl` (+60L), `50.mir/mir_instructions.spl` (+80L),
  `50.mir/mir_lowering_expr.spl` (+200L), `60.mir_opt/mir_opt/simd_lowering.spl` (+60L),
  `70.backend/backend/native/arm_neon.spl` (+80L), `70.backend/backend/native/x86_64_simd.spl`
  (+120L — keep monolithic per C3a §5.2; SSE+AVX2 share `_encode_simd_3op_xmm/ymm`),
  `70.backend/backend/native/x86_64_avx512.spl` (NEW ~500L),
  `70.backend/portable_numeric_capabilities.spl` (+40L),
  `test/backend/simd_strict_emit/avx512/` (5 golden files NEW),
  `test/backend/simd_strict_emit/neon/` (5 golden files NEW),
  `test/backend/simd_strict_emit/sse_avx2/` (5 golden files NEW).
  Ref: C2 §3.2, C3a §2.4, C3a §5.2, C3a §5.3.
- **Owner workstream:** backend-cpu, compiler-frontend, tests
- **Entry criteria:**
  - M0 exit gate passes
  - V-01 (EVEX P0/P1/P2 bit field positions) verified against Intel SDM Vol 2A §2.6.1 Table 2-36
  - V-06 (`VFMADD213PS` byte example `62 F2 75 C9 A8 C2`) verified against Intel SDM Vol 2B
  - V-25 (NEON `vclt`/`FCMGT` operand reversal) verified against ARM ARM §C7.2 — blocks G-11 polarity
  - V-03 (k0 z-bit behaviour) verified (C3b §14)
- **Exit criteria (compiled mode):**
  - All 15 AVX-512/NEON/SSE/AVX2 golden byte-diff tests pass:
    `diff <(objdump -d out.o | grep -oP '\t[0-9a-f ]+\t') kernel.golden`
  - `bin/simple test test/compiler/simd_type_check.spl` passes in compiled mode
  - No `E_SIMD_BAD_LANES`, `E_SIMD_TYPE_MISMATCH`, `E_SIMD_NO_NATIVE_SCALAR_FALLBACK`
    on well-formed `FixedVec<f32,4>` SAXPY
  - `W_SIMD_AVX2_SCATTER_SLOW` fires on scatter site without AVX-512
- **Diagnostic codes activated:** all C2 §9 type-check codes + mir_opt fallback codes. See §3.
- **Errata guards activated:** G-01 (k0-reserve), G-04 (vfmadd-form), G-07 (scatter-conflict),
  G-11 (NEON vclt reversal). See §4.
- **Estimated complexity:** XL (~+1,720L; C1 §1.2–1.8 EVEX encoding complexity; C3a §5.3
  lists ~12 AVX-512 helpers; 3 backend files significantly modified)
- **Bootstrap rebuild required:** YES — new backend code paths wired from MIR
- **Risks:** V-01/V-06 byte errors silently wrong until golden diffed; V-25 G-11 polarity
  flips masked comparisons on NEON. Both are blocking entry criteria above.

---

### M2 — Predication Promotion Pass

**Purpose.** Add `60.mir_opt/predicate_promote.spl` liveness pass; emit `W_SIMD_PRED_PROMOTE_HINT`
hints; make `_z` (zero-fill) vs `_x` (undef) distinction first-class in MIR; wire
`MirInstKind::MaskOp` variants landed in M1 to `_z` default predication.

- **Inputs:** M1 outputs (`MirInstKind::MaskOp` must exist)
- **Outputs:** `60.mir_opt/mir_opt/predicate_promote.spl` (NEW ~200L),
  `50.mir/mir_lowering_expr.spl` (+40L — `_z` default annotation),
  `test/predication/predicate_promote_liveness.spl` (NEW ~100L).
  Ref: C2 §5.3, B1 §3.2.
- **Owner workstream:** mir-opt, compiler-frontend
- **Entry criteria:** M1 exit gate passes
- **Exit criteria (compiled mode):**
  - `_z` predication test: `bin/simple test test/predication/predicate_z.spl` passes compiled
  - `_x` promotion test: `bin/simple test test/predication/predicate_x_promote.spl` passes compiled
  - `W_SIMD_PRED_PROMOTE_HINT` fires at least once on the SAXPY-with-tail-mask benchmark
- **Diagnostic codes activated:** `W_SIMD_PRED_PROMOTE_HINT` (C2 §9 Table 9-B). See §3.
- **Errata guards activated:** none new (NEON G-11 already active from M1)
- **Estimated complexity:** M (~+340L total; C2 §5.3 liveness contract is well-specified)
- **Bootstrap rebuild required:** NO
- **Risks:** liveness analysis interacts with loop unrolling pass; false-positive hints on
  already-predicated ops.

---

### M3 — SVE2 Backend

**Purpose.** Introduce `ScalableVec<T>` lowering end-to-end; implement `arm_sve2.spl`
strict-emit with Z/P register model; add SVE2 capability detection via `mrs ID_AA64ZFR0_EL1`
(C1 §2.1); activate P15 reserved (C3b §8.3) and Apple M no-warp guard (G-03);
replace `SimdCapabilities` struct with `SimdFeatureFlags` bitmask (C2 §6, B1 §6).

- **Inputs:** M2 outputs (`predicate_promote` pass and `Mask<V>` MIR type must be complete)
- **Outputs:** `50.mir/mir_types.spl` (+60L — `ScalableVec`/`ScalableMask` wire-up),
  `50.mir/mir_lowering_expr.spl` (+120L — `ScalableVecOp` + vsetvl strip-mine loop),
  `30.types/simd_platform.spl` (+80L — SVE2 detection, `SimdFeatureFlags` bitmask),
  `70.backend/backend/native/arm_sve2.spl` (NEW ~600L — Z/P model, `_z` default,
  `svptrue_b32` prolog, `ld1_gather`, `st1_scatter`, `svand_b_z`, `sveor_b_z`),
  `35.semantics/gpu_checker.spl` (+40L — Apple M guard),
  `test/backend/simd_strict_emit/sve2/` (5 golden files NEW),
  `test/platform/simd_platform_detect_sve2.spl` (NEW ~80L).
  Ref: C1 §2.1, C2 §4, C3a §5.4, C3b §8.3.
- **Owner workstream:** backend-cpu, compiler-frontend, tests
- **Entry criteria:** M2 exit gate passes; QEMU SVE2 support confirmed:
  `qemu-aarch64 -cpu max,sve2=on /bin/true && echo ok`
- **Exit criteria (compiled mode):**
  - 5 SVE2 golden text-diff tests pass (QEMU `qemu-aarch64 -cpu max,sve2=on`)
  - `E_WARP_NO_APPLE_M` fires on `WarpVec` call with `target=apple-m`
  - Strip-mine loop test: ScalableVec SAXPY with N=7 (non-power-of-2) passes compiled
  - `bin/simple test test/platform/simd_platform_detect_sve2.spl` passes
- **Diagnostic codes activated:** `E_SCALABLE_NOT_FIXABLE`, `W_SIMD_HARDCODED_STRIDE`,
  `E_WARP_NO_APPLE_M`, `W_SIMD_FIXED_EXCEEDS_MIN_LANES` (C2 §9). See §3.
- **Errata guards activated:** G-03 (apple-m-no-warp), G-06 (sve2-smstart, assert-false stub).
  See §4.
- **Estimated complexity:** XL (~+980L total; C1 §2.1 Z/P register model complexity; C3a §5.4
  lists ~14 SVE2 helpers; strip-mine loop is non-trivial; P15 reserve requires allocator
  change per C3b §8.3)
- **Bootstrap rebuild required:** YES — `arm_sve2.spl` adds new MIR-wired backend code
- **Risks:** V-08 (SVE2 Z-register byte encoding UNVERIFIED); V-12 (SMSTART invalidates Z/P —
  out-of-scope but guard must be present). QEMU SVE2 VLEN may not match hardware; use
  `--sve-vector-bits=128` baseline.

---

### M4 — RVV Backend (LMUL=1)

**Purpose.** Implement `riscv_rvv.spl` strict-emit with LMUL=1 only; wire v0 mask-copy
convention (G-02); activate vstart=0 guard (G-05); activate vlmul=100 reserved hole guard
(G-09). LMUL widen deferred to M7.

- **Inputs:** M3 outputs (SVE2 scalable lowering template and `ScalableVecOp` MIR API must
  be frozen before RVV starts; C3b §8 regalloc argument — see §6)
- **Outputs:** `70.backend/backend/native/riscv_rvv.spl` (NEW ~600L — vsetvli, LMUL=1,
  vmv1r insertion, vstart=0 assertion after vsetvli, vlmul=100 reserve guard),
  `30.types/simd_platform.spl` (+50L — RVV `hwcap` probe + Zvfh/Zvfbfmin detection stubs),
  `test/backend/simd_strict_emit/rvv/` (5 golden files NEW),
  `test/platform/simd_platform_detect_rvv.spl` (NEW ~80L).
  Ref: C1 §3, C3a §5.5, C3b §4.6, C3b §8 G-02/G-05.
- **Owner workstream:** backend-cpu, tests
- **Entry criteria:**
  - M3 exit gate passes
  - V-13 (vlmul fractional encoding `101=mf8` etc.) verified against RVV spec §3.4.2 Table 4
  - V-15 (vfadd funct6=000000 OPFVV) verified against RVV inst-table
  - V-16 (vfmacc funct6=011000) verified (C3b §14)
  - QEMU RVV confirmed: `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64 --version`
- **Exit criteria (compiled mode):**
  - 5 RVV LMUL=1 golden byte-diff tests pass under QEMU riscv64
  - SAXPY and dot kernels produce identical output to reference scalar on LMUL=1
  - G-02 fires (assert) if vmv1r is skipped before a masked op in debug build
  - G-05 fires (assert) if vstart != 0 after vsetvli in debug build
  - `bin/simple test test/backend/simd_strict_emit/rvv/` passes compiled mode
- **Diagnostic codes activated:** `E_SCALABLE_NO_PTX` (already present), `W_SIMD_MASK_BITS_OOB`
  (RVV fractional LMUL mask width check). See §3.
- **Errata guards activated:** G-02 (vmv1r-before-mask), G-05 (vstart-zero), G-09
  (vlmul-reserved). See §4.
- **Estimated complexity:** L (~+830L; C1 §3 encoding tables are partially verified;
  C3a §5.5 ~15 RVV helpers; v0 mask-copy adds overhead to every masked op lowering)
- **Bootstrap rebuild required:** YES — new RVV backend wired from MIR
- **Risks:** V-13/V-15 byte errors make all RVV goldens wrong (hard block). V-38
  (vstart/vsetvli trap-resume hazard — non-blocking, guard comment incomplete).

---

### M5 — GPU WarpVec Skeleton

**Purpose.** Extend `gpu_intrinsics.spl` with `WarpVec<T>` warp-scoped ops; add PTX
`.v4` packed loads and `shfl.sync`/`vote.sync` per C1 §3.1; add SPIR-V subgroup ops
for Vulkan compute; wire `E_SCALABLE_NO_PTX` hard error; add `E_WARP_NOT_IN_KERNEL`
and `E_WARP_SELF_EXCLUDED` enforcement.

- **Inputs:** M1 outputs (FixedVec MIR must be wired; B1 §7 `FixedVec<f32,4>` → `OpTypeVector`)
- **Outputs:** `70.backend/gpu_intrinsics.spl` (+120L — `shfl_up/down/bfly/idx`,
  `warp_reduce_sum`, `warp_ballot`), `35.semantics/gpu_checker.spl` (+60L — kernel-only
  enforcement), `70.backend/backend/cuda/ptx_builder.spl` (+150L — `.v4.f32` packed load,
  `shfl.sync.*`, `vote.sync.ballot.b32`), `70.backend/backend/vulkan/spirv_builder.spl`
  (+120L — `OpTypeVector float32 4`, `OpGroupNonUniformShuffle`, `OpGroupNonUniformFAdd`,
  `OpGroupNonUniformBallot`), `test/backend/simd_strict_emit/ptx/` (5 PTX golden files NEW),
  `test/backend/simd_strict_emit/spirv/` (5 SPIR-V golden files NEW),
  `test/gpu/cuda_saxpy_warpvec.spl` (NEW ~100L), `test/gpu/vulkan_saxpy_warpvec.spl`
  (NEW ~100L). Ref: C1 §3.1, C1 §4, B1 §7, C3a §5.6–5.7.
- **Owner workstream:** backend-gpu, tests
- **Entry criteria:** M1 exit gate passes; CUDA driver API or `nvcc --ptx` available in CI
- **Exit criteria (compiled mode):**
  - 5 PTX text-diff goldens pass
  - `E_SCALABLE_NO_PTX` fires on `ScalableVec<f32>` in PTX target
  - `E_WARP_NOT_IN_KERNEL` fires on `WarpVec` call outside `@kernel` context
  - G-08 fires on `shfl.sync` with mask excluding calling lane
  - CUDA SAXPY end-to-end: `test/gpu/cuda_saxpy_warpvec.spl` compiled output passes
- **Diagnostic codes activated:** `E_SCALABLE_NO_PTX`, `E_WARP_NOT_IN_KERNEL`,
  `E_WARP_NO_APPLE_M` (already from M3), `E_WARP_DELTA_OOB`, `E_WARP_SELF_EXCLUDED`,
  `E_WARP_LANE_OOB`, `E_WARP_SIZE_RUNTIME_ONLY`, `W_WARP_SYNC_EMPTY_MASK`. See §3.
- **Errata guards activated:** G-08 (ptx-shfl-self), G-10 (rdna-wave32-default-hint),
  G-12 (spirv-subgroup-size-hint). See §4.
- **Estimated complexity:** L (~+850L; C1 §3.1 PTX shfl encoding verified; C3a §5.6 ~16
  PTX helpers, §5.7 ~17 SPIR-V helpers; GPU end-to-end needs driver API in CI)
- **Bootstrap rebuild required:** YES
- **Risks:** V-23 (PTX `shfl.sync` syntax UNVERIFIED); CI GPU unavailability — mitigate
  with PTX text-diff gate not requiring execution; SPIR-V validation via `spirv-val`.

---

### M6 — Auto-Vectorization Wiring

**Purpose.** Confirm and wire `auto_vectorize_codegen.spl` into the MIR opt pass driver;
verify 5 named loop patterns emit `SimdXxx` MIR on at least one CPU target; cross-verify
on all 5 CPU targets.

- **Inputs:** M2 outputs (Mask lowering complete); M1 outputs (`SimdXxx` MIR variants exist)
- **Outputs:** MIR opt driver pass file (wire-up, ~+20L if call site absent per A2 §7),
  `60.mir_opt/mir_opt/auto_vectorize_codegen.spl` (minor rename fixes ~+20L),
  `test/auto_vectorize/` (5 loop pattern tests NEW ~200L).
  Ref: B1 §5, A2 §7, C2 §3.
- **Owner workstream:** mir-opt, tests
- **Entry criteria:** M2 exit gate passes; M4/M5 must be complete so cross-target
  verification covers all 5 CPU targets plus GPU; first step is confirming wire-up:
  `grep -r 'auto_vectorize_codegen' src/compiler/60.mir_opt/ | grep -v 'auto_vectorize_codegen.spl'`
- **Exit criteria (compiled mode):**
  - 5 auto-vectorize loop patterns emit `SimdAddF32x*` or equivalent on x86-64 AVX2 compiled
  - Cross-target: same 5 patterns pass on NEON, SSE2, AVX2, AVX-512, RVV (QEMU where needed)
  - No `W_SIMD_NO_NATIVE_LOWERING` on simple SAXPY loop on any target with SIMD support
- **Diagnostic codes activated:** `W_SIMD_NO_NATIVE_LOWERING`, `W_SIMD_SCALAR_FALLBACK`
  (mir_opt phase). See §3.
- **Errata guards activated:** none new
- **Estimated complexity:** M (~+240L; A2 §7 notes the wire-up gap — may be zero-change if
  call site exists; 5 loop patterns are pre-coded in stubs)
- **Bootstrap rebuild required:** NO
- **Risks:** A2 §7 "call site unconfirmed" may mean more work; loop-pattern test may expose
  LMUL-width mismatch on RVV before M7.

---

### M7 — LMUL Widening + Perf Gates

**Purpose.** Implement `lmul_widen.spl` pass to promote LMUL=1 → LMUL=2/4 on hot RVV
loops behind `--enable-lmul-widen` flag; run SAXPY peak-throughput perf regression suite
on all 6 CPU targets; gate ship on perf parity.

- **Inputs:** M4 outputs (RVV LMUL=1 stable); M6 outputs (auto-vectorize green)
- **Outputs:** `60.mir_opt/mir_opt/lmul_widen.spl` (NEW ~250L), golden updates for
  `test/backend/simd_strict_emit/rvv/` (MODIFY), `test/perf/simd_perf_suite.spl`
  (NEW ~150L), `test/backend/lmul_equivalence/` (NEW ~80L).
  Ref: B1 §3.2, C1 §3.5–3.7.
- **Owner workstream:** mir-opt, backend-cpu, tests
- **Entry criteria:** M4 + M6 exit gates pass; V-13 verified (fractional LMUL encoding
  needed for widen stride table)
- **Exit criteria (compiled mode):**
  - LMUL=1 vs LMUL=2 output equivalence for SAXPY and dot on RVV QEMU
  - LMUL=4 equivalence likewise
  - SAXPY throughput with `--enable-lmul-widen=4` >= LMUL=1 throughput
  - All 6 CPU targets pass perf regression suite (throughput >= reference floor)
- **Diagnostic codes activated:** none new
- **Errata guards activated:** none new (G-02/G-05 already active from M4)
- **Estimated complexity:** M (~+695L; C1 §3.5–3.7 LMUL widen constraints well-specified;
  C3b §14 V-13 is entry-blocking)
- **Bootstrap rebuild required:** NO
- **Risks:** Cross-target equivalence failure if LMUL=2 widen changes memory-ordering
  semantics on misaligned vectors (non-blocking: flag gates it until 100 PR cycles pass).

---

### M8 — Mixed-Precision (F16 / BF16 / INT8)

**Purpose.** Add F16, BF16, and INT8 ops per C1 §8: AVX-512-FP16 (`_encode_avx512_fp16_*`),
AVX-512-BF16 (`VDPBF16PS`), SVE2 `BFCVT`/`BFDOT`/`BFMMLA`, RVV Zvfh (`vfloat16m1_t`,
`vfwcvt.f.f.v`), NEON BF16, PTX `bf16`/`mma` (non-tensor-core path only). INT8 VNNI on
AVX-512-VNNI. `W_SIMD_FP16_AUTOPROMOTE` warning on f16 fallback.

- **Inputs:** M7 outputs (all CPU backends stable and perf-gated); M5 outputs (PTX backend
  complete for bf16 path)
- **Outputs:**
  - `70.backend/backend/native/x86_64_avx512.spl` (+150L — AVX-512-FP16, BF16 VDPBF16PS,
    VNNI VP2INTERSECTD fallback)
  - `70.backend/backend/native/arm_sve2.spl` (+100L — BFCVT, BFDOT, BFMMLA)
  - `70.backend/backend/native/arm_neon.spl` (+60L — NEON BF16 BFDOT)
  - `70.backend/backend/native/riscv_rvv.spl` (+80L — Zvfh SEW=16 path, Zvfbfmin convert)
  - `70.backend/backend/cuda/ptx_builder.spl` (+80L — PTX `.bf16` type emit)
  - `30.types/simd_platform.spl` (+60L — F16/BF16/INT8 feature flag detection)
  - `00.common/simd_types.spl` (+30L — `SimdElementType` F16/BF16/INT8 variants)
  - `test/backend/simd_strict_emit/mixed_precision/` (10 golden files NEW)
  Ref: C1 §8.1 (AVX-512-FP16), C1 §8.3 (SVE2 BF16), C1 §8.4 (NEON BF16),
  C1 §8.5 (RVV Zvfh), C1 §8.6 (PTX bf16).
- **Owner workstream:** backend-cpu, backend-gpu, tests
- **Entry criteria:** M7 exit gate passes; RVV Zvfh probe confirmed in `simd_platform.spl`
  (C1 §8.5 notes Zvfh is optional extension)
- **Exit criteria (compiled mode):**
  - `W_SIMD_FP16_AUTOPROMOTE` fires on `FixedVec<f16,8>` on AVX2 (no FP16 native)
  - AVX-512-FP16 SAXPY golden passes on Sapphire Rapids or QEMU AVX-512-FP16
  - SVE2 BFDOT golden passes under QEMU `qemu-aarch64 -cpu max`
  - RVV Zvfh `vfloat16m1_t` SAXPY passes under QEMU with Zvfh enabled
  - INT8 VNNI dot golden passes (AVX-512-VNNI)
- **Diagnostic codes activated:** `W_SIMD_FP16_AUTOPROMOTE` (C2 §9 Table 9-B). See §3.
- **Errata guards activated:** none new (AVX-512 guards G-01/G-04/G-07 already active)
- **Estimated complexity:** L (~+1,400L gross; C1 §8 per-ISA mixed-precision differences
  significant; RVV Zvfh BF16 arithmetic requires convert+compute+convert pattern per
  C1 §8.5 — no native BF16 arithmetic; Sapphire Rapids hardware rare in CI)
- **Bootstrap rebuild required:** YES (new element-type variants in MIR)
- **Risks:** Sapphire Rapids AVX-512-FP16 hardware unavailable; mitigate with QEMU AVX-512-FP16
  emulation (QEMU 8.x supports). RVV Zvfh is optional extension — detection guard required.

---

### M9 — Tensor-Core / mma.sync (Placeholder)

**Purpose.** Scope-defined placeholder for CUDA `mma.sync` / `wmma::` API support
(`mma.m16n8k16.f32.f16.f16.f32`). Out of scope for first ship. Named here to prevent
ad-hoc addition to earlier phases.

- **Inputs:** M8 outputs (PTX bf16 path required as foundation)
- **Outputs:** scope-definition document only; no `.spl` files
- **Owner workstream:** backend-gpu
- **Entry criteria:** M8 complete; SM version >= 70 (Volta) confirmed in CI GPU
- **Exit criteria:** scope document approved (no compiled-mode gate for placeholder)
- **Diagnostic codes activated:** none (M9 placeholder only)
- **Errata guards activated:** G-13 (tensor-core-future, out-of-scope stub). See §4.
- **Estimated complexity:** S (scope-definition only; implementation is XL when activated)
- **Risks:** mma.sync API shape may conflict with `WarpVec` interface; resolve before
  activating by auditing `WarpVec` method catalog (C2 §6).

---

## 2. File-by-File Touch List

Columns: `path | action | phase | owner | est. LOC delta | depends on | C2/C3 ref`

Actions: NEW = new file, MODIFY = edit existing, SPLIT = split into multiple files,
RENAME = rename only, DELETE = remove, GEN = auto-generated (not manually committed).

> Note: C3a §5.2 explicitly recommends keeping `x86_64_simd.spl` monolithic for SSE+AVX2
> (shared `_encode_simd_3op_xmm/ymm` helpers) and adding only a separate `x86_64_avx512.spl`.
> The task brief's suggested 3-way split is overridden by the primary source.

### 2.1 Compiler — Common / Type Layers

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/compiler/00.common/simd_types.spl` | MODIFY | M0 | compiler-frontend | +250 | none | C2 §3.2, B1 §2 |
| `src/compiler/25.traits/vector_traits.spl` | NEW | M0 | compiler-frontend | +150 | `simd_types.spl` | C2 §1, B1 §8.2 |
| `src/compiler/30.types/simd_vector_types.spl` | MODIFY | M0 | compiler-frontend | −300 net | `vector_traits.spl` | C2 §3.2, B1 §8.3 |
| `src/compiler/30.types/simd_platform.spl` | MODIFY | M1+M3+M4+M8 | compiler-frontend | +80/+50/+60 | M0 type IR | C2 §6, C3b §9 |
| `src/compiler/35.semantics/simd_check.spl` | MODIFY | M1 | compiler-frontend | +120 | `vector_traits.spl` | C2 §3.2, B1 §3.2 |
| `src/compiler/35.semantics/gpu_checker.spl` | MODIFY | M3+M5 | compiler-frontend | +40/+60 | M0 type IR | C2 §6.4, G-03 |
| `src/compiler/40.mono/instantiation.spl` | MODIFY | M1 | compiler-frontend | +80 | M0 type IR | C2 §3 |

### 2.2 Compiler — HIR / MIR Layers

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/compiler/20.hir/` (method dispatch) | MODIFY | M1 | compiler-frontend | +60 | M0 type IR | C2 §3.1 |
| `src/compiler/50.mir/mir_types.spl` | MODIFY | M1+M3 | compiler-frontend | +60/+60 | M0 type IR | C2 §3.1, B1 §3.2 |
| `src/compiler/50.mir/mir_instructions.spl` | MODIFY | M1 | compiler-frontend | +80 | `mir_types.spl` | C2 §3.1, B1 §3.2 |
| `src/compiler/50.mir/mir_lowering_expr.spl` | MODIFY | M1+M2+M3 | compiler-frontend | +200/+40/+120 | M1 MIR types | C2 §3.1, B1 §3.2 |

### 2.3 Compiler — MIR Opt Layer

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/compiler/60.mir_opt/mir_opt/simd_lowering.spl` | MODIFY | M1 | mir-opt | +60 | M1 MIR instructions | B1 §3.2 |
| `src/compiler/60.mir_opt/mir_opt/predicate_promote.spl` | NEW | M2 | mir-opt | +200 | M1 MaskOp variants | C2 §5.3, B1 §3.2 |
| `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` | MODIFY | M6 | mir-opt | +20 | M1+M2 MIR | B1 §5, A2 §7 |
| `src/compiler/60.mir_opt/mir_opt/` (pass driver) | MODIFY | M6 | mir-opt | +20 | M6 wire-up | A2 §7 |
| `src/compiler/60.mir_opt/mir_opt/lmul_widen.spl` | NEW | M7 | mir-opt | +250 | M4 RVV LMUL=1 | B1 §3.2, C1 §3.5 |

### 2.4 Compiler — Backend: x86-64

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/compiler/70.backend/backend/native/x86_64_simd.spl` | MODIFY | M1 | backend-cpu | +120 | M1 MIR | C3a §5.2, C3b §4.2–4.3 |
| `src/compiler/70.backend/backend/native/x86_64_avx512.spl` | NEW | M1 | backend-cpu | +500 | `x86_64_simd.spl` | C3a §5.3, C3b §4.4, G-01, G-04 |
| `src/compiler/70.backend/portable_numeric_capabilities.spl` | MODIFY | M1 | backend-cpu | +40 | M1 AVX-512 | C3b §9.1 |

### 2.5 Compiler — Backend: ARM

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/compiler/70.backend/backend/native/arm_neon.spl` | MODIFY | M1+M8 | backend-cpu | +80/+60 | M1 MIR | C3a §5.1, C3b §4.1, G-11 |
| `src/compiler/70.backend/backend/native/arm_sve2.spl` | NEW | M3+M8 | backend-cpu | +600/+100 | M2 Mask MIR | C3a §5.4, C3b §4.5, G-03, G-06 |

### 2.6 Compiler — Backend: RISC-V

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/compiler/70.backend/backend/native/riscv_rvv.spl` | NEW | M4+M8 | backend-cpu | +600/+80 | M3 scalable MIR | C3a §5.5, C3b §4.6, G-02, G-05, G-09 |

### 2.7 Compiler — Backend: GPU

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/compiler/70.backend/gpu_intrinsics.spl` | MODIFY | M5 | backend-gpu | +120 | M1 FixedVec MIR | B1 §7, C1 §3.1 |
| `src/compiler/70.backend/backend/cuda/ptx_builder.spl` | MODIFY | M5+M8 | backend-gpu | +150/+80 | M5 WarpVec | C3a §5.6, C3b §4.7, G-08 |
| `src/compiler/70.backend/backend/vulkan/spirv_builder.spl` | MODIFY | M5 | backend-gpu | +120 | M5 WarpVec | C3a §5.7, C3b §4.8, G-12 |

### 2.8 Stdlib — `src/lib/nogc_sync_mut/simd/`

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `src/lib/nogc_sync_mut/simd/__init__.spl` | NEW | M0 | stdlib | +40 | none | B1 §8.3 |
| `src/lib/nogc_sync_mut/simd/fixed_vec.spl` | NEW | M0 | stdlib | +100 | `vector_traits.spl` | C2 §1.2, B1 §8.3 |
| `src/lib/nogc_sync_mut/simd/scalable_vec.spl` | NEW | M0 | stdlib | +80 | `vector_traits.spl` | C2 §1.3, B1 §8.3 |
| `src/lib/nogc_sync_mut/simd/warp_vec.spl` | NEW | M0 | stdlib | +60 | `vector_traits.spl` | C2 §6, B1 §8.3 |
| `src/lib/nogc_sync_mut/simd/platform.spl` | NEW | M0 | stdlib | +80 | none | C2 §6, B1 §8.3 |
| `src/lib/nogc_sync_mut/simd/compat.spl` | NEW | M0 | stdlib | +40 | `fixed_vec.spl` | B1 §8.3 |

### 2.9 Tests — Backend Golden Files

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `test/backend/simd_strict_emit/avx512/` (5 files) | NEW | M1 | tests | +150 | M1 AVX-512 emit | C3b §10, V-01, V-06 |
| `test/backend/simd_strict_emit/neon/` (5 files) | NEW | M1 | tests | +100 | M1 NEON emit | C3b §10, V-25 |
| `test/backend/simd_strict_emit/sse_avx2/` (5 files) | NEW | M1 | tests | +120 | M1 SSE/AVX2 emit | C3b §10 |
| `test/backend/simd_strict_emit/sve2/` (5 files) | NEW | M3 | tests | +100 | M3 SVE2 emit | C3b §10, V-08 |
| `test/backend/simd_strict_emit/rvv/` (5 files) | NEW | M4 | tests | +100 | M4 RVV emit | C3b §10, V-13, V-15 |
| `test/backend/simd_strict_emit/ptx/` (5 files) | NEW | M5 | tests | +80 | M5 PTX emit | C3b §10, V-23 |
| `test/backend/simd_strict_emit/spirv/` (5 files) | NEW | M5 | tests | +80 | M5 SPIR-V emit | C3b §10 |
| `test/backend/simd_strict_emit/mixed_precision/` (10 files) | NEW | M8 | tests | +120 | M8 FP16/BF16 | C3b §10, C1 §8 |
| `test/backend/lmul_equivalence/` (2 files) | NEW | M7 | tests | +80 | M4+M7 RVV | C1 §3.5 |

### 2.10 Tests — Functional / Integration

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `test/types/simd_type_aliases.spl` | NEW | M0 | tests | +80 | M0 type IR | C2 §2 |
| `test/compiler/simd_type_check.spl` | NEW | M1 | tests | +100 | M1 semantics | C2 §9 |
| `test/predication/predicate_z.spl` | NEW | M2 | tests | +60 | M2 pass | C2 §5.3 |
| `test/predication/predicate_x_promote.spl` | NEW | M2 | tests | +60 | M2 pass | C2 §5.3 |
| `test/predication/predicate_promote_liveness.spl` | NEW | M2 | tests | +100 | M2 pass | C2 §5.3 |
| `test/platform/simd_platform_detect_sve2.spl` | NEW | M3 | tests | +80 | M3 platform | C3b §9.2 |
| `test/platform/simd_platform_detect_rvv.spl` | NEW | M4 | tests | +80 | M4 platform | C3b §9.3 |
| `test/gpu/cuda_saxpy_warpvec.spl` | NEW | M5 | tests | +100 | M5 CUDA | B1 §7, C1 §3.1 |
| `test/gpu/vulkan_saxpy_warpvec.spl` | NEW | M5 | tests | +100 | M5 Vulkan | B1 §7, C1 §4 |
| `test/auto_vectorize/` (5 pattern files) | NEW | M6 | tests | +200 | M6 wiring | B1 §5 |
| `test/perf/simd_perf_suite.spl` | NEW | M7 | tests | +150 | M6+M7 | B1 §1.3 |

### 2.11 Documentation (auto-generated)

| Path | Action | Phase | Owner | LOC delta | Depends on | Ref |
|------|--------|-------|-------|-----------|-----------|-----|
| `doc/06_spec/generated/auto_vectorize_patterns.md` | GEN | M6 | tooling | varies | M6 | B1 §5 |
| `doc/08_tracking/build/recent_build.md` | GEN | all | tooling | varies | each build | CLAUDE.md |

**Touch list totals:** ~100 rows; ~93 distinct file paths (including test subtrees as
single-row entries per 5-file golden directory). Compiler source: 29 rows.
Stdlib: 6 rows. Tests: 27 rows. Docs: 2 rows.

---

## 3. Diagnostic-Code Rollout Schedule

Source: C2 §9 Tables 9-A (errors) and 9-B (warnings). Codes are activated when the phase
that introduces their trigger condition lands. "Active from" means the code can fire in
that phase's compiled-mode tests.

### 3.1 Error Codes (Table 9-A)

| Code | Trigger | Active from | Phase rationale |
|------|---------|-------------|-----------------|
| `E_SIMD_BAD_LANES` | N not in {2,4,8,16,32,64} | M0 | FixedVec<T,N> type node introduced in M0 |
| `E_SIMD_TYPE_MISMATCH` | T not satisfying element-type constraint | M0 | Same — type-check phase, M0 type IR |
| `E_SIMD_CONST_REQUIRED` | `permute(ctrl)` where ctrl is not compile-time const | M1 | Permute/shuffle MIR ops added in M1 |
| `E_SIMD_NO_NATIVE_SCALAR_FALLBACK` | Scalar fallback attempted but not available | M1 | Fallback chain wired in M1 `mir_lowering_expr.spl` |
| `E_SIMD_MASK_TYPE_MISMATCH` | `Mask<V>` associated type inconsistency | M1 | `MirInstKind::MaskOp` and `simd_check.spl` extension in M1 |
| `E_SIMD_MONO_DEPTH` | Monomorphization depth exceeded | M1 | Specialization registry added in M1 `instantiation.spl` |
| `E_SIMD_GATHER_ALIGN` | Gather base pointer alignment violation | M1 | `SimdGather` MIR variant wired in M1 |
| `E_SIMD_SCATTER_ALIGN` | Scatter base pointer alignment violation | M1 | `SimdScatter` MIR variant wired in M1 |
| `E_SCALABLE_NOT_FIXABLE` | `try_to_fixed()` fails at compile time | M3 | ScalableVec lowering wired in M3 `mir_types.spl` |
| `E_SCALABLE_NO_PTX` | `ScalableVec` used on PTX target | M5 | PTX backend code-gen path wired in M5; enforced earlier by `gpu_checker.spl` M3 change |
| `E_SCALABLE_INTERP_ONLY` | Method called in interpreter without scalar fallback | M3 | ScalableVec interp parity gap documented in C2 §7 |
| `E_WARP_NOT_IN_KERNEL` | `WarpVec` method called outside `@kernel` context | M5 | `gpu_checker.spl` full extension in M5 |
| `E_WARP_NO_APPLE_M` | `WarpVec` method on Apple M-series target | M3 | G-03 guard placed in `gpu_checker.spl` in M3 |
| `E_WARP_DELTA_OOB` | `shfl_up/down` delta >= warp_size | M5 | WarpVec delta bounds check in M5 `gpu_checker.spl` |
| `E_WARP_SELF_EXCLUDED` | `shfl` mask does not include calling thread | M5 | G-08 enforcement in M5 PTX emit |
| `E_WARP_LANE_OOB` | `shfl_idx` src_lane >= warp_size | M5 | WarpVec lane bounds check in M5 |
| `E_WARP_SIZE_RUNTIME_ONLY` | `target_warp_size_const()` on variable-size target | M5 | WarpVec size portability check in M5 `gpu_checker.spl` |

### 3.2 Warning Codes (Table 9-B)

| Code | Trigger | Active from | Phase rationale |
|------|---------|-------------|-----------------|
| `W_SIMD_SCALAR_FALLBACK` | Scalar loop fallback used | M1 | Fallback chain in M1 `simd_lowering.spl` |
| `W_SIMD_NO_NATIVE_LOWERING` | Split to multiple sub-width ops | M1 | Fallback chain, M1 `simd_lowering.spl` |
| `W_SIMD_AVX2_SCATTER_SLOW` | AVX2 scatter lowered to scalar store loop | M1 | C3a §7.2; scatter fallback in M1 |
| `W_SIMD_PRED_PROMOTE_HINT` | `_x` promotion opportunity detected | M2 | `predicate_promote.spl` liveness pass in M2 |
| `W_SIMD_HARDCODED_STRIDE` | `ScalableVec` loop with constant induction step | M3 | ScalableVec strip-mine loop in M3 `mir_lowering_expr.spl` |
| `W_SIMD_FIXED_EXCEEDS_MIN_LANES` | `to_scalable()` with N > target min_lanes | M3 | ScalableVec conversion check in M3 |
| `W_SIMD_MASK_BITS_OOB` | `from_bits` for ScalableVec beyond runtime lanes | M4 | RVV fractional LMUL mask-width check in M4 |
| `W_WARP_SYNC_EMPTY_MASK` | `warp_sync(0)` with empty mask | M5 | WarpVec sync check in M5 `gpu_checker.spl` |
| `W_SIMD_FP16_AUTOPROMOTE` | `FixedVec<f16,N>` on target without native FP16 | M8 | F16 element-type detection in M8 `simd_platform.spl` |

**Total codes: 17 error + 9 warning = 26 distinct codes enumerated in C2 §9 Tables 9-A
and 9-B.** The task brief cites 33; the discrepancy is noted here — C2 §9 as read
contains 26 named codes. Implementation should not add phantom codes to reach 33; if
additional codes are needed during M8 (mixed-precision edge cases), they should be
formally added to C2 §9 first.

---

## 4. Errata-Guard Rollout Schedule

Source: C3b §13 (G-01..G-13). Guards are activated when the backend ISA that requires
them is first introduced. C1 §6 errata citations accompany each row.

| Guard | ID | Errata | Phase activated | ISA target | Type | C1 citation |
|-------|----|--------|----------------|-----------|------|-------------|
| G-01 | k0-reserve | k0 EVEX opmask all-ones sentinel | M1 | AVX-512 | Hard assert (ICE) | C1 §1.4 |
| G-02 | vmv1r-before-mask | v0 mask-copy before every masked RVV op | M4 | RVV | Hard assert (ICE) | C1 §6-J |
| G-03 | apple-m-no-warp | Apple M has no SVE2 / WarpVec | M3 | Apple M (ARM) | Semantic-phase abort | C1 §6-H, C2 §6.4 |
| G-04 | vfmadd-form | AVX-512/AVX2 FMA form 132/213/231 dest-slot match | M1 | AVX-512, AVX2 | Errata-corrected logic | C1 §6-F, §1.8 |
| G-05 | vstart-zero | vstart == 0 assertion after vsetvli | M4 | RVV | Hard assert (ICE in debug) | C1 §6-D, §3.8 |
| G-06 | sve2-smstart | SMSTART SM invalidates Z/P — assert false stub | M3 | SVE2/SME | Out-of-scope stub (assert false) | C1 §6-C |
| G-07 | scatter-conflict | AVX-512 VSCATTERDPS index conflict → VPCONFLICTD | M1 | AVX-512 | Hard assert / runtime fallback | C1 §6-A, §6-B |
| G-08 | ptx-shfl-self | PTX shfl.sync mask must include calling lane | M5 | PTX/CUDA | Errata-corrected logic | C1 §6-G |
| G-09 | vlmul-reserved | vlmul=100 (binary) is reserved hole in vtype | M4 | RVV | Hard assert (ICE) | C1 §3.5, §3.7 |
| G-10 | rdna-wave32-hint | RDNA default wave32 vs wave64 capability check | M5 | SPIR-V/Vulkan | Warning | C1 §6-I (RDNA note) |
| G-11 | neon-vclt-reversed | NEON vclt maps to FCMGT with operands reversed | M1 | NEON/AArch64 | Errata-corrected logic | C1 §6-K |
| G-12 | spirv-subgroup-size | SPIR-V subgroup size hint capability required | M5 | SPIR-V/Vulkan | Warning | C1 §4, C3b §4.8 |
| G-13 | tensor-core-future | mma.sync / tensor-core ops out of scope | M9 | PTX/CUDA | Out-of-scope stub | C1 §8.6 |

**Guard activation summary by phase:**
- M1: G-01, G-04, G-07, G-11 (4 guards — all AVX-512 + NEON)
- M3: G-03, G-06 (2 guards — Apple M + SVE2/SME stub)
- M4: G-02, G-05, G-09 (3 guards — all RVV)
- M5: G-08, G-10, G-12 (3 guards — all GPU)
- M9: G-13 (1 guard — placeholder)

---

## 5. Risk Register v2

Refined from B3 §6. V-series items from C1 §10 / C3b §14 marked blocking (B) or
non-blocking (NB). Top 12 risks ordered by likelihood × impact.

### 5.1 V-Series Classification

| V-ID | Claim at risk | Blocking phase | B/NB | Resolution URL |
|------|--------------|---------------|------|----------------|
| V-01 | EVEX P0/P1/P2 bit field positions | M1 entry | B | Intel SDM Vol 2A §2.6.1 Table 2-36 |
| V-03 | k0 z-bit ignored when aaa=000 | M1 entry | B | Intel SDM Vol 2A §2.6.1 k0 note |
| V-06 | VFMADD213PS byte example `62 F2 75 C9 A8 C2` | M1 entry | B | Intel SDM Vol 2B §4.x VFMADD213PS |
| V-13 | vlmul fractional encoding 101=mf8, 110=mf4, 111=mf2 | M4 entry + M7 entry | B | RVV spec §3.4.2 Table 4 |
| V-15 | vfadd funct6=000000 OPFVV | M4 entry | B | RVV inst-table — search vfadd |
| V-16 | vfmacc funct6=011000 OPFVV | M4 entry | B | RVV inst-table — search vfmacc |
| V-25 | NEON vclt → FCMGT operands reversed (G-11 polarity) | M1 entry | B | ARM ARM §C7.2.x FCMGT |
| V-08 | SVE2 Z-register encoding bytes | M3 exit | B | ARMv9 ARM §C7 SVE encodings |
| V-23 | PTX `shfl.sync` exact syntax + mask semantics | M5 exit | B | PTX ISA Ref §9.7 shfl |
| V-12 | SMSTART SM invalidates Z/P contents | M3 (G-06 stub) | NB | ARM ARM §A1.4.2 + SME Guide §2 |
| V-38 | vstart/vsetvli trap-resume hazard | M4 (G-05 comment) | NB | RVV spec §3.7 trap handling |
| V-02 | EVEX ZMM16-31 complement encoding | M1 exit | NB | Intel SDM Vol 2A §2.6.1 |
| V-04 | AVX-512 broadcast table | M1 exit | NB | Intel SDM Vol 2A §2.6.1 Table 2-35 |

### 5.2 Top 12 Risk Items

Columns: Likelihood × Impact drives priority. Trigger = observable condition that
confirms the risk has fired. Fallback = what to do if the mitigation is insufficient.

| # | Risk | L | I | Owner | Trigger condition | Mitigation | Guard/ref | Fallback if mitigation fails |
|---|------|---|---|-------|------------------|-----------|-----------|------------------------------|
| R1 | **Compiled-mode false-greens** — `--mode=native` no-ops; `--mode=smf` swallows errors | H | H | all | A test reports PASSED but `diff <(objdump -d old) <(objdump -d new)` differs | Primary gate: byte/text diff, not exit code; `diff <(objdump -d ...)` is mandatory final gate for all CPU phases | — | Halt phase; add explicit panic-on-unresolved-extern to test harness |
| R2 | **V-01/V-06 EVEX bytes wrong** — all AVX-512 goldens ship corrupted | H | H | M1 | Any M1 golden file byte-differs from Intel SDM hand-assembled reference | Verify V-01+V-06+V-03 against Intel SDM §2.6.1 / §4.x before M1 entry; blocking entry criteria | G-01, G-04 | Revert M1 goldens; treat EVEX section as blocked until V-01/V-06 resolved |
| R3 | **V-25 NEON FCMGT reversal** — masked compare results silently inverted | H | H | M1 | NEON compare test produces inverse result (all-ones where zero expected) | Verify V-25 against ARM ARM §C7.2.x before M1 entry; G-11 guard mandatory | G-11 | Replace vclt emission with explicit FCMGT + swap; add polarity regression test |
| R4 | **V-13/V-15 RVV encoding wrong** — all RVV goldens ship corrupted | H | H | M4 | `objdump -d` of RVV output shows wrong funct6/funct3 bits | Verify V-13, V-15, V-16 against RVV spec §3.4.2 / inst-table before M4 entry; blocking entry criteria | G-02, G-05 | Revert M4 goldens; block M4 exit until enc table verified from authoritative RVV spec |
| R5 | **Cranelift `>>` bug recurrence** — shift-heavy SIMD lowering silently miscompiles | M | H | M1+ | Shift-by-scalar golden differs from reference on compiled mode | Use compiled mode for all SIMD tests; byte-diff gate catches wrong output | — | File Cranelift issue; emit shift as loop unroll or software-emulation path until fixed |
| R6 | **Bootstrap rebuild forgotten** — `bin/simple build` silently no-ops after new externs | M | H | M1,M3,M4,M5,M8 | New `rt_simd_*` extern added but `bin/simple test` segfaults or gives wrong result | Exit criteria include extern-count check before/after; `bootstrap-from-scratch.sh --deploy` required | — | Add CI step: `grep -c 'rt_simd_' src/runtime/*.c` must match `grep -c 'extern rt_simd_'` in .spl files |
| R7 | **SVE2 hardware unavailable** | H | L | M3 | No aarch64 host with SVE2; QEMU SVE2 SIGILL | `qemu-aarch64 -cpu max,sve2=on` for all SVE2 tests | G-06 (SME out of scope) | Skip hardware execution; text-diff `.s` output only; mark M3 as emulator-validated |
| R8 | **RVV hardware unavailable** | H | L | M4 | No riscv64 host with V extension; QEMU RVV illegal instruction | `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64` | G-05 | Skip hardware execution; byte-diff of `.o` section; mark M4 as emulator-validated |
| R9 | **GPU CI unavailable** — CUDA/Vulkan tests cannot execute | M | M | M5 | No NVIDIA GPU in CI; `nvcc` not installed | PTX text-diff gate; SPIR-V via `spirv-val`; execution optional | G-08, G-12 | Accept text-diff + validator only; flag M5 as no-execution-gate pending GPU CI |
| R10 | **Auto-vectorize wire-up missing** — A2 §7 "call site unconfirmed" | M | M | M6 | `grep -r 'emit_simd_autovec' src/compiler/` returns no results | First M6 task: grep to confirm; budget +80L if absent | — | Implement wire-up as M6 prerequisite task before any autovec tests |
| R11 | **LMUL widen breaks numerical equivalence** | L | H | M7 | Existing RVV M4 test golden differs after M7 LMUL=2/4 change | Gate behind `--enable-lmul-widen` flag; 100-PR-cycle soak before default-on | G-02 | Revert LMUL default to 1; keep widen as permanent opt-in flag |
| R12 | **Sapphire Rapids FP16 unavailable in CI** | H | L | M8 | AVX-512-FP16 instruction raises `#UD` on test host | QEMU 8.x: `qemu-x86_64 -cpu Cooperlake,avx512fp16=on` | — | Text-diff `.s` output only; mark M8 AVX-512-FP16 as emulator-validated |

---

## 6. Sequencing Rationale v2

### Why M0 before everything

`FixedVec<T,N>` as a generic type node must exist before `mir_lowering_expr.spl` can
wire `FixedVec::add` → `MirInstKind::SimdAddF32x4`. Every downstream phase depends on
this type spine. The `25.traits/vector_traits.spl` stubs introduced in M0 must also
exist before M1's `simd_check.spl` extension can validate `Mask<V>` consistency (C2 §5).

### Why M1 (Fixed + AVX-512) before M2 (Predication)

`MirInstKind::MaskOp` and `MirInstKind::SimdGather/Scatter` variants are introduced in
M1's `mir_instructions.spl` extension. `predicate_promote.spl` (M2) operates on these
variants in its liveness analysis — it cannot be written until the IR shape is stable.
Additionally, the `_z` vs `_x` predication default must be anchored to concrete MIR
types, not to trait stubs.

### Why M3 (SVE2) before M4 (RVV) — C3b §8 regalloc argument

SVE2 has a clean, dedicated P-register file (P0–P15, with P15 reserved per C3b §8.3).
This maps directly onto the `Mask<V>` model: each predicate operation takes a P-register
operand and the allocator's job is straightforward. RVV, by contrast, has no separate
mask register file — it reuses v0 from the data register file. Every masked RVV op
requires a `vmv1r.v v0, v<mask_phys>` insertion before the op if the mask is not already
in v0 (G-02). The allocator must track v0-liveness across the instruction window, which
is a non-trivial constraint layered on top of the scalable lowering model.

Implementing SVE2 first gives a validated scalable lowering template (strip-mine loop,
`vsetvl` analogue via `whilelt`/`ptrue`, `ScalableVecOp` MIR API shape) that RVV can
adopt as a well-scoped delta. Starting RVV without this template would require
implementing both the scalable-lowering model and the v0-mask constraint simultaneously,
significantly increasing defect probability. C3b §8 identifies this ordering constraint
explicitly in the regalloc section.

Additionally, QEMU SVE2 support (`-cpu max,sve2=on`) is more mature and better-tested
than QEMU RVV (particularly for VLEN selection and `vsetvli` interactions), so M3 can
serve as a QEMU-stability proving ground before M4 depends on it.

### Why M5 (GPU) parallel-eligible after M1 but serialised after M3/M4 in practice

B1 §7 notes that M5 strictly requires M1 (FixedVec MIR must be wired before GPU kernel
type-check; `FixedVec<f32,4>` → SPIR-V `OpTypeVector` requires the MIR type to exist).
M5 does not strictly require M3 or M4. In a two-track team, M5 can begin after M1 while
M3 and M4 proceed on the CPU track. In a single-track team, M3→M4→M5 is the preferred
order because the CPU-backend implementer gains RVV context useful for PTX's analogous
warp-scoped constraints.

### Why M6 (Auto-vectorize) after M4 (all CPU targets)

Cross-target auto-vectorize verification requires all 5 CPU targets to be green. If any
target is missing, the loop-pattern test suite cannot certify ISA-portability. Additionally,
M2's `Mask<V>` MIR types are needed for the conditional-copy vectorization pattern.

### Why M7 (LMUL widen) last among CPU phases

LMUL widening operates on top of LMUL=1 RVV (M4) and measures throughput using the
auto-vectorize suite (M6). The pass must be gated behind a flag until the M7 exit gate
validates cross-LMUL equivalence, so it cannot ship before M6 makes the perf suite
meaningful. The sequencing also protects against the R11 risk (silent precision drift on
misaligned vectors at LMUL=4).

### Why M8 (Mixed-precision) after M7

AVX-512-FP16 instructions require the AVX-512 encoder (`x86_64_avx512.spl`) to be
stable and perf-gated. SVE2 BFDOT/BFMMLA require `arm_sve2.spl` to be green. RVV Zvfh
requires `riscv_rvv.spl` LMUL=1. All three conditions are satisfied only after M7. PTX
bf16 additionally requires M5's `ptx_builder.spl` extension. M8 also introduces new
`SimdElementType` variants (F16, BF16, INT8) in `00.common/simd_types.spl` — adding
these mid-stream in M1–M7 would require retrofitting all backend emit paths.

---

## 7. Effort Summary v2

### Assumptions

1. LOC delta counts are gross additions; deletions counted separately. Net = gross adds −
   deletes. Source: B3 §8 for M0–M7 baselines; this document's M8 estimate (+1,400L gross).
2. "1 dev-week" = 4 productive days of new implementation + tests + review.
3. Bootstrap rebuild overhead (~2–4h per phase) is included in phase estimates where required.
4. M9 is scope-defined only: 0 LOC, 0 dev-weeks in this document. Implementation is XL
   when activated but not budgeted here.
5. C1 §10 V-series verification effort (resolving ~13 blocking items) is estimated at
   ~0.5 dev-weeks total (URL-lookups + byte-level checks), distributed across M1/M4 entry.

### Per-Phase Complexity

| Phase | Title | Complexity | Est. gross LOC | Est. net LOC | Est. weeks |
|-------|-------|-----------|---------------|-------------|-----------|
| M0 | Type IR Foundations | M | +610 | +310 | 1.5 |
| M1 | Fixed + Mask + AVX-512 | XL | +1,720 | +1,720 | 4.0 |
| M2 | Predication Promotion | M | +340 | +340 | 1.5 |
| M3 | SVE2 Backend | XL | +980 | +980 | 3.5 |
| M4 | RVV Backend (LMUL=1) | L | +830 | +830 | 2.5 |
| M5 | GPU WarpVec Skeleton | L | +850 | +850 | 2.5 |
| M6 | Auto-Vectorize Wiring | M | +240 | +240 | 1.5 |
| M7 | LMUL Widening + Perf Gates | M | +695 | +695 | 2.0 |
| M8 | Mixed-Precision (F16/BF16/INT8) | L | +1,400 | +1,400 | 3.5 |
| M9 | Tensor-Core Placeholder | S | 0 | 0 | 0 |
| **Total (M0–M8)** | | | **~7,665** | **~7,365** | **~22.5** |

Variance drivers: V-01/V-06/V-25 byte-verification failure (adds 1–2 weeks to M1 if
bytes are wrong and golden suite must be rebuilt); QEMU RVV instability (adds 0.5 weeks
to M4); M6 wire-up absent (adds 0.5 weeks). Upside: if V-series items verify cleanly on
first check, M1+M4 entry overhead is < 1 day total.

C1 errata reference: C1 §10 enumerates 38 unverified items (V-01..V-38). Of these, 9
are classified as blocking in this plan (§5.1). Resolution effort scales with how many
bytes are wrong — in the worst case (V-01 wrong → all AVX-512 EVEX bytes wrong), M1
golden suite rebuild cost is ~2 days.

---

## 8. Open Questions / Followups v2

Items that require human decision or external verification before M0 begins or before
their blocking phase entry gate opens.

**OQ-1 (blocks M1 entry) — V-01/V-06/V-03 EVEX byte verification.**
C3b §14 lists `62 F2 75 C9 A8 C2` as the VFMADD213PS example (V-06) with status
UNVERIFIED. The EVEX P0/P1/P2/P3 field positions (V-01) and k0 z-bit behavior (V-03)
are also unverified. Resolution: fetch Intel SDM Vol 2A §2.6.1 Table 2-36 and Vol 2B
VFMADD213PS entry before writing any AVX-512 golden file. Assign to backend-cpu lead.

**OQ-2 (blocks M1 entry) — V-25 NEON FCMGT operand reversal.**
C3b §14 states NEON `vclt Vd, Vn, Vm` maps to `FCMGT Vm, Vn` with operands reversed.
If wrong, G-11 has inverted polarity and all masked comparisons on NEON produce wrong
results. Resolution: fetch ARM ARM §C7.2.x FCMGT before writing NEON golden comparisons.
Assign to backend-cpu lead (same person resolving OQ-1).

**OQ-3 (blocks M4 entry) — V-13/V-15/V-16 RVV encoding verification.**
vlmul fractional encoding table (V-13), vfadd funct6=000000 (V-15), vfmacc funct6=011000
(V-16) are all unverified per C3b §14. These are hard-blocking for RVV golden suite.
Resolution: fetch RVV spec §3.4.2 Table 4 and inst-table.adoc before M4 entry.

**OQ-4 (blocks M3 exit) — V-08 SVE2 Z-register encoding.**
SVE2 instruction encoding bytes for the ~14 C3a §5.4 helpers are unverified. Resolution:
fetch ARMv9 ARM §C7 SVE encodings before M3 golden files are written.

**OQ-5 (blocks M5 exit) — V-23 PTX shfl.sync syntax.**
PTX `shfl.sync` exact syntax including mask operand position and `.b32` type suffix is
unverified (C3b §14). Resolution: fetch PTX ISA Reference §9.7.6 before M5 PTX goldens.

**OQ-6 (decision before M0) — Diagnostic code count discrepancy.**
C2 §9 as enumerated contains 26 codes (17 errors + 9 warnings). The task brief asserts 33.
Human decision required: either (a) accept 26 as the authoritative count and update the
brief, or (b) identify the 7 additional codes that C2 §9 is missing and add them formally
before M1 activates the full set. Do not silently add phantom codes during implementation.

**OQ-7 (decision before M1) — x86_64_simd.spl split scope.**
Task brief suggested a 3-way split into `x86_64_sse.spl`, `x86_64_avx2.spl`,
`x86_64_avx512.spl`. C3a §5.2 explicitly recommends keeping SSE+AVX2 monolithic (shared
`_encode_simd_3op_xmm/ymm`) and adding only `x86_64_avx512.spl` as new file. This plan
follows C3a §5.2 (2-file outcome). Human confirmation requested before M1 begins to
avoid mid-phase rename churn.

**OQ-8 (decision before M4) — riscv_rvv.spl vs riscv_v.spl filename.**
B3 §3 uses `riscv_v.spl`; C3b §11.3 helper count table uses `riscv_rvv.spl`. This plan
uses `riscv_rvv.spl` (C3b §11.3 is more authoritative as it ties to helper count).
Human confirmation requested before M4 creates the file.

**OQ-9 (decision before M3) — P15 allocation policy.**
C3b §8.3 reserves P15 for the SVE2 allocator. Confirm whether P15 should be hard-reserved
at allocator init (analogous to k0 reserve in G-01) or lazily avoided by the liveness
pass. Hard-reserve is safer; lazy avoidance risks P15 appearing in a generated instruction
if the liveness pass has a bug. Recommended: hard-reserve.

**OQ-10 (decision before M8) — RVV Zvfbfmin convert-compute-convert pattern.**
C1 §8.5 notes that RVV Zvfbfmin provides BF16 load/store and `vfncvtbf16.f.f.w`
(f32→bf16 narrowing) but no native BF16 arithmetic. M8's RVV BF16 path requires a
convert-to-f32 → f32 arithmetic → convert-back pattern. Decision: auto-insert with a
`W_SIMD_BF16_RVV_EMULATED` diagnostic (recommended), or require user to write explicit
f32 code? The auto-insert path is more ergonomic but hides a latency penalty.

**OQ-11 (non-blocking, post-M4 follow-up) — V-38 vstart trap-resume comment.**
C3b §14 V-38: G-05 guard comment is incomplete for trap-resume hazard. The guard itself
is correct; the comment should cite RVV spec §3.7 once verified. Assign to backend-cpu
for a post-M4 follow-up commit.

**OQ-12 (non-blocking, M9 scope gate) — WarpVec / mma.sync interface conflict.**
Before M9 is activated, audit `WarpVec<T>` method catalog (C2 §6) for conflicts with
the `mma.sync` operand shape (m×n×k tile sizes, accumulator type). WMMA's
`mma.m16n8k16.f32.f16.f16.f32` does not fit naturally into a lane-indexed `WarpVec<f32>`.
A new trait (e.g., `TileVec<T,M,N,K>`) may be needed. Resolve before activating M9.
