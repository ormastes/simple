<!-- claude-design -->
# Design: SIMD Rollout Plan (Phases M0–M7)

This document synthesizes Wave A1 (ISA survey), A2 (internal state gap map), B1 (unified architecture), and B2 (backend strict-emit op tables) into an executable 8-phase rollout for full SIMD support in the Simple compiler. The plan covers FixedVec/ScalableVec/WarpVec type system landing, Mask/predication, CPU backend extensions (AVX-512, SVE2, RVV), GPU WarpVec skeleton (CUDA/Vulkan), auto-vectorization wiring, and LMUL-widening perf gates. All gating tests run in compiled mode using strict-emit byte-exact or text-exact goldens as the primary verification mechanism, not exit-code-only pass/fail.

---

## 1. Goals & Exit Criteria

"SIMD support shipped" is defined by the following observable criteria — not by code-written milestones.

### 1.1 Performance

Peak FMA throughput is defined as the ISA-theoretical maximum: e.g., AVX-512 on Skylake-SP = 2 × 16 FMAs/cycle × clockspeed; NEON A72 = 2 × 4 FMAs/cycle. The reference machine for each target is fixed once at the start of M7 (using M4 completion as the baseline measurement point). Measurement tool: `perf stat -e cycles,fp_arith_inst_retired.256b_packed_single` (x86) or `perf stat -e armv8_pmuv3/fp_scale_ops_spec/` (AArch64); QEMU cycle counts are an approximation only — flag if QEMU yields < 50% of theoretical (emulation overhead expected).

| Target | Kernel | Criterion | Reference machine |
|--------|--------|-----------|------------------|
| NEON (AArch64) | SAXPY f32x4 | ≥ 95% of peak FMA throughput (`perf stat` cycles/element) | Neoverse N1 (or Apple M-series) |
| AVX2 (x86-64) | SAXPY f32x8 | ≥ 95% of peak FMA throughput | Skylake or later |
| AVX-512 (x86-64) | SAXPY f32x16 | ≥ 95% of peak FMA throughput | Icelake-SP or later; use QEMU `-cpu Icelake-Server` if no hardware |
| SVE2 (AArch64) | SAXPY scalable f32 | ≥ 95% of theoretical (QEMU cycle model) | `qemu-aarch64 -cpu max,sve2=on` |
| RVV 1.0 (RISC-V) | SAXPY scalable f32 | ≥ 95% of theoretical (QEMU cycle model) | `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64` |
| PTX / CUDA | SAXPY f32 warp-tile | Kernel launches and produces correct output; SM_70+ | Any CUDA 11+ SM_70 GPU |

### 1.2 Correctness

- **35 strict-emit golden files** (5 kernels × 7 CPU targets + 2 GPU targets; see §4.1) all match byte-for-byte (CPU) or text-for-text (PTX/SPIR-V).
- **Cross-target equivalence**: the 5 kernels compiled to all 7 CPU targets produce identical numerical output for the same inputs (verified via host run + QEMU for non-host targets).
- **Predication semantics**: `_z` (zero-fill) test passes with `predicate_promote` OFF; `_x` (undef) promotion test passes with pass ON. Both verified in compiled mode.
- **LMUL invariance**: RVV at LMUL=1 and LMUL=2/4 produce identical output for SAXPY and dot kernels.

### 1.3 Doc Coverage

- User-facing SIMD library at `src/lib/nogc_sync_mut/simd/` achieves ≥ 80% doc coverage per `bin/simple doc-coverage`.

### 1.4 Auto-Vectorization

The compiler auto-vectorizes the following 5 loop patterns on at least one CPU target without explicit `FixedVec` calls:

1. **Elementwise saxpy**: `y[i] += alpha * x[i]` (contiguous, no alias)
2. **Dot product accumulation**: `acc += x[i] * y[i]` (reduction, no cross-iter dep)
3. **Type-cast copy**: `dst[i] = f32(src[i])` (i32 → f32 lane conversion)
4. **Conditional copy**: `if cond[i]: dst[i] = src[i]` (mask-select pattern)
5. **Scalar broadcast multiply**: `y[i] = x[i] * k` (splat + mul, k is loop-invariant)

Trigger confirmed by: emitted MIR contains `SimdAddF32x*` / `SimdMulF32x*` instructions (verified by `bin/simple desugar` output inspection in compiled mode).

---

## 2. Phase Breakdown

### Phase Summary

| Phase | Title | Complexity | Bootstrap Rebuild | Primary Owner | New Files | Gating Test |
|-------|-------|-----------|------------------|---------------|-----------|-------------|
| M0 | Type IR Foundations | M | No | compiler-frontend | `25.traits/vector_traits.spl` + 6 stdlib files | `desugar` shows `Vec4f→FixedVec<f32,4>` |
| M1 | FixedVec End-to-End + All Fixed-Width Backends | XL | **Yes** | backend-cpu | `x86_64_avx512.spl` + 20 goldens | 20 golden diffs byte-exact |
| M2 | First-Class Mask + Predication | L | No | mir-opt | `predicate_promote.spl` + 2 semantics tests | `_z`/`_x` predication semantics tests |
| M3 | ScalableVec + SVE2 | XL | **Yes** | backend-cpu | `arm_sve2.spl` + 5 SVE2 goldens | 5 SVE2 golden diffs under QEMU |
| M4 | ScalableVec + RVV 1.0 | L | **Yes** | backend-cpu | `riscv_rvv.spl` + 5 RVV goldens | 5 RVV golden diffs under QEMU+spike |
| M5 | GPU WarpVec Skeleton | L | **Yes** | backend-gpu | 5 PTX goldens + 2 GPU e2e tests | PTX golden diff + CUDA e2e run |
| M6 | Auto-Vectorization Wiring | M | No | mir-opt | 5 av_*.spl tests | `desugar` shows `SimdXxx` MIR in 5 patterns |
| M7 | LMUL Widening + Perf Gates | M | No | mir-opt | `lmul_widen.spl` + perf suite | LMUL equivalence + 95% throughput |

### M0: Type IR Foundations
**Purpose**: Replace the 19-line stub `00.common/simd_types.spl` with a complete SIMD type IR; define `Vector`/`Mask`/`WarpVec` trait stubs in `25.traits/`; deprecate the 5 hardcoded scalar structs in `simd_vector_types.spl` by replacing them with `FixedVec<T,N>` + back-compat aliases. This phase establishes the type-system spine that every downstream phase depends on.

- **Inputs**: None (greenfield on stubs; existing `simd_vector_types.spl:57,323,440`, `00.common/simd_types.spl:1–19`)
- **Outputs** (per B1 §2, §3.2, §8.2–8.3):
  - `src/compiler/00.common/simd_types.spl` — full type IR enums/structs (MODIFY, ~+250 lines)
  - `src/compiler/25.traits/vector_traits.spl` — `Vector`, `Mask`, `WarpVec` trait definitions (NEW, ~150 lines)
  - `src/compiler/30.types/simd_vector_types.spl` — replace scalar structs with `FixedVec<T,N>`, `FixedMask<N>`, `ScalableVec<T>`, `ScalableMask`; retain `Vec2f/Vec4f/...` aliases (MODIFY: ~500→200 lines net, -300)
  - `src/lib/nogc_sync_mut/simd/` — new directory with 6 files (NEW, ~400 lines total): `__init__.spl`, `fixed_vec.spl`, `scalable_vec.spl`, `warp_vec.spl`, `platform.spl`, `compat.spl`
- **Bootstrap rebuild required**: NO (M0 adds no new `rt_simd_*` externs)
- **Owner workstream**: compiler-frontend, stdlib
- **Verification gate** (run in order; all must pass before M1 begins):
  ```
  # 1. Type-check
  bin/simple build
  # 2. Vec4f alias resolves correctly
  bin/simple desugar src/compiler/30.types/simd_vector_types.spl | grep 'Vec4f.*FixedVec'
  # 3. Compiled-mode type test
  bin/simple test --mode=native test/types/simd_fixedvec_types.spl
  # 4. Confirm no accidental .x/.y migration in geometry code
  grep -r '\.x\b\|\.y\b\|\.z\b\|\.w\b' --include='*.spl' \
    src/lib/nogc_sync_mut/engine/render/vector.spl \
    src/lib/common/linear_algebra/vector_ops.spl | wc -l  # must be > 0 (geometry fields retained)
  ```
- **Estimated complexity**: M
- **Risks**: `Vec2f/Vec4f` field access (`v.x`, `v.y`) must be migrated to `extract(N)` at every call site in the compiler itself — A2 §1b notes 5 hardcoded structs with positional fields. Geometry code in `engine/render/vector.spl` and `linear_algebra/vector_ops.spl` must NOT be migrated (different positional semantics, per B1 §8.2). Scope migration: `grep -r '\.x\b\|\.y\b' --include='*.spl' src/compiler/ | grep -i 'vec4f\|vec2f'` before M0 to count call sites. Risk of inadvertent breakage if a refactor script is too broad.

---

### M1: Common Vector Trait + FixedVec End-to-End (CPU, Existing Backends)
**Purpose**: Type-check `FixedVec<T,N>` end-to-end through the compiler pipeline; wire `FixedVec::method` calls to `SimdXxx` MIR instructions; retarget existing NEON and SSE/AVX2 emit through the new trait; land AVX-512 strict-emit.

- **Inputs**: M0 outputs
- **Outputs** (per B1 §3.2, B2 §5.2, A2 §2 `:116`, A2 §7):
  - `src/compiler/35.semantics/simd_check.spl` — extend to validate `FixedVec<T,N>` type-check, monomorphization bounds (MODIFY, ~+120 lines)
  - `src/compiler/40.mono/` — add `FixedVec<T,N>` specialization registry (likely modify `instantiation.spl`, ~+80 lines)
  - `src/compiler/50.mir/mir_types.spl` — add `MaskOp`, `SimdGather`, `SimdScatter`, `SimdPermute`, `SimdShuffle` instruction variants (MODIFY, ~+60 lines)
  - `src/compiler/50.mir/mir_instructions.spl` — add gather/scatter/permute/shuffle/mask instruction variants (MODIFY, ~+80 lines)
  - `src/compiler/50.mir/mir_lowering_expr.spl` — wire `FixedVec::method` → `SimdXxx` MIR; A2 §2 notes `:116` currently does scalar dispatch (MODIFY, ~+200 lines)
  - `src/compiler/60.mir_opt/mir_opt/simd_lowering.spl` — add names for gather/scatter/permute/mask ops per B1 §3.2 (MODIFY, ~+60 lines)
  - `src/compiler/70.backend/backend/native/arm_neon.spl` — retarget to flow through Vector trait; extend BSL mask-blend for `FixedMask<N>` per B2 §4.1 (MODIFY, ~+80 lines)
  - `src/compiler/70.backend/backend/native/x86_64_simd.spl` — retarget SSE/AVX2 through Vector trait; add gather/blend helper encoders per B2 §5.2 (MODIFY, ~+120 lines)
  - `src/compiler/70.backend/backend/native/x86_64_avx512.spl` — AVX-512 EVEX encoder: ZMM regs, k0 reserved as all-ones per B2 finding 4, sub-feature dispatch BW/DQ/VL/VBMI per A1 §1.4 (NEW, ~500 lines)
  - `src/compiler/70.backend/portable_numeric_capabilities.spl` — add NEON/SVE/AVX-512 fields per A2 §6 (MODIFY, ~+60 lines)
  - `test/backend/simd_strict_emit/neon/` — 5 golden files (NEW)
  - `test/backend/simd_strict_emit/sse/` — 5 golden files (NEW)
  - `test/backend/simd_strict_emit/avx2/` — 5 golden files (NEW)
  - `test/backend/simd_strict_emit/avx512/` — 5 golden files (NEW)
- **Bootstrap rebuild required**: YES — M1 wires new `rt_simd_*` names into MIR lowering. After any new extern addition: `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (NOT `bin/simple build bootstrap` — the latter silently no-ops per `feedback_extern_bootstrap_rebuild`).
- **Owner workstream**: compiler-frontend, mir-opt, backend-cpu, tests
- **Verification gate** (run in order; all must pass before M2 begins):
  ```
  # 1. Bootstrap rebuild
  scripts/bootstrap/bootstrap-from-scratch.sh --deploy
  # 2. Compile each kernel for NEON, SSE, AVX2
  bin/simple build --target=aarch64-neon   test/backend/simd_strict_emit/neon/saxpy_kernel.spl -o /tmp/saxpy_neon.o
  bin/simple build --target=x86_64-sse4    test/backend/simd_strict_emit/sse/saxpy_kernel.spl  -o /tmp/saxpy_sse.o
  bin/simple build --target=x86_64-avx2   test/backend/simd_strict_emit/avx2/saxpy_kernel.spl -o /tmp/saxpy_avx2.o
  bin/simple build --target=x86_64-avx512 test/backend/simd_strict_emit/avx512/saxpy_kernel.spl -o /tmp/saxpy_avx512.o
  # 3. Strict-emit golden diff (byte-exact; NOT exit-code-only)
  for target in neon sse avx2 avx512; do
    for kernel in saxpy dot hcompare gather_add masked_store; do
      diff <(objdump -d /tmp/${kernel}_${target}.o | grep -oP '\t[0-9a-f ]+\t') \
           test/backend/simd_strict_emit/${target}/${kernel}.golden
    done
  done
  # 4. Cross-target equivalence (host)
  bin/simple test --mode=native test/backend/simd_equivalence/saxpy_cross_target.spl
  # 5. AVX-512 on QEMU if no hardware
  qemu-system-x86_64 -cpu Icelake-Server -nographic -kernel /tmp/saxpy_avx512 2>&1 | grep 'PASS'
  ```
- **Estimated complexity**: XL
- **Risks**: AVX-512 EVEX encoding is qualitatively more complex than VEX (4-byte prefix, embedded k-mask); any bit error is silent on non-AVX-512 hardware (test on QEMU `-cpu Icelake-Server`). k0 reserved (B2 finding 4) must be enforced in the allocator — a missed `k0` alloc produces incorrect masked ops silently.

---

### M2: First-Class Mask + Predication
**Purpose**: Lower `Mask<V>` as a first-class MIR type; wire `_z` (zero-fill) as the default predication mode; add `predicate_promote.spl` liveness pass for `_z` → `_x` promotion; complete AVX-512 k-register allocation end-to-end.

- **Inputs**: M1 outputs
- **Outputs** (per B1 §2.2, §2.3, §3.2, A1 §5):
  - `src/compiler/50.mir/mir_types.spl` — add `MirType.Mask(N)` variant; distinguish `FixedMask<N>` from `ScalableMask` (MODIFY, ~+40 lines)
  - `src/compiler/50.mir/mir_lowering_expr.spl` — lower `Mask<V>` construction and boolean ops to `MirInstKind::MaskOp` (MODIFY, ~+80 lines)
  - `src/compiler/60.mir_opt/mir_opt/predicate_promote.spl` — liveness pass: `_z` → `_x` when inactive lane values proven dead per B1 §3.2 (NEW, ~200 lines)
  - `src/compiler/70.backend/backend/native/x86_64_avx512.spl` — k-reg allocation: k0 reserved all-ones; k1–k7 allocatable; boolean ops lower to `_kand_mask16` / `_kor_mask16` per A1 §5 (MODIFY, ~+100 lines)
  - `src/compiler/70.backend/backend/native/arm_neon.spl` — NEON masked ops cost one extra reg + BSL per B2 finding 2; implement `FixedMask<N>` via BSL (MODIFY, ~+60 lines)
  - `test/backend/simd_strict_emit/avx512/` — update goldens with k-reg masked variants (MODIFY)
  - `test/semantics/simd_predication/` — `_z` default semantics test; `_x` promotion test (NEW, ~100 lines)
- **Bootstrap rebuild required**: NO (M2 adds no new externs; only MIR pass logic changes)
- **Owner workstream**: compiler-frontend, mir-opt, backend-cpu, tests
- **Verification gate** (run in order):
  ```
  # 1. _z default — predicate_promote pass disabled
  SIMPLE_NO_PREDPROMOTE=1 bin/simple build --target=x86_64-avx512 \
    test/semantics/simd_predication/predz_default.spl -o /tmp/predz_test
  /tmp/predz_test  # inactive lanes must be 0.0
  # 2. _x promotion — pass enabled
  bin/simple build --target=x86_64-avx512 \
    test/semantics/simd_predication/predx_promote.spl -o /tmp/predx_test
  /tmp/predx_test  # must emit _x form (check objdump: no vzeroupper zeroing)
  # 3. AVX-512 hcompare + masked_store golden diff
  diff <(objdump -d /tmp/hcompare_avx512.o | grep -oP '\t[0-9a-f ]+\t') \
       test/backend/simd_strict_emit/avx512/hcompare.golden
  diff <(objdump -d /tmp/masked_store_avx512.o | grep -oP '\t[0-9a-f ]+\t') \
       test/backend/simd_strict_emit/avx512/masked_store.golden
  ```
- **Estimated complexity**: L
- **Risks**: A1 §5 notes that `_m` (merge-predication) must only be generated when an explicit merge-source is tracked in IR — accidentally emitting `_m` instead of `_z` is a latent miscompile. Strict-emit goldens catch this only if the golden was written correctly; validate goldens against manual LLVM IR reference output.

---

### M3: ScalableVec + SVE2 Backend
**Purpose**: Introduce `ScalableVec<T>` lowering end-to-end; implement `arm_sve2.spl` strict-emit with Z/P register model; add SVE2 capability detection via `mrs ID_AA64ZFR0_EL1` per A1 §2.1.

- **Inputs**: M2 outputs
- **Outputs** (per B1 §2.4, B2 §4.5, A1 §2.1, A2 §7):
  - `src/compiler/50.mir/mir_types.spl` — wire `ScalableVec<T>` lowering (currently stub at `:170`); add `ScalableMask` MIR type (MODIFY, ~+60 lines)
  - `src/compiler/50.mir/mir_lowering_expr.spl` — `ScalableVec::method` → `MirInstKind::ScalableVecOp` lowering; `vsetvl` strip-mine loop emission (MODIFY, ~+120 lines)
  - `src/compiler/30.types/simd_platform.spl` — add SVE2 capability detection using `mrs ID_AA64ZFR0_EL1`; rename `SimdCapabilities` → `SimdFeatureFlags` bitmask per B1 §6 (MODIFY, ~+80 lines)
  - `src/compiler/70.backend/backend/native/arm_sve2.spl` — SVE2 Z/P register model; `_z` default; `svptrue_b32` loop prolog; gather (`ld1_gather`) / scatter (`st1_scatter`) per A1 §2.1; `svand_b_z` / `sveor_b_z` mask bool ops (NEW, ~600 lines)
  - `test/backend/simd_strict_emit/sve2/` — 5 golden files (NEW)
  - `test/platform/simd_platform_detect.spl` — SVE2 capability detection test under QEMU (NEW, ~80 lines)
- **Bootstrap rebuild required**: YES — `arm_sve2.spl` adds new backend code paths wired from MIR; run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` after landing `arm_sve2.spl`.
- **Owner workstream**: backend-cpu, compiler-frontend, tests
- **Verification gate** (run in order):
  ```
  # 1. Bootstrap rebuild
  scripts/bootstrap/bootstrap-from-scratch.sh --deploy
  # 2. Compile SVE2 kernels
  bin/simple build --target=aarch64-sve2 test/backend/simd_strict_emit/sve2/saxpy_kernel.spl \
    -o /tmp/saxpy_sve2.o
  # 3. Golden diff (text-based disassembly; use aarch64-linux-gnu-objdump)
  for kernel in saxpy dot hcompare gather_add masked_store; do
    diff <(aarch64-linux-gnu-objdump -d /tmp/${kernel}_sve2.o | grep -E 'ld1|st1|fadd|fmla|svptrue|pnext') \
         test/backend/simd_strict_emit/sve2/${kernel}.golden
  done
  # 4. Execute under QEMU (SVE2 capability detection + correctness)
  qemu-aarch64 -cpu max,sve2=on /tmp/saxpy_sve2 x=[1,2,3,4] y=[0,0,0,0] alpha=2.0
  # 5. Cross-target SAXPY equivalence
  bin/simple test --mode=native test/backend/simd_equivalence/saxpy_sve2_vs_neon.spl
  # 6. NEON regression: confirm existing NEON goldens still pass
  diff <(objdump -d /tmp/saxpy_neon.o | grep -oP '\t[0-9a-f ]+\t') \
       test/backend/simd_strict_emit/neon/saxpy.golden
  ```
- **Estimated complexity**: XL
- **Risks**: SVE2 vsetvl-style strip-mining requires backend loop restructuring that touches `mir_lowering_expr.spl` heavily — risk of regression in existing NEON path (verify NEON goldens explicitly, step 6 above). A1 §2.3 notes SVE2 has 3 predication modes (`_x`, `_z`, `_m`); `_m` must remain unimplemented until explicitly requested. Test hardware is QEMU only; physical Neoverse N2 CI is out of scope for this phase.

---

### M4: ScalableVec + RVV 1.0 Backend
**Purpose**: Implement `riscv_rvv.spl` strict-emit with `vsetvli`, v0 mask copy convention, `csrr vlenb` capability detection; LMUL stays at 1 for this phase.

- **Inputs**: M3 outputs (SVE2 template used as reference for scalable emit pattern)
- **Outputs** (per B2 §4.6, A1 §2.2, B1 §2.4):
  - `src/compiler/30.types/simd_platform.spl` — add RVV capability detection using `csrr vlenb` per A1 §2.2; add `has_riscv_v` flag wiring (currently exists as dead field, A2 §6) (MODIFY, ~+50 lines)
  - `src/compiler/70.backend/backend/native/riscv_rvv.spl` — `vsetvli t0, a0, e32, m1, ta, ma` at loop prolog; v0 mask: allocate mask to any vX, emit `vmv1r.v v0, vX` before each masked op per B2 finding 3; `vluxei` gather / `vsuxei` scatter per A1 §2.2 (NEW, ~550 lines)
  - `test/backend/simd_strict_emit/rvv/` — 5 golden files (NEW)
  - `test/platform/riscv_capability_detect.spl` — `csrr vlenb` capability detection test (NEW, ~60 lines)
- **Bootstrap rebuild required**: YES — `riscv_rvv.spl` is a new backend file; run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` after landing it.
- **Owner workstream**: backend-cpu, tests
- **Verification gate** (run in order):
  ```
  # 1. Bootstrap rebuild
  scripts/bootstrap/bootstrap-from-scratch.sh --deploy
  # 2. Compile RVV kernels
  bin/simple build --target=riscv64-rvv test/backend/simd_strict_emit/rvv/saxpy_kernel.spl \
    -o /tmp/saxpy_rvv
  # 3. Golden diff (text disassembly; check vsetvli + vmv1r convention)
  for kernel in saxpy dot hcompare gather_add masked_store; do
    diff <(riscv64-linux-gnu-objdump -d /tmp/${kernel}_rvv | grep -E 'vsetvli|vmv1r|vadd|vfmacc|vluxei|vsuxei') \
         test/backend/simd_strict_emit/rvv/${kernel}.golden
  done
  # 4. Execute under QEMU (LMUL=1)
  qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64 -nographic \
    -kernel /tmp/saxpy_rvv 2>&1 | grep 'PASS'
  # 5. Cross-target equivalence
  bin/simple test --mode=native test/backend/simd_equivalence/saxpy_rvv_vs_sve2.spl
  # 6. Spike secondary gate (LMUL alignment)
  spike --isa=rv64gcv /tmp/hcompare_rvv 2>&1 | grep -v 'illegal instruction'
  ```
- **Estimated complexity**: L
- **Risks**: v0 mask copy convention (`vmv1r.v v0, vX` before every masked op, B2 finding 3) adds register pressure. Any LMUL-grouped instruction accidentally using odd-aligned registers will generate illegal-instruction traps at runtime, not compile errors — require strict-emit golden testing on spike simulator (step 6 above) as secondary gate.

---

### M5: GPU WarpVec Skeleton (CUDA + Vulkan Compute)
**Purpose**: Extend `gpu_intrinsics.spl` with `WarpVec` warp-scoped ops; add PTX `.v4` packed loads and `shfl.sync` / `vote.sync` warp ops; add SPIR-V subgroup ops for Vulkan compute. End-to-end: one CUDA SAXPY kernel and one Vulkan compute SAXPY shader compile and execute.

- **Inputs**: M1 outputs (FixedVec MIR must be wired before GPU kernel type-check; see §7 for parallel-eligible note)
- **Outputs** (per B1 §7, A1 §3):
  - `src/compiler/70.backend/gpu_intrinsics.spl` — add `WarpVec<T>` ops: `shfl_up`, `shfl_down`, `shfl_bfly`, `shfl_idx`, `warp_reduce_sum`, `warp_ballot` per B1 §2.6 (MODIFY, ~+120 lines)
  - `src/compiler/35.semantics/gpu_checker.spl` — extend to enforce "WarpVec only in kernel context" per B1 §2.6 (MODIFY, ~+60 lines)
  - `src/compiler/70.backend/backend/cuda/ptx_builder.spl` — add `.v4.f32` packed load/store per A1 §3.1; `shfl.sync.up.b32`, `shfl.sync.down.b32`, `shfl.sync.bfly.b32`, `shfl.sync.idx.b32` per A1 §3.1; `vote.sync.ballot.b32` per A1 §3.1 (MODIFY, ~+150 lines)
  - `src/compiler/70.backend/backend/vulkan/spirv_builder.spl` — add `OpTypeVector float32 4`; `OpGroupNonUniformShuffle`; `OpGroupNonUniformFAdd` (subgroup reduce); `OpGroupNonUniformBallot` per B1 §7.3 (MODIFY, ~+120 lines)
  - `test/backend/simd_strict_emit/ptx/` — 5 golden files (PTX text) (NEW)
  - `test/gpu/cuda_saxpy_warpvec.spl` — end-to-end CUDA SAXPY; executed via `nvcc --ptx` + CUDA driver API (NEW, ~100 lines)
  - `test/gpu/vulkan_saxpy_compute.spl` — end-to-end Vulkan compute SAXPY; executed via Vulkan loader (NEW, ~120 lines)
- **Bootstrap rebuild required**: YES — new `shfl.sync` / `vote.sync` PTX lowering paths added to `ptx_builder.spl`; run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`.
- **Owner workstream**: backend-gpu, tests
- **Verification gate** (run in order):
  ```
  # 1. Bootstrap rebuild
  scripts/bootstrap/bootstrap-from-scratch.sh --deploy
  # 2. PTX golden diff (CUDA SDK major must be pinned in golden header comment)
  export CUDA_MAJOR=$(nvcc --version | grep -oP 'release \K[0-9]+')
  for kernel in saxpy dot hcompare gather_add masked_store; do
    diff <(bin/simple build --target=ptx-sm70 test/backend/simd_strict_emit/ptx/${kernel}_kernel.spl \
           --emit=ptx 2>/dev/null) \
         test/backend/simd_strict_emit/ptx/${kernel}.golden
  done
  # 3. End-to-end CUDA execution (requires SM_70+ GPU or CUDA simulator)
  bin/simple build --target=ptx-sm70 test/gpu/cuda_saxpy_warpvec.spl -o /tmp/cuda_saxpy
  /tmp/cuda_saxpy  # verifies output vs CPU reference
  # 4. Vulkan compute (requires Vulkan 1.2+ with VK_KHR_shader_subgroup)
  bin/simple build --target=spirv-vulkan test/gpu/vulkan_saxpy_compute.spl -o /tmp/vk_saxpy.spv
  # Run via vulkaninfo to verify subgroup support, then execute
  /tmp/vulkan_saxpy_runner /tmp/vk_saxpy.spv | grep 'PASS'
  ```
- **Estimated complexity**: L
- **Risks**: PTX/SAS output varies between CUDA SDK major versions; goldens store SDK major in header (`# cuda-sdk: 12`); test runner checks `nvcc --version` before golden comparison and fails if mismatch. A1 §3.1 notes tensor cores (`mma.sync`) are explicitly OUT of scope for this phase; risk of scope creep if warp intrinsics are mistakenly extended to tensor ops.

#### GPU Skeleton Scope

**IN scope for M5:**
- `WarpVec<T>` shuffles (`shfl_up/down/bfly/idx`)
- `warp_reduce_sum`, `warp_ballot`
- PTX `.v4` packed load/store
- SPIR-V `OpTypeVector`, subgroup shuffle/reduce/ballot
- One end-to-end CUDA matmul-tile kernel (SAXPY; tiled matmul is M7+ stretch)
- One end-to-end Vulkan compute shader (SAXPY)

**OUT of scope for M5 (deferred):**
- Tensor cores (`mma.sync`, `wmma`)
- CUDA dynamic parallelism
- ROCm / HIP backend
- Metal / MSL backend
- WGSL backend
- Vulkan ray query
- Sparsity tensor cores
- PTX SASS-level optimization (structured barriers, mbarrier)

---

### M6: Auto-Vectorization Wiring
**Purpose**: Verify and wire the latent `auto_vectorize_codegen.spl` into the MIR opt pass driver sequence; confirm 5 named loop patterns auto-vectorize on at least one CPU target; verify on all 5 CPU targets.

- **Inputs**: M2 outputs (Mask lowering must be complete before conditional-copy pattern works); M1 outputs (SimdXxx MIR variants must exist)
- **Outputs** (per B1 §5, A2 §7):
  - `src/compiler/60.mir_opt/mir_opt/` (MIR opt driver pass file, name TBD by verification) — add `auto_vectorize_codegen.spl` call site in pass sequence per A2 §7 "wire-up gap" finding. **First task of M6 is to confirm whether call site is present (A2 §7: unconfirmed).**
  - `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` — potential minor changes to emit correct MIR variant names after M0–M1 renames (MODIFY if needed, ~+20 lines)
  - `test/auto_vectorize/` — 5 loop pattern tests confirming `SimdXxx` MIR emission (NEW, ~200 lines)
  - `doc/06_spec/generated/auto_vectorize_patterns.md` — auto-generated doc of 5 patterns (generated, not manually written)
- **Bootstrap rebuild required**: NO (M6 adds no new externs; only pass wiring in existing files)
- **Owner workstream**: mir-opt, tests
- **Verification gate** (run in order):
  ```
  # 0. First, verify wire-up status (A2 §7: "call site unconfirmed")
  grep -r 'auto_vectorize_codegen\|auto_vectorize' --include='*.spl' \
    src/compiler/60.mir_opt/ | grep -v '^.*auto_vectorize_codegen.spl'
  # If the above returns nothing → wire-up IS missing; add call site.
  # If it returns a call site → confirm it is in the pass driver sequence.

  # 1. Build with auto-vectorize enabled
  bin/simple build --target=x86_64-avx2 test/auto_vectorize/av_saxpy.spl -o /tmp/av_saxpy
  # 2. Confirm SimdXxx MIR was emitted
  bin/simple desugar --target=x86_64-avx2 test/auto_vectorize/av_saxpy.spl \
    | grep -E 'SimdAddF32|SimdMulF32|SimdFmaF32'
  # 3. Run all 5 pattern tests in compiled mode
  for test in av_saxpy av_dot av_cast_copy av_cond_copy av_broadcast_mul; do
    bin/simple test --mode=native test/auto_vectorize/${test}.spl
  done
  # 4. Verify on all CPU targets (QEMU for non-host)
  for target in aarch64-neon x86_64-avx2 x86_64-avx512 aarch64-sve2 riscv64-rvv; do
    bin/simple build --target=${target} test/auto_vectorize/av_saxpy.spl -o /tmp/av_saxpy_${target}
  done
  ```
- **Estimated complexity**: M
- **Risks**: `auto_vectorize_codegen.spl:316` already emits real `SimdXxx` MIR (A2 §7) — the main risk is that the wire-up gap is larger than anticipated (pass ordering dependencies, cost model not firing, or MIR variant name mismatch post-M1 renames). The complexity estimate is M (not L) because of the unconfirmed call site — if wiring is trivial (one line), complexity drops to S; if ordering requires pass restructuring, it rises to L.

---

### M7: LMUL Widening + Perf Gates
**Purpose**: Implement `lmul_widen.spl` pass to promote LMUL=1 → LMUL=2/4 on hot RVV loops behind a flag; run perf regression suite; gate ship on SAXPY peak throughput on all 6 CPU targets.

- **Inputs**: M4 outputs (RVV LMUL=1 must be stable); M6 outputs (auto-vectorize must be green before perf gates mean anything)
- **Outputs** (per B1 §3.2):
  - `src/compiler/60.mir_opt/mir_opt/lmul_widen.spl` — RVV LMUL 1→2→4 promotion pass; gated behind `--enable-lmul-widen` flag until cross-target equivalence passes 100 PR cycles (NEW, ~250 lines)
  - `test/backend/simd_strict_emit/rvv/` — update goldens with LMUL=2 and LMUL=4 variants (MODIFY)
  - `test/perf/simd_perf_suite.spl` — SAXPY peak throughput benchmark on all 6 CPU targets; dot product; compare against reference timings (NEW, ~150 lines)
  - `test/backend/lmul_equivalence/` — LMUL=1 vs LMUL=2/4 output equivalence for SAXPY and dot (NEW, ~80 lines)
- **Bootstrap rebuild required**: NO (M7 adds no new externs; only MIR pass logic)
- **Owner workstream**: mir-opt, backend-cpu, tests
- **Verification gate** (run in order):
  ```
  # 1. LMUL=1 vs LMUL=2 equivalence (RVV, QEMU)
  bin/simple build --target=riscv64-rvv --enable-lmul-widen=2 \
    test/backend/lmul_equivalence/lmul1_vs_lmul2.spl -o /tmp/lmul2
  qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64 -kernel /tmp/lmul2 \
    2>&1 | grep 'PASS'
  # 2. LMUL=4 equivalence
  bin/simple build --target=riscv64-rvv --enable-lmul-widen=4 \
    test/backend/lmul_equivalence/lmul1_vs_lmul4.spl -o /tmp/lmul4
  qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64 -kernel /tmp/lmul4 \
    2>&1 | grep 'PASS'
  # 3. Golden diff with LMUL=2 variants
  diff <(riscv64-linux-gnu-objdump -d /tmp/lmul2 | grep -E 'vsetvli.*m2') \
       test/backend/simd_strict_emit/rvv/saxpy_lmul2.golden
  # 4. Perf gate (M7 ships only when all 6 targets hit ≥ 95% of §1.1 baseline)
  bin/simple run test/perf/simd_perf_suite.spl --target=all --threshold=0.95
  ```
- **Estimated complexity**: M
- **Risks**: LMUL widening that accidentally uses odd-aligned register groups causes illegal-instruction traps at runtime (B2 §4.6 alignment rules). The 100-PR-cycle flag gate (B1 architectural decision) means this may ship gated for a long time if the equivalence tests are not comprehensive. Ensure the flag is testable via env var (`SIMPLE_LMUL_WIDEN=2`), not just a compile-time constant — this lets CI toggle it independently of source changes.

---

## 3. File-by-File Touch List

All paths relative to repo root. LOC delta is net (positive = added lines, negative = removed lines). "Sum-of-absolutes" total is given in §8.

| # | Path | Action | Phase | Owner Workstream | Est. LOC Δ | Depends On |
|---|------|---------|-------|-----------------|------------|------------|
| 1 | `src/compiler/00.common/simd_types.spl` | MODIFY | M0 | compiler-frontend | +250 | — |
| 2 | `src/compiler/25.traits/vector_traits.spl` | NEW | M0 | compiler-frontend | +150 | 1 |
| 3 | `src/compiler/30.types/simd_vector_types.spl` | MODIFY | M0 | compiler-frontend | -300 (500→200) | 1, 2 |
| 4 | `src/lib/nogc_sync_mut/simd/__init__.spl` | NEW | M0 | stdlib | +60 | 2, 3 |
| 5 | `src/lib/nogc_sync_mut/simd/fixed_vec.spl` | NEW | M0 | stdlib | +120 | 2 |
| 6 | `src/lib/nogc_sync_mut/simd/scalable_vec.spl` | NEW | M0 | stdlib | +80 | 2 |
| 7 | `src/lib/nogc_sync_mut/simd/warp_vec.spl` | NEW | M0 | stdlib | +60 | 2 |
| 8 | `src/lib/nogc_sync_mut/simd/platform.spl` | NEW | M0 | stdlib | +60 | 1 |
| 9 | `src/lib/nogc_sync_mut/simd/compat.spl` | NEW | M0 | stdlib | +40 | 3 |
| 10 | `src/lib/nogc_sync_mut/simd.spl` | DELETE (replace with dir) | M0 | stdlib | -existing | 4 |
| 11 | `src/compiler/35.semantics/simd_check.spl` | MODIFY | M1 | compiler-frontend | +120 | 1, 2, 3 |
| 12 | `src/compiler/40.mono/instantiation.spl` | MODIFY | M1 | compiler-frontend | +80 | 3 |
| 13 | `src/compiler/50.mir/mir_types.spl` | MODIFY | M1 | compiler-frontend | +60 | 1 |
| 14 | `src/compiler/50.mir/mir_instructions.spl` | MODIFY | M1 | compiler-frontend | +80 | 13 |
| 15 | `src/compiler/50.mir/mir_lowering_expr.spl` | MODIFY | M1 | compiler-frontend | +200 | 11, 13, 14 |
| 16 | `src/compiler/60.mir_opt/mir_opt/simd_lowering.spl` | MODIFY | M1 | mir-opt | +60 | 13, 14 |
| 17 | `src/compiler/70.backend/backend/native/arm_neon.spl` | MODIFY | M1 | backend-cpu | +80 | 14 |
| 18 | `src/compiler/70.backend/backend/native/x86_64_simd.spl` | MODIFY | M1 | backend-cpu | +120 | 14 |
| 19 | `src/compiler/70.backend/backend/native/x86_64_avx512.spl` | NEW | M1 | backend-cpu | +500 | 14, 18 |
| 20 | `src/compiler/70.backend/portable_numeric_capabilities.spl` | MODIFY | M1 | backend-cpu | +60 | 1 |
| 21 | `test/backend/simd_strict_emit/neon/saxpy.golden` | NEW | M1 | tests | +30 | 17 |
| 22 | `test/backend/simd_strict_emit/neon/dot.golden` | NEW | M1 | tests | +30 | 17 |
| 23 | `test/backend/simd_strict_emit/neon/hcompare.golden` | NEW | M1 | tests | +30 | 17 |
| 24 | `test/backend/simd_strict_emit/neon/gather_add.golden` | NEW | M1 | tests | +30 | 17 |
| 25 | `test/backend/simd_strict_emit/neon/masked_store.golden` | NEW | M1 | tests | +30 | 17 |
| 26 | `test/backend/simd_strict_emit/sse/saxpy.golden` | NEW | M1 | tests | +25 | 18 |
| 27 | `test/backend/simd_strict_emit/sse/dot.golden` | NEW | M1 | tests | +25 | 18 |
| 28 | `test/backend/simd_strict_emit/sse/hcompare.golden` | NEW | M1 | tests | +25 | 18 |
| 29 | `test/backend/simd_strict_emit/sse/gather_add.golden` | NEW | M1 | tests | +25 | 18 |
| 30 | `test/backend/simd_strict_emit/sse/masked_store.golden` | NEW | M1 | tests | +25 | 18 |
| 31 | `test/backend/simd_strict_emit/avx2/saxpy.golden` | NEW | M1 | tests | +30 | 18 |
| 32 | `test/backend/simd_strict_emit/avx2/dot.golden` | NEW | M1 | tests | +30 | 18 |
| 33 | `test/backend/simd_strict_emit/avx2/hcompare.golden` | NEW | M1 | tests | +30 | 18 |
| 34 | `test/backend/simd_strict_emit/avx2/gather_add.golden` | NEW | M1 | tests | +30 | 18 |
| 35 | `test/backend/simd_strict_emit/avx2/masked_store.golden` | NEW | M1 | tests | +30 | 18 |
| 36 | `test/backend/simd_strict_emit/avx512/saxpy.golden` | NEW | M1 | tests | +35 | 19 |
| 37 | `test/backend/simd_strict_emit/avx512/dot.golden` | NEW | M1 | tests | +35 | 19 |
| 38 | `test/backend/simd_strict_emit/avx512/hcompare.golden` | NEW | M1 | tests | +35 | 19 |
| 39 | `test/backend/simd_strict_emit/avx512/gather_add.golden` | NEW | M1 | tests | +35 | 19 |
| 40 | `test/backend/simd_strict_emit/avx512/masked_store.golden` | NEW | M1 | tests | +35 | 19 |
| 41 | `src/compiler/50.mir/mir_types.spl` | MODIFY | M2 | compiler-frontend | +40 | 13 |
| 42 | `src/compiler/50.mir/mir_lowering_expr.spl` | MODIFY | M2 | compiler-frontend | +80 | 15 |
| 43 | `src/compiler/60.mir_opt/mir_opt/predicate_promote.spl` | NEW | M2 | mir-opt | +200 | 14, 16 |
| 44 | `src/compiler/70.backend/backend/native/x86_64_avx512.spl` | MODIFY | M2 | backend-cpu | +100 | 19 |
| 45 | `src/compiler/70.backend/backend/native/arm_neon.spl` | MODIFY | M2 | backend-cpu | +60 | 17, 41 |
| 46 | `test/backend/simd_strict_emit/avx512/hcompare.golden` | MODIFY | M2 | tests | ~0 | 44 |
| 47 | `test/backend/simd_strict_emit/avx512/masked_store.golden` | MODIFY | M2 | tests | ~0 | 44 |
| 48 | `test/semantics/simd_predication/predz_default.spl` | NEW | M2 | tests | +60 | 43 |
| 49 | `test/semantics/simd_predication/predx_promote.spl` | NEW | M2 | tests | +60 | 43 |
| 50 | `src/compiler/30.types/simd_platform.spl` | MODIFY | M3 | compiler-frontend | +80 | 1 |
| 51 | `src/compiler/50.mir/mir_types.spl` | MODIFY | M3 | compiler-frontend | +60 | 41 |
| 52 | `src/compiler/50.mir/mir_lowering_expr.spl` | MODIFY | M3 | compiler-frontend | +120 | 42 |
| 53 | `src/compiler/70.backend/backend/native/arm_sve2.spl` | NEW | M3 | backend-cpu | +600 | 51, 52 |
| 54 | `test/backend/simd_strict_emit/sve2/saxpy.golden` | NEW | M3 | tests | +40 | 53 |
| 55 | `test/backend/simd_strict_emit/sve2/dot.golden` | NEW | M3 | tests | +40 | 53 |
| 56 | `test/backend/simd_strict_emit/sve2/hcompare.golden` | NEW | M3 | tests | +40 | 53 |
| 57 | `test/backend/simd_strict_emit/sve2/gather_add.golden` | NEW | M3 | tests | +40 | 53 |
| 58 | `test/backend/simd_strict_emit/sve2/masked_store.golden` | NEW | M3 | tests | +40 | 53 |
| 59 | `test/platform/simd_platform_detect.spl` | NEW | M3 | tests | +80 | 50 |
| 60 | `src/compiler/30.types/simd_platform.spl` | MODIFY | M4 | backend-cpu | +50 | 50 |
| 61 | `src/compiler/70.backend/backend/native/riscv_rvv.spl` | NEW | M4 | backend-cpu | +550 | 51, 52 |
| 62 | `test/backend/simd_strict_emit/rvv/saxpy.golden` | NEW | M4 | tests | +40 | 61 |
| 63 | `test/backend/simd_strict_emit/rvv/dot.golden` | NEW | M4 | tests | +40 | 61 |
| 64 | `test/backend/simd_strict_emit/rvv/hcompare.golden` | NEW | M4 | tests | +40 | 61 |
| 65 | `test/backend/simd_strict_emit/rvv/gather_add.golden` | NEW | M4 | tests | +40 | 61 |
| 66 | `test/backend/simd_strict_emit/rvv/masked_store.golden` | NEW | M4 | tests | +40 | 61 |
| 67 | `test/platform/riscv_capability_detect.spl` | NEW | M4 | tests | +60 | 60 |
| 68 | `src/compiler/70.backend/gpu_intrinsics.spl` | MODIFY | M5 | backend-gpu | +120 | 15 |
| 69 | `src/compiler/35.semantics/gpu_checker.spl` | MODIFY | M5 | backend-gpu | +60 | 2, 68 |
| 70 | `src/compiler/70.backend/backend/cuda/ptx_builder.spl` | MODIFY | M5 | backend-gpu | +150 | 68 |
| 71 | `src/compiler/70.backend/backend/vulkan/spirv_builder.spl` | MODIFY | M5 | backend-gpu | +120 | 68 |
| 72 | `test/backend/simd_strict_emit/ptx/saxpy.golden` | NEW | M5 | tests | +50 | 70 |
| 73 | `test/backend/simd_strict_emit/ptx/dot.golden` | NEW | M5 | tests | +50 | 70 |
| 74 | `test/backend/simd_strict_emit/ptx/hcompare.golden` | NEW | M5 | tests | +50 | 70 |
| 75 | `test/backend/simd_strict_emit/ptx/gather_add.golden` | NEW | M5 | tests | +50 | 70 |
| 76 | `test/backend/simd_strict_emit/ptx/masked_store.golden` | NEW | M5 | tests | +50 | 70 |
| 77 | `test/gpu/cuda_saxpy_warpvec.spl` | NEW | M5 | tests | +100 | 70 |
| 78 | `test/gpu/vulkan_saxpy_compute.spl` | NEW | M5 | tests | +120 | 71 |
| 79 | `src/compiler/60.mir_opt/mir_opt/` (pass driver, file TBD) | MODIFY | M6 | mir-opt | +20 | 16, 43 |
| 80 | `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` | MODIFY (if needed) | M6 | mir-opt | +20 | 14, 79 |
| 81 | `test/auto_vectorize/av_saxpy.spl` | NEW | M6 | tests | +40 | 79, 80 |
| 82 | `test/auto_vectorize/av_dot.spl` | NEW | M6 | tests | +40 | 79, 80 |
| 83 | `test/auto_vectorize/av_cast_copy.spl` | NEW | M6 | tests | +40 | 79, 80 |
| 84 | `test/auto_vectorize/av_cond_copy.spl` | NEW | M6 | tests | +40 | 79, 80 |
| 85 | `test/auto_vectorize/av_broadcast_mul.spl` | NEW | M6 | tests | +40 | 79, 80 |
| 86 | `src/compiler/60.mir_opt/mir_opt/lmul_widen.spl` | NEW | M7 | mir-opt | +250 | 61 |
| 87 | `test/backend/simd_strict_emit/rvv/saxpy_lmul2.golden` | NEW | M7 | tests | +45 | 86 |
| 88 | `test/backend/simd_strict_emit/rvv/dot_lmul2.golden` | NEW | M7 | tests | +45 | 86 |
| 89 | `test/backend/simd_strict_emit/rvv/saxpy_lmul4.golden` | NEW | M7 | tests | +45 | 86 |
| 90 | `test/backend/lmul_equivalence/lmul1_vs_lmul2.spl` | NEW | M7 | tests | +80 | 86, 62, 63 |
| 91 | `test/backend/lmul_equivalence/lmul1_vs_lmul4.spl` | NEW | M7 | tests | +80 | 86, 89 |
| 92 | `test/perf/simd_perf_suite.spl` | NEW | M7 | tests | +150 | 17–19, 53, 61, 86 |

---

## 4. Test Plan

### 4.1 Strict-Emit Goldens

**37 golden files** total: 5 kernels × 7 CPU targets + 5 PTX GPU target + 2 additional GPU (SPIR-V Vulkan, tracked separately from golden files as end-to-end shader compile).

Path scheme: `test/backend/simd_strict_emit/<target>/<kernel>.golden`

CPU goldens are byte-exact hex sequences (one word per line, as per B2 §7.3). PTX goldens are human-readable `.ptx` text snippets.

| Target | Kernel set | Format | Phase | Emulator |
|--------|-----------|--------|-------|---------|
| `neon` | saxpy, dot, hcompare, gather_add, masked_store | hex bytes | M1 | native AArch64 or `qemu-aarch64` |
| `sse` | same 5 | hex bytes | M1 | native x86-64 |
| `avx2` | same 5 | hex bytes | M1 | native x86-64 |
| `avx512` | same 5 | hex bytes | M1/M2 | `qemu-system-x86_64 -cpu Icelake-Server` |
| `sve2` | same 5 | hex bytes | M3 | `qemu-aarch64 -cpu max,sve2=on` |
| `rvv` | same 5 + lmul2/lmul4 saxpy/dot (M7) | hex bytes | M4/M7 | `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64` |
| `ptx` | same 5 | PTX text | M5 | CUDA SDK nvptx / `cuobjdump` |

**Compiled-mode requirement**: every golden test is invoked as:
1. Compile the kernel source to native binary: `bin/simple build --target=<target> kernel.spl`
2. Disassemble / inspect emitted instructions: compare against `.golden` via `diff`
3. Do NOT use `bin/simple test` exit-code-only gating — per `feedback_compile_mode_false_greens` (project memory), both `--mode=native` and `--mode=smf` can false-green. Strict-emit diff is the primary gate.

**Non-host target QEMU invocations (copy-paste reference)**:

| Target | QEMU command |
|--------|-------------|
| AVX-512 (no hardware) | `qemu-system-x86_64 -cpu Icelake-Server -nographic -kernel <binary>` |
| SVE2 | `qemu-aarch64 -cpu max,sve2=on <binary>` |
| RVV | `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64 -nographic -kernel <binary>` |
| RVV (spike secondary) | `spike --isa=rv64gcv <binary>` |
| NEON cross-run on x86 host | `qemu-aarch64 -cpu max <binary>` |

### 4.2 Cross-Target Equivalence

The 5 kernels compiled to all 7 CPU targets must produce identical output for known float32 inputs:
- Input: `x=[1.0, 2.0, ..., 16.0]`, `y=[0.5, 1.0, ..., 8.0]`, `alpha=2.0`
- SAXPY expected output: `y[i] += 2.0 * x[i]` for all i
- Comparison: bitwise-identical float output (NaN/infinity edge cases excluded)
- Non-host targets run via QEMU (same framework as FreeBSD QEMU bootstrap in CLAUDE.md)

### 4.3 Predication Semantics

| Test | Condition | Expected | Phase |
|------|-----------|----------|-------|
| `predz_default.spl` | `predicate_promote` pass OFF | Inactive lanes contain 0.0 (zero-filled) | M2 |
| `predx_promote.spl` | `predicate_promote` pass ON, inactive lanes provably dead | Emitted instructions use `_x` form; no zeroing overhead | M2 |
| Manual golden for AVX-512 | k-reg masked `vcmpps` + `vmaskmovps` | Byte-exact match | M2 |

All run in compiled mode (`bin/simple build && ./out`).

### 4.4 LMUL Invariance

| Test | LMUL | Expected |
|------|------|----------|
| `lmul1_vs_lmul2.spl` SAXPY | LMUL=1 vs LMUL=2 | Bitwise-identical output | M7 |
| `lmul1_vs_lmul4.spl` SAXPY | LMUL=1 vs LMUL=4 | Bitwise-identical output | M7 |
| `lmul1_vs_lmul2.spl` dot | LMUL=1 vs LMUL=2 | Bitwise-identical output | M7 |

LMUL variants tested under `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64` in compiled mode.

### 4.5 GPU / CUDA End-to-End

| Test | Target | Execution method | Pass criterion |
|------|--------|-----------------|----------------|
| `cuda_saxpy_warpvec.spl` | PTX SM_70+ | CUDA driver API; launch kernel; memcpy back | Output matches CPU reference |
| `vulkan_saxpy_compute.spl` | SPIR-V Vulkan 1.2+ | Vulkan loader; compute dispatch; readback | Output matches CPU reference |
| PTX golden diff | PTX text | `diff test/backend/simd_strict_emit/ptx/<k>.golden` | Byte-exact match |

If no GPU hardware is available in CI, PTX golden diff is the only required gating test. Hardware execution is an optional smoke test.

---

## 5. GPU / CUDA Skeleton Scope (Explicit)

### In Scope for M5 (First Ship)

| Feature | Detail |
|---------|--------|
| `WarpVec<T>` shuffle ops | `shfl_up`, `shfl_down`, `shfl_bfly`, `shfl_idx` via `shfl.sync.*` PTX |
| `warp_reduce_sum` | Shuffle-based tree reduction; SPIR-V `OpGroupNonUniformFAdd` |
| `warp_ballot` | `vote.sync.ballot.b32` PTX; SPIR-V `OpGroupNonUniformBallot` |
| PTX `.v4` packed load/store | `ld.global.v4.f32`, `st.global.v4.f32` |
| End-to-end CUDA SAXPY kernel | One tile; correct output on SM_70+ |
| End-to-end Vulkan compute SAXPY | One dispatch; `OpTypeVector float32 4`; correct output |
| PTX strict-emit goldens | 5 goldens, text-exact diff |
| WarpVec kernel-only enforcement | `35.semantics/gpu_checker.spl` compile error on non-kernel call |

### Out of Scope for M5 (Deferred)

| Feature | Reason for deferral |
|---------|---------------------|
| Tensor cores (`mma.sync`, `wmma`) | Requires matrix type extension; separate RFC |
| CUDA dynamic parallelism | Complex host–device control flow; not needed for SIMD |
| ROCm / HIP backend | New backend family; deferred to post-M7 |
| Metal / MSL backend | macOS-only; deferred to post-M7 |
| WGSL backend | WebGPU; deferred to post-M7 |
| Vulkan ray query extension | Not SIMD compute; separate work |
| Sparsity tensor cores | Requires SM_80+ sparse matmul; deferred |
| PTX SASS-level optimization | `mbarrier`, structured barriers; deferred |
| tiled matmul kernel | Needs shared memory tile management; M7+ stretch |

---

## 6. Risk Register & Contingencies

| # | Risk | Source | Likelihood | Impact | Mitigation |
|---|------|--------|-----------|--------|------------|
| R1 | **Compiled-mode false-greens**: `--mode=native` no-ops unresolved std.spec calls; `--mode=smf` swallows runtime errors; both report PASSED | `feedback_compile_mode_false_greens` (project memory) | High | High | **Primary gate is strict-emit byte/text diff, not exit code.** Cross-target equivalence is secondary gate only after strict-emit passes. Never gate phase completion on "test reports PASSED" alone. Check: `diff <(objdump -d out.o \| grep -oP '\t[0-9a-f ]+\t') kernel.golden` must be the final gate for every CPU phase. |
| R2 | **Cranelift `>>` bug pattern recurrence**: shift-heavy SIMD lowering may silently miscompile signed right-shifts | `feedback_cranelift_shr_bug` (project memory, FR-DRIVER-0002b) | Medium | High | All shift ops in NEON/AVX-512/SVE2/RVV emitters reviewed in compiled mode at M1 and M3. Specific `>>` golden in test suite for each target. Check: `grep -n 'shr\|sar\|>>\\|shift' src/compiler/70.backend/backend/native/arm_neon.spl src/compiler/70.backend/backend/native/x86_64_avx512.spl` — each hit must have a corresponding golden entry. |
| R3 | **jj parallel commit clobbering**: parallel agent commits can trigger jj reconcile deleting uncommitted Edit-tool changes | `feedback_jj_uncommitted_clobbered_by_parallel` + `feedback_force_push_kernel_arc` (project memory) | High | Medium | Each sub-batch committed immediately after lint-clean. All parallel file scopes partitioned disjointly (per `feedback_parallel_scope_partition`). Check after each push: `git log --oneline -5 && git diff origin/main --stat` — if file count drops, abort and investigate before proceeding. |
| R4 | **New rt_simd_* externs require full bootstrap rebuild**: `bin/simple build` silently no-ops; only `bootstrap-from-scratch.sh --deploy` works | `feedback_extern_bootstrap_rebuild` (project memory) | Medium | High | Any phase adding a new `rt_simd_*` extern MUST run `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`. Check: `grep -r 'rt_simd_\|rt_vec_\|rt_mask_' --include='*.spl' src/runtime/ \| wc -l` before and after each extern addition. |
| R5 | **SVE2 hardware unavailability**: no physical SVE2 hardware in CI | A1 §2.1 (SVE2 is Neoverse N2+, not widely available) | High | Low | Mitigation: `qemu-aarch64 -cpu max,sve2=on` for all SVE2 tests. Check QEMU supports SVE2: `qemu-aarch64 -cpu max,sve2=on /bin/true && echo ok`. Physical hardware is an optional smoke test, not gating. |
| R6 | **RVV hardware unavailability**: no physical RISC-V V-extension hardware | A1 §2.2 (RVV 1.0 ratified 2021; boards limited) | High | Low | Mitigation: `qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64` + spike simulator as secondary. Check: `spike --isa=rv64gcv --help 2>&1 \| grep -i vector` before M4 begins. Pin VLEN=128 in goldens to match emulator default. |
| R7 | **PTX/SAS divergence between CUDA SDK versions**: warp shuffle encoding changes between SM_70 / SM_80 / SM_90 | A1 §3.1 (PTX ISA §9.7.14 mbarrier semantics change between SM generations) | Medium | Medium | Pin SDK major in test runner. Check: `nvcc --version \| grep -oP 'release \K[0-9]+'`. Golden header must contain `# cuda-sdk: <major>`. Test runner fails if SDK major != golden header major. |
| R8 | **Vec4f/Vec2f caller breakage during alias migration**: existing callers use `.x`/`.y`/`.z`/`.w` field access, which `FixedVec<T,N>` does not expose | B1 §8.2 (field access → `extract(N)` migration required); A2 §1b (5 hardcoded structs) | Medium | Medium | Migration only within compiler-internal code. `compat.spl` provides type aliases. **Do NOT migrate** geometry code in `engine/render/vector.spl` or `linear_algebra/vector_ops.spl` (different positional semantics, B1 §8.2 explicit exclusion). Check before M0: `grep -rn '\.x\b\|\.y\b\|\.z\b\|\.w\b' --include='*.spl' src/compiler/ \| grep -i 'vec4f\|vec2f\|vec8f'` — enumerate all call sites, confirm count before and after migration. |

---

## 7. Sequencing Rationale

### Why M0 before M1

M0 establishes the type spine (`FixedVec<T,N>`, `Vector` trait, `Mask<V>`, `FixedMask<N>`). M1's wire-up of `FixedVec::method` → `SimdXxx` MIR (at `mir_lowering_expr.spl`) cannot proceed until the types are defined. Similarly, the AVX-512 EVEX emitter in M1 requires `FixedVec<f32,16>` to be a legal type in the IR.

### Why M1 before M2

The k-register allocation path for AVX-512 (M2) depends on `FixedVec<T,N>` and `x86_64_avx512.spl` being present (M1). The `predicate_promote.spl` liveness analysis requires `MirInstKind::MaskOp` variants (M1).

### Why M2 before M3 and M4

`ScalableVec<T>` predication (SVE2 `_z`/`_x`, RVV `vm` mask) reuses the same `Mask<V>` type and `predicate_promote` pass introduced in M2. Doing M3/M4 before M2 would require implementing two different predication models or deferring predication to post-M3/M4 and retrofitting — a large rework risk.

### Why M3 (SVE2) before M4 (RVV)

SVE2 has dedicated P-registers (clean `Mask<V>` lowering, directly analogous to AVX-512 k-regs just landed in M2). RVV reuses v0 from the data register file — the allocator must emit `vmv1r.v v0, vX` before every masked op (B2 finding 3), which is a non-trivial constraint layered on top of the scalable lowering model. Implementing SVE2 first gives a validated scalable template; RVV then adds the v0 constraint as a well-scoped delta. Additionally, QEMU SVE2 support is more mature than QEMU RVV (especially with VLEN selection).

### Why M3/M4 are serial, not parallel

M4 uses M3's `arm_sve2.spl` as the structural template for `riscv_rvv.spl`. Parallelizing requires two implementers to agree on the scalable lowering API in `mir_lowering_expr.spl` before either starts — coordination overhead exceeds the time saved. With a single-track implementation, sequential is cheaper. If two independent tracks are available, M3 and M4 can be parallelized after the `ScalableVecOp` MIR lowering API is frozen (typically at the M3 design review).

### Why M5 (GPU WarpVec) is placed after M4 but can be parallel

M5 requires FixedVec MIR (M1) for GPU kernel type-check but does NOT depend on M3/M4 (scalable CPU targets). File scopes for M5 are disjoint from M3/M4: M3 touches `arm_sve2.spl` + `mir_lowering_expr.spl`; M4 touches `riscv_rvv.spl`; M5 touches `gpu_intrinsics.spl`, `ptx_builder.spl`, `spirv_builder.spl`, `gpu_checker.spl`. No file overlap. Per `feedback_parallel_scope_partition`, parallel development is safe after M2 ships.

**Parallel schedule option** (if two tracks are available):

```
Track A:  M0 → M1 → M2 → M3 → M4 → M7
Track B:                  M5 → M6
```
Track B starts M5 immediately after M2 completes (FixedVec MIR is stable). Track B M6 starts after M5 and after Track A completes M4 (so all CPU targets are available for auto-vectorize cross-target testing). Tracks A and B merge at M7. Estimated saving vs serial: 4–5 dev-weeks.

### Why M6 (auto-vectorize) before M7 (LMUL widening)

Auto-vectorization (M6) wires the existing `auto_vectorize_codegen.spl` into the MIR opt driver. Without M6, the auto-vectorizer is latent and performance metrics in M7's perf suite would not reflect auto-vectorized loops. M7's SAXPY peak throughput criterion (§1.1) requires auto-vectorization to be active.

### Why M7 last

LMUL widening is a pure optimization pass with correctness validated by equivalence tests. It is gated behind a flag until 100 PR cycles of equivalence testing pass (B1 architectural decision). It has no downstream dependents within this rollout — it is the final perf polish phase.

---

## 8. Effort Summary

### Per-Phase Complexity

| Phase | Title | Complexity | Est. New LOC | Est. Weeks (1 dev) |
|-------|-------|-----------|-------------|-------------------|
| M0 | Type IR Foundations | M | +610 (net: +310 after -300 delete) | 1.5 |
| M1 | FixedVec End-to-End + Existing Backends + AVX-512 | XL | +1,720 | 4.0 |
| M2 | First-Class Mask + Predication | L | +620 | 2.5 |
| M3 | ScalableVec + SVE2 | XL | +1,070 | 3.5 |
| M4 | ScalableVec + RVV | L | +820 | 2.5 |
| M5 | GPU WarpVec Skeleton | L | +820 | 2.5 |
| M6 | Auto-Vectorization Wiring | M | +240 | 1.5 |
| M7 | LMUL Widening + Perf Gates | M | +695 | 2.0 |
| **Total** | | | **~6,600 sum-of-abs; ~6,300 net** | **~20 dev-weeks** |

### Phase Dependency DAG

```
M0 ──► M1 ──► M2 ──► M3 ──► M4 ──────────► M7
                └──────────► M5 ──► M6 ──► M7
```

Key hard edges (cannot start phase without prior completing):
- M0 → M1: `FixedVec<T,N>` type must exist before `mir_lowering_expr.spl` wire-up
- M1 → M2: `MirInstKind::MaskOp` variants needed before predication lowering
- M2 → M3: `predicate_promote` pass and `Mask<V>` MIR type needed before SVE2 predication
- M2 → M5: FixedVec MIR stable before GPU kernel type-check (B1 §7 requires `FixedVec<f32,4>` → SPIR-V `OpTypeVector`)
- M3 → M4: SVE2 scalable lowering template and `ScalableVecOp` MIR API frozen before RVV starts
- M4 → M7: RVV LMUL=1 must be green before LMUL widening pass touches it
- M4 → M6: all 5 CPU targets needed for cross-target auto-vectorize verification (§1.4)
- M6 → M7: auto-vectorize must be active so M7 perf suite measures real vectorized throughput

Soft edges (preferred ordering, not strictly blocking):
- M5 after M4 in single-track: allows one developer to finish CPU work before switching ISA families
- M6 after M5 in two-track: M5 implementer can contribute M6 GPU auto-vectorize path (SPIR-V vector ops)

### Assumptions

1. One senior implementer per phase; no parallel tracks (conservative baseline). See §7 for two-track option saving 4–5 weeks.
2. Bootstrap rebuild (`bootstrap-from-scratch.sh --deploy`) counted once per phase that adds new externs (M1, M3, M4, M5), adding ~0.5 days each. Per `feedback_extern_bootstrap_rebuild`, `bin/simple build` silently no-ops for extern additions — must use the full script.
3. QEMU test infrastructure already usable (per FreeBSD QEMU bootstrap pattern in CLAUDE.md as precedent); no environment setup time counted. Verify with `qemu-aarch64 --version`, `qemu-system-riscv64 --version` before M3/M4 begin.
4. GPU phase (M5) assumes CUDA SDK 11+ is installed (`nvcc --version`) and Vulkan 1.2+ loader is available (`vulkaninfo --summary`).
5. LOC deltas are net within each phase; overlap rows in the table (same file modified in multiple phases, e.g., `mir_lowering_expr.spl` in M1 and M2) are counted separately per-phase.
6. LOC delta total (sum-of-absolutes) is ~6,600; net is ~6,300 (slightly less due to `-300` delete of old `simd_vector_types.spl` scalar structs).
7. `30.types/simd.spl` (665-line test file, A2 §1a) is a test artifact, not a compiler source file. It is not in the file-touch table and not counted in LOC delta.
8. `simd_lowering.spl:203` (A2 §2) is counted as an existing file being modified (M1 adds ~60 lines for new op names). It is not a new file.

---

## 9. Observable Success State per Phase

The following table answers "how do I know this phase is genuinely done?" using observable compiler output, not implementer assertion. Each row uses a concrete `bin/simple` invocation or file check — not "tests pass."

| Phase | Observable Signal | Command / Check |
|-------|------------------|----------------|
| M0 | `Vec4f` alias resolves to `FixedVec<f32,4>` in desugared output | `bin/simple desugar src/lib/nogc_sync_mut/simd/compat.spl \| grep 'Vec4f.*FixedVec<f32, 4>'` |
| M0 | `use std.simd` imports `FixedVec`, `ScalableVec`, `Vector` | `bin/simple check src/lib/nogc_sync_mut/simd/__init__.spl \| grep 'no errors'` |
| M1 | NEON SAXPY golden is byte-exact | `diff <(objdump -d /tmp/saxpy_neon.o \| grep -oP '\t[0-9a-f ]+\t') test/backend/simd_strict_emit/neon/saxpy.golden && echo OK` |
| M1 | AVX-512 saxpy contains EVEX-encoded vfmadd (not VEX) | `objdump -d /tmp/saxpy_avx512.o \| grep -P '^.*\tevex.*vfmadd'` |
| M2 | AVX-512 masked op uses k1–k7, never k0 | `objdump -d /tmp/masked_store_avx512.o \| grep '{k[1-7]}'` — must match; `grep '{k0}'` — must be empty |
| M2 | `_x` promotion emits fewer instructions than `_z` for same kernel | `wc -l <(bin/simple desugar --predpromote=off ...)` vs `wc -l <(bin/simple desugar --predpromote=on ...)` |
| M3 | SVE2 SAXPY contains `svptrue` + `fmla` | `aarch64-linux-gnu-objdump -d /tmp/saxpy_sve2.o \| grep -E 'svptrue\|fmla'` |
| M3 | NEON goldens unchanged after M3 lands | `diff test/backend/simd_strict_emit/neon/saxpy.golden test/backend/simd_strict_emit/neon/saxpy.golden.pre-m3` |
| M4 | RVV SAXPY contains `vsetvli` + `vmv1r.v v0` before masked op | `riscv64-linux-gnu-objdump -d /tmp/masked_store_rvv.o \| grep -A1 'vmv1r.v v0'` |
| M5 | PTX SAXPY contains `ld.global.v4.f32` + `shfl.sync` | `grep -E 'ld\.global\.v4\.f32\|shfl\.sync' test/backend/simd_strict_emit/ptx/saxpy.golden` |
| M6 | Auto-vectorizer fires on scalar saxpy loop | `bin/simple desugar --target=x86_64-avx2 test/auto_vectorize/av_saxpy.spl \| grep 'SimdFmaF32\|SimdMulF32'` |
| M7 | LMUL=2 RVV saxpy golden contains `vsetvli.*m2` | `grep 'vsetvli.*m2' test/backend/simd_strict_emit/rvv/saxpy_lmul2.golden` |
| M7 | LMUL=1 and LMUL=2 produce bitwise-identical output | `diff <(qemu-riscv64 lmul1_out.bin) <(qemu-riscv64 lmul2_out.bin) && echo LMUL-EQUIV-OK` |

---

## 10. Pre-Flight Checklist per Phase

Before starting each phase, the implementer must verify these environment preconditions. Failures here cause false-pass at phase gates (per R4, R5, R6). Open questions that block the phase are called out inline (see §11 for full list).

### M0 Pre-Flight
```
# Import resolver handles simd/ directory (Q6):
grep -r 'nogc_sync_mut/simd' --include='*.spl' src/compiler/ | head -5  # find importer code
# Count Vec4f/.x call sites to size migration (Q5):
grep -rn '\.x\b\|\.y\b\|\.z\b\|\.w\b' --include='*.spl' src/compiler/ | grep -i 'vec4f\|vec2f\|vec8f' | wc -l
```

### M1 Pre-Flight
```
# Confirm qemu-system-x86_64 supports Icelake-Server (for AVX-512 testing):
qemu-system-x86_64 -cpu Icelake-Server -nographic -snapshot -kernel /dev/null 2>&1 | grep -v 'Icelake'
# Confirm bootstrap script is available:
ls scripts/bootstrap/bootstrap-from-scratch.sh
```

### M3 Pre-Flight
```
# Confirm QEMU version supports SVE2 (needs QEMU ≥ 6.2):
qemu-aarch64 --version | head -1
qemu-aarch64 -cpu max,sve2=on /bin/true 2>&1; echo "exit: $?"  # must be 0
# Confirm AArch64 cross-objdump available for golden inspection:
aarch64-linux-gnu-objdump --version | head -1
```

### M4 Pre-Flight
```
# Confirm QEMU RISC-V supports V extension:
qemu-system-riscv64 -cpu rv64,v=true,vlen=128,elen=64 -nographic -machine virt \
  -bios none -kernel /dev/null 2>&1 | grep -v 'could not'
# Confirm spike simulator available (secondary gate):
which spike && spike --isa=rv64gcv --help 2>&1 | grep -i vector
# Confirm riscv64 cross-objdump:
riscv64-linux-gnu-objdump --version | head -1
```

### M5 Pre-Flight
```
# Confirm CUDA SDK major version (pin in golden headers):
nvcc --version | grep -oP 'release \K[0-9]+'
# Confirm Vulkan 1.2+ with subgroup support:
vulkaninfo --summary 2>/dev/null | grep -E 'subgroupSize|Vulkan 1\.[2-9]'
# Confirm nvcc on PATH:
which nvcc
```

### M7 Pre-Flight
```
# Confirm RVV LMUL=1 goldens pass before enabling widening (regression baseline):
for k in saxpy dot hcompare gather_add masked_store; do
  diff <(riscv64-linux-gnu-objdump -d /tmp/${k}_rvv | grep -E 'vsetvli.*m1') \
       test/backend/simd_strict_emit/rvv/${k}.golden && echo "${k}: OK"
done
# Confirm perf baseline was established (§1.1 / Q8):
ls test/perf/simd_perf_baseline.json 2>/dev/null || echo "MISSING: run perf baseline first"
```

---

## 11. Open Questions / Followups (Required Before M0)

The following questions cannot be resolved from the four upstream docs and require human decision before implementation begins.

| # | Question | Blocking Phase | Source of Uncertainty |
|---|----------|---------------|----------------------|
| Q1 | **auto_vectorize wire-up status**: A2 §7 states "call site unconfirmed." First task of M6 must be a `grep` verification: is `auto_vectorize_codegen.spl` already called from the MIR opt pass driver? If YES, M6 complexity drops to S. If NO (wiring required), M6 is M. | M6 | A2 §7 gap map — explicitly marked unconfirmed |
| Q2 | **SVE2 sub-feature target**: Does M3 target SVE2 base only, or include SME (Scalable Matrix Extension) and SVE2.1? A1 §2.1 covers SVE2 base; SME and SVE2.1 add new instruction classes. Recommend: base SVE2 only, SME is post-M7. | M3 | A1 §2.1 does not enumerate SME or SVE2.1 explicitly |
| Q3 | **RVV backend filename**: B2 §4.6 specifies `riscv_rvv.spl`; B1 pipeline overview says `riscv_v.spl`. Choose one canonical name before M4. This plan uses `riscv_rvv.spl` (B2 §4.6 is more recent). | M4 | Naming inconsistency between B1 and B2 |
| Q4 | **PTX minimum SM level**: B1 §7 does not specify minimum SM for WarpVec shuffles. Recommend SM_70 (`__shfl_sync` requires Volta+). Confirm with CUDA SDK team or pin in test runner config. | M5 | A1 §3.1 mentions `shfl.sync` without SM version constraint |
| Q5 | **Vec4f field-access migration scope**: How many call sites in the compiler use `.x`/`.y`/`.z`/`.w` on `Vec4f`/`Vec8f`? A2 §1b reports 5 hardcoded structs but does not count call sites. Run `grep -r '\.x\b\|\.y\b\|\.z\b\|\.w\b' src/compiler/` scoped to `Vec4f` before M0 to size the migration. | M0 | A2 §1b does not enumerate call sites |
| Q6 | **`simd.spl` single-file vs `simd/` directory rename**: `src/lib/nogc_sync_mut/simd.spl` (and `simd.smf`) currently exist as single files. The migration to `simd/` directory requires a RENAME+DELETE. Confirm that `use std.simd` resolution in the import resolver handles both a single-file `.spl` and a directory `__init__.spl` correctly (or if a compiler change is needed). | M0 | A2 §8.3 assumes directory resolution works; import resolver behavior unconfirmed |
| Q7 | **LMUL widening flag interface**: B1 says "keep behind a flag" but does not specify whether the flag is a CLI arg (`--enable-lmul-widen`), an env var (`SIMPLE_LMUL_WIDEN=1`), or a source annotation (`@lmul_widen`). Choose one before M7 to avoid ABI-like flag naming churn. | M7 | B1 §3.2 defers to implementation |
| Q8 | **Performance regression baseline**: M7 gates on "≥ 95% of peak FMA throughput." The baseline must be established (measured cycles/element on a reference machine) before M7 can gate. Plan: establish baseline at end of M4 when the first complete scalable target is available. | M7 | §1.1 performance criterion requires a reference measurement |
