# Portable SIMD + FP Modules Specification

**Feature ID:** #PSFM-001 | **Category:** Compiler Backend | **Status:** Draft

_Source: `test/unit/compiler/portable_numeric_capabilities_spec.spl`_

---

Tests the phase-1 portable numeric capability registry.
Verifies feature-family separation, preset-derived capability facts, lowering selection, and explicit diagnostics.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 1 |

## Covered Scenarios

- x86_64 generic preset exposes scalar FP and portable vector capability while requiring runtime SIMD probing for AVX selection.
- RV64 Linux exposes scalar FP through `F`/`D` and selects `riscv_fd`.
- Disabling `vector_simd` on RV64 Linux leaves `scalar_fp` and `riscv_fd` intact.
- RV32 bare-metal integer-only preset exposes scalar fallback only.
- Unsupported vector requests are visible in diagnostics output.

## Phase 2 Covered Scenarios

_Source: `test/unit/compiler/portable_numeric_capabilities_spec.spl` (extended), `test/unit/compiler/portable_numeric_plan_threading_spec.spl` (new), `test/unit/compiler/scalable_vec_mir_scaffolding_spec.spl` (new)_

| # | Scenario | Test File | AC | Marker |
|---|----------|-----------|-----|--------|
| P2-1 | `riscv_v` capability available → `ScalableVec` MIR type instantiable; native lowering returns deferred-diagnostic | `scalable_vec_mir_scaffolding_spec.spl` | AC-5 | negative |
| P2-2 | x86_64 generic preset → AVX flags NOT in LLVM features list (`requires_runtime_simd_probe == true`) | `portable_numeric_capabilities_spec.spl` | AC-1 | positive |
| P2-3 | rv64_linux preset → `+f` and `+d` derive from registry, not hardcoded | `portable_numeric_capabilities_spec.spl` | AC-2 | positive |
| P2-4 | rv32_baremetal int-only preset → no `+f`/`+d`/`+v` features | `portable_numeric_capabilities_spec.spl` | AC-2 | positive |
| P2-5 | `NativeCodegenAdapter` exposes `plan: PortableNumericLoweringPlan` field after `create()` | `portable_numeric_plan_threading_spec.spl` | AC-3 | positive |
| P2-6 | `compile_native_riscv64` with `ScalableVec` ops returns deferred-diagnostic, not silent code (negative guard) | `scalable_vec_mir_scaffolding_spec.spl` | AC-5 | negative |
| GAP-1 | Generic x86_64 LLVM target → `cpu == "x86-64-v1"` and features list contains neither `+avx` nor `+avx2` | `portable_numeric_capabilities_spec.spl` | AC-4 | negative |

### Zicbom/Zicboz/Zicbop Cross-Feature Contract (Feature B)

| # | Scenario | Test File | AC | Marker |
|---|----------|-----------|-----|--------|
| B-1 | `PortableNumericCapabilities` exposes 4 new bool fields (`has_riscv_zicbom`, `has_riscv_zicboz`, `has_riscv_zicbop`, `requires_runtime_cache_probe`) with `false` defaults across all existing presets | `portable_numeric_capabilities_spec.spl` | AC-4 | positive |

### Negative Marker Alignment

Active negative markers (tests that must FAIL if implementation is wrong):
- P2-1: `ScalableVec` MIR type missing → spec script exits non-zero
- P2-6: `NativeCodegenAdapter` does not return deferred-diagnostic → assertion on `diagnostics` string fails
- GAP-1: `LlvmTargetConfig.for_target_portable_numeric` produces `cpu != "x86-64-v1"` or `features` contains `+avx`/`+avx2`

### Phase 2 Follow-Up Scenarios (Moved to Covered Above)

_All 5 original follow-up scenarios are now covered by the Phase 2 Covered Scenarios table above._
