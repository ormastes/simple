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

## Phase 2 Follow-Up Scenarios

- LLVM entry points consume the portable numeric registry rather than relying only on hardcoded x86_64/RISC-V feature defaults.
- Native backend dispatch consumes the same target-derived portable plan before per-architecture ISel selection.
- Generic x86_64 keeps `x86_avx_requires_runtime_probe` semantics visible even after LLVM/native integration.
- RV64 `F`/`D` targets do not silently claim vector SIMD during LLVM/native integration.
- `scalar_fallback` remains present across backend integrations when target lowering is enabled.
