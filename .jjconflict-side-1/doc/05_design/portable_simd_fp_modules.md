<!-- codex-design -->
# Design: portable_simd_fp_modules

## Module Shape

- `src/compiler/70.backend/portable_numeric_capabilities.spl`
  - derives portable numeric capabilities from `TargetPreset`,
  - models feature-family enablement,
  - produces lowering-module selections and diagnostics.
- `src/compiler/70.backend/__init__.spl`
  - re-exports the new module for stable backend imports.
- `test/unit/compiler/portable_numeric_capabilities_spec.spl`
  - runs a compiled probe script against the real module imports.

## Capability Rules

- `has_scalar_fp`:
  - true when preset FP support is available or RISC-V `F`/`D` is implied.
- `has_vector_simd`:
  - true for phase-1 x86_64 portable vectors,
  - true for RISC-V only when `V` is explicitly present,
  - false for RV64/RV32 `F`/`D`-only targets.
- `has_avx` / `has_avx2`:
  - remain false in the generic preset-derived capability result,
  - x86_64 records `requires_runtime_simd_probe=true` instead.

## Lowering Selection

- If `scalar_fp` is enabled and available, add `scalar_fp`.
- If `vector_simd` is enabled and available, add `vector_simd`.
- If `target_lowering` is enabled:
  - always add `scalar_fallback`,
  - add `x86_avx` for x86_64,
  - add `riscv_v` when `V` is present,
  - otherwise add `riscv_fd` when `F` or `D` is present.
- Add diagnostics when a requested family is unavailable or when x86 needs runtime SIMD probing.

## Deferred Work

- No RVV scalable-vector MIR representation in this slice.
- No user-facing AVX-only or RVV-only API in this slice.

## Phase 2 Wiring Targets

- LLVM target configuration:
  - [llvm_target.spl](/home/ormastes/dev/pub/simple/src/compiler/70.backend/backend/llvm_target.spl:213)
  - Use the portable numeric registry as the authoritative source for phase-2 SIMD/FP feature selection.
  - Resolve the current mismatch where generic x86_64 assumes `x86-64-v3` while the registry marks AVX-family use as runtime-probe-gated.
- LLVM translation entry:
  - [mir_to_llvm.spl](/home/ormastes/dev/pub/simple/src/compiler/70.backend/backend/mir_to_llvm.spl:25)
  - Thread target-derived portable numeric plans into LLVM lowering once vector/scalar-FP pattern selection becomes real.
- Native adapter and dispatch:
  - [native_codegen_adapter.spl](/home/ormastes/dev/pub/simple/src/compiler/70.backend/backend/native_codegen_adapter.spl:16)
  - [native/mod.spl](/home/ormastes/dev/pub/simple/src/compiler/70.backend/backend/native/mod.spl:34)
  - Derive the plan once per compile and thread it into per-target native lowering paths before ISel dispatch.
- RISC-V target normalization:
  - [riscv_target.spl](/home/ormastes/dev/pub/simple/src/compiler/70.backend/backend/riscv_target.spl:29)
  - Replace hardcoded `F`/`D` assumptions with a registry-backed capability source before claiming `riscv_v` or integer-only variants.
