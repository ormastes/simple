# SStack State: portable-simd-fp-modules

## User Request
> Implement portable SIMD/FP module scaffolding: capability registry (derives NumericCaps from TargetPreset), lowering-module selection (scalar_fallback, x86_avx, riscv_fd, riscv_v), FP profile classification, and a comprehensive spec covering all four modules.

## Task Type
feature

## Refined Goal
> Create four source modules in src/lib/nogc_sync_mut/simd/ covering (1) numeric_caps — portable capability facts, (2) cap_registry — TargetSpec→CapRegistryEntry derivation with x86 probe encoding, (3) lowering_sel — independently toggleable scalar_fp/vector_simd/target_lowering selection, (4) fp_profile — FP tier classification per architecture. Verified via a self-contained 20-test spec.

## Acceptance Criteria
- [x] AC-1: NumericCaps struct with scalar_only / x86_64_baseline factories + supports_vectorization, max_simd_bits, describe methods
- [x] AC-2: CapRegistryEntry.derive() correctly derives x86 probe requirement and riscv integer-only diagnostics
- [x] AC-3: LoweringSelection.select() chooses x86_sse2, x86_avx, riscv_fd, riscv_v, or scalar_fallback correctly
- [x] AC-4: LoweringConfig scalar_fp, vector_simd, target_lowering independently toggleable
- [x] AC-5: FpProfile with tier classification (none, soft-fp, hard-fp-sp, hard-fp-dp, hard-fp-simd)
- [x] AC-6: 20 tests all pass under interpreter mode (bin/simple run)

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [-] 2-research (skipped) — 2026-05-18
- [-] 3-arch (skipped) — 2026-05-18
- [-] 4-spec (skipped) — 2026-05-18
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18: 20/20 tests pass in interpreter mode
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
Scaffolding task: create 4 source modules + 1 spec for portable SIMD/FP capability surface.

### 5-implement
Created files:
- src/lib/nogc_sync_mut/simd/numeric_caps.spl — TargetFamily enum, NumericCaps struct with capability facts
- src/lib/nogc_sync_mut/simd/cap_registry.spl — TargetSpec + CapRegistryEntry with derive() factory
- src/lib/nogc_sync_mut/simd/lowering_sel.spl — LoweringFamily, LoweringConfig, LoweringSelection
- src/lib/nogc_sync_mut/simd/fp_profile.spl — FpTier enum, FpProfile struct with per-arch factories
- test/unit/lib/simd/portable_simd_fp_spec.spl — 20 self-contained tests

### 7-verify
All 20 tests pass: 6 NumericCaps + 3 TargetFamily + 5 CapRegistryEntry + 5 LoweringSelection + 4 FpProfile.
Run: bin/simple run test/unit/lib/simd/portable_simd_fp_spec.spl

## Log
- 2026-05-18: All phases complete. 20/20 tests pass.
