# SStack State: portable-simd-fp-phase2

## User Request
> Portable SIMD FP Modules Phase 2 — Fix Wave 2 dispatch gap. Phase 1 SIMD modules exist; Phase 2 needs dispatch infrastructure for wider vector widths and fallback paths.

## Refined Goal
> Add pure-Simple scalar fallback implementations for i32x4/i32x8 arithmetic (add/sub/mul) and f32x8/f64x4 width decomposition, plus a width-dispatch layer that selects scalar fallback vs hardware SIMD based on runtime tier detection. This closes the Wave 2 dispatch gap where `rt_simd_add_i32x4` etc. are declared as externs but have no interpreter dispatch arm — consumers can use the fallback paths instead of trapping on the FFI dispatcher.

## Task Type
feature

## Acceptance Criteria
- [x] AC-1: Pure-Simple scalar fallback functions for i32x4 arithmetic (add/sub/mul) that operate on Vec4i fields without calling rt_simd_* externs
- [x] AC-2: Pure-Simple scalar fallback functions for i32x8 arithmetic (add/sub/mul) that operate on Vec8i fields without calling rt_simd_* externs
- [x] AC-3: Width-dispatch wrapper class that selects scalar fallback vs SIMD tier based on runtime detection, defaulting to scalar when externs are unavailable
- [x] AC-4: f32x8 width decomposition fallback that decomposes Vec8f operations into two Vec4f operations for non-AVX hosts
- [x] AC-5: f64x4 width decomposition fallback that decomposes Vec4d operations into scalar f64 arithmetic for non-AVX hosts
- [x] AC-6: New module exported from `simd/mod.spl` so consumers can `import wave2_dispatch`
- [x] AC-7: All new code passes `bin/simple build lint` syntax check with no errors

## Cooperative Providers
- Codex: not needed
- Gemini: not needed (no UI)

## Architecture Style
**MDSOC-only** (stdlib module, no ECS layer).

## Coordination Notes
- Prior phase2 work in `.spipe/portable_simd_fp_modules_phase2/` covered registry threading and MIR scaffolding (completed 2026-05-02)
- This pipeline addresses the distinct runtime dispatch gap surfaced by T1 during ChaCha20 vectorization
- Does NOT modify `simd.spl` extern declarations or Rust runtime files

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-19
- [x] 2-research (Analyst) — 2026-05-19
- [x] 5-implement (Engineer) — 2026-05-19
- [ ] 7-verify (QA) — pending
- [ ] 8-ship (Release Mgr) — pending

## Phase Outputs

### 1-dev
**Date:** 2026-05-19
**Type:** feature (Wave 2 dispatch gap fix)
**Scope:** Pure-Simple fallback paths + width dispatch layer in `src/lib/nogc_sync_mut/simd/wave2_dispatch.spl`
**Acceptance criteria:** AC-1..AC-7 above

### 2-research
**Date:** 2026-05-19
**Findings:**
- `rt_simd_add_i32x4`, `rt_simd_sub_i32x4`, `rt_simd_mul_i32x4` and i32x8 siblings are declared as externs in `simd.spl` (lines 375-439) but have zero dispatch arms in `src/runtime/` or `src/compiler_rust/`
- T1 (ChaCha20) worked around this with direct field arithmetic on Vec4i fields
- Existing dispatch infrastructure: `variant_dispatch.spl` (DispatchRoute/Table/RuntimeSelector/CodegenTierRouter), `lowering_sel.spl` (LoweringFamily/Config/Selection), `host_cpu_config.spl` (TierFallbackChain), `vlen.spl` (VLen)
- Solution: promote T1's field-arithmetic pattern to reusable scalar fallback functions + a width-dispatch wrapper

### 5-implement
**Date:** 2026-05-19
**Files created:**
- `src/lib/nogc_sync_mut/simd/wave2_dispatch.spl` — scalar fallback + width dispatch module
**Files modified:**
- `src/lib/nogc_sync_mut/simd/mod.spl` — added `import wave2_dispatch` + exports
