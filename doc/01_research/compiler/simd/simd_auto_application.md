# Research: SIMD / Matrix / Bit-ISA Auto-Application

Date: 2026-05-03
Owner: Codex

## Scope

This note consolidates the local compiler state for automatic application of:

- MIR auto-vectorization for existing scalar loops
- portable bit-idiom recognition and ISA-aware lowering
- matrix-kernel recognition for dot/outer-product style loops

It supplements, and does not replace:

- `doc/01_research/auto_vectorize_survey_2026-05-02.md`
- `doc/01_research/compress_simd_patterns_2026-05-02.md`
- `doc/01_research/cipher_simd_patterns_2026-05-02.md`
- `doc/05_design/simd_auto_vectorize_design.md`

## Current local state

- `src/compiler/60.mir_opt/mir_opt/auto_vectorize.spl` already has structural matchers for elementwise and reduction loops plus a scaffolded rewrite path.
- `src/compiler/60.mir_opt/mir_opt/auto_vectorize_codegen.spl` already emits vector-loop scaffolding with MIR intrinsics rather than hard backend opcodes.
- `src/compiler/70.backend/feature_caps.spl` already provides per-target idiom support and preferred vector width hints.
- `src/compiler/70.backend/lowering/intrinsic_lowering_{x86,aarch64,riscv}.spl` already route crypto/CRC/CLMUL intrinsics through target capability gates.

## Gaps before this change

- auto-vectorize rewrite gating was effectively add-only
- elementwise FP loops were conservatively tied to `fast_math` even when no reassociation occurred
- vector-width choice was still hardcoded in the pass rather than routed through target capability helpers
- there was no shared feature-class view for fixed-width SIMD, scalable SIMD, bitmanip, crypto, and matrix planning
- portable bit/matrix intrinsic families were not named centrally in MIR
- matrix-kernel recognition did not exist in the MIR optimizer

## What landed in this turn

- Added canonical MIR intrinsic names for:
  - rotate-left/right
  - popcount
  - clz/ctz
  - bswap
  - bitreverse
  - generic crypto clmul
  - matrix dot / outer-product / FMA kernel
- Extended `TargetIdiom` and added `TargetFeatureClass` plus helper queries for:
  - fixed-width SIMD
  - scalable SIMD
  - bitmanip
  - crypto
  - matrix
- Added preferred-lane-count helpers derived from backend capability width instead of hardcoded lane counts.
- Extended auto-vectorize recipes with index/store metadata.
- Added matrix-kernel structural recognition for dot/outer-product style inner loops.
- Broadened the phase-1 elementwise rewrite gate to:
  - add
  - sub
  - mul
  - xor
- Removed the `fast_math` gate for elementwise FP loops. `fast_math` remains relevant for reductions and reassociation-sensitive transforms.

## Remaining gaps

- no full backend byte lowering yet for the new scalar bitmanip intrinsic families
- matrix-kernel recognition currently logs recipes only; it does not yet emit dedicated matvec/dot/FMA MIR rewrites
- loop splicing is still scaffold-first and not yet a fully general CFG surgery path
- function-level source attributes like `#[simd(enable)]` are not wired end-to-end in this turn

## Recommended next implementation wave

1. Lower portable bitmanip intrinsics through x86/AArch64/RISC-V backend routers.
2. Teach vector-loop codegen to emit widening/reduction forms for dot-product kernels.
3. Add target-triple plumbing into MIR auto-vectorize so lane selection uses real compilation targets instead of the default planning profile.
4. Add frontend-to-MIR propagation for `#[simd(enable)]`, `#[simd(disable)]`, and `#[simd(prefer_scalable)]`.
