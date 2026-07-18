<!-- codex-research -->
# Research: simd_fixed_and_scalable_vectors

## Goal

Audit the repo’s real SIMD state after `FixedVec` landed and `ScalableVec`
scaffolding was added, then define a first implementation slice that is
compatible with the shipped stdlib surface.

## Repo Audit

- `src/lib/nogc_sync_mut/simd/fixed.spl`
  - `FixedVec<T>` is the active fixed-width stdlib vector surface.
  - Construction uses runtime `lanes` rather than parser-level `FixedVec<T,N>`.
  - Alias helpers such as `vec4f_splat()` and `vec8i_from_array()` are already
    part of the compatibility surface.
- `src/lib/nogc_sync_mut/simd/scalable.spl`
  - `ScalableVec<T>` already exists as a real interpreter-visible type.
  - Core operations are present: construction, arithmetic, comparisons,
    reductions, masks, and explicit fixed/scalable conversion helpers.
  - The gap was primarily verification and documentation: tests still treated
    the surface as unreachable.
- `src/compiler/00.common/simd_types.spl`
  - IR already models both `FixedVecType` and `ScalableVecType`.
- `src/compiler/50.mir/mir_types.spl`
  - MIR already has `MirTypeKind.ScalableVec(element, min_lanes)`.
- `src/compiler/70.backend/backend/native/isel_riscv64.spl`
  - Native RV64 lowering still stops with `riscv_v_native_lowering_deferred`.
  - That guard is intentional and must remain stable until real RVV lowering is
    implemented.
- `doc/02_requirements/feature/portable_simd_fp_modules.md`
  - The selected requirements still describe scalable vectors as deferred phase-1
    work, which no longer matches the current language and stdlib trajectory.

## Mismatch Summary

The codebase had already moved to a dual-surface SIMD model:

- fixed-width vectors are real and tested,
- scalable vectors are real in the stdlib and MIR surface,
- backend-native scalable lowering is still deferred.

The outdated part was the documentation and the missing parity tests, not the
existence of scalable vectors themselves.

## First-Slice Policy

- Preserve `FixedVec<T>` as the active compatibility surface.
- Preserve back-compat aliases and helper constructors.
- Treat `ScalableVec<T>` as a supported language/stdlib surface in interpreter
  and MIR-visible flows.
- Keep native scalable lowering explicitly deferred with stable diagnostics.
- Do not make `FixedVec<T,N>` parser work a dependency of this landing.
