# SIMD / Bit-ISA Sync Readiness — 2026-05-04

Scope: follow-up readiness pass for the feature-only SIMD / matrix / bit-ISA sync.

## Confirmed Current State

- Generic MIR pattern dispatch is now multi-arch (`TargetCapsKind`) rather than x86-only.
- SSH sync is blocked by GitHub public-key auth, not by local networking.
- The worktree contains substantial unrelated dirty state and must be split before a feature-only commit.

## Documentation Corrections

- `doc/04_architecture/security_ext_optimization_layer.md` previously described the pattern-idiom pass as x86-only and still sharing the `"vectorization"` dispatch key. That is now stale against the current implementation.
- Older AES readiness notes should be read narrowly:
  - SIMD AES-NI extern wiring still has open/stale tracking notes.
  - The scalar/block/TLS AES runtime and interpreter paths are implemented and registered.
- Older `[u8]` AES interpreter blocker notes are stale against current interpreter code, which now accepts both `Int` and `UInt` byte elements.

## Confirmed Intentional Follow-On Blockers

- x86 generic `bit_clz` / `bit_ctz` still intentionally return `no-cap` pending `lzcnt` / `tzcnt` capability modeling and zero-input policy.
- AArch64 generic `bit_popcount` still does not lower through the portable intrinsic-lowering path, even though native ISel has a concrete scalar fallback.
- `matrix_*` idioms are still recognised but intentionally return `unimplemented`.
- Masked / predicated MIR ops remain incomplete.
- Reduction vectorization remains partial.
- Bulk-copy SIMD remains blocked on array-layout/runtime prerequisites.

## Sync Guidance

- Keep the feature-only sync bounded to the MIR-opt / feature-cap / matching-spec slice.
- Do not expand this sync to matrix lowering, masked SIMD, reductions, or bulk-copy follow-up work.
