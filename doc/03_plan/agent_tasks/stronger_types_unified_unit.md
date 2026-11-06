# Agent Task Breakdown — Stronger Types (wave 1)

**Date:** 2026-11-05
**Lane:** `work/simple-hardening-release-20261013` (worktree `D:/dev/simple-rt`, base `origin/release/1.0.0`)
**Merge owner:** this session (kimi). **Final reviewer:** this session, normal-capability review before merge.

## Lane A — P1 canonical unit metadata (coder subagent)

- Scope: `src/compiler/10.frontend/core/types.spl` (canonical decl pool), `src/compiler/30.types/units/unit_registry.spl` (role-aware entries, dual-pool build, `entry_count`), delete dead 16-slot `CustomPrimitiveRegistry` in `src/compiler/30.types/custom_primitive_info.spl` (keep `PrimitiveTypeResolver`/`PrimitiveAbiNames` if referenced).
- Contract: `unit_decl_register(full_name, role, short_symbol, underlying_tag, alias_of) -> i64`; `UnitEntry` gains `role: text`, `alias_of: text`; legacy newunit entries build with role `"nominal"`; `unit_registry_build()` consumes both pools; `entry_count()` added.
- Sidecars: N/A (single-file-scope compiler internals). Reviewer: session.

## Lane B — P3 effect unknown/completeness (coder subagent)

- Scope: `src/compiler/20.hir/hir_types.spl` (`EffectKind.Unknown`), `src/compiler/30.types/type_infer/inference_effects.spl` (fail-closed unknown, completeness flag), `src/compiler/30.types/type_infer_types.spl` + `type_infer/context.spl` (`current_function_effects_complete`), unit spec `test/01_unit/compiler/semantics/effect_inference_unknown_spec.spl`.
- Out of scope (deferred, recorded): latent lambda effects on type schemes; Throws payload join semantics change (audit only); `param_effects/` and `type_system/effects.spl` unification.
- Sidecars: N/A. Reviewer: session.

## Rules for both lanes

- No commits; session owns landing. Do not run builds or `bin/simple` (bootstrap in progress elsewhere).
- Match file idioms; files stay under 800 lines; no stubs — anything not finished stays out of the diff.
- Report: files changed, APIs added, risks, and exactly which existing specs could be affected (for the post-bootstrap verification pass).
