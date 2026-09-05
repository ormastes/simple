# Stage 2 stale HIR const-fold import

**Status:** Fixed on isolated work branch; protected integration pending  
**Observed:** 2026-08-26  
**Fix commit:** `2df527fe598`

## Root cause

Commit `828bdb1a152` intentionally deleted the discarded no-op HIR constant-fold
pass and routed resolved HIR directly. Snapshot commit `4edef8fab8e` later
resurrected only the driver import and call, without restoring the deleted
module. Stage 2 therefore failed E1034 while compiling
`driver_hir_pipeline_lowering.spl`.

The module resolver is not at fault. Two independent reviews confirmed that
`compiler.semantics.*` uses the canonical numbered compiler mapping and that
neighboring imports resolve through the same mechanism.

## Fix and evidence

- Removed the stale import and `run_const_fold_pass` call.
- Routed `resolved_module` directly into both bootstrap collections.
- Repaired the existing quarantine spec's unsupported negated-string matcher.
- Focused quarantine spec: PASS, 2/2.
- Working and staged direct-environment guards: PASS.
- One bounded receipt-free Stage 2 retry passed the former E1034 boundary.

The retry did **not** admit Stage 2. It later failed at link on independent
unresolved symbols including `aspect_module_identity_index`,
`safetychecker_flag_static_reference`, `mir_type_probe_text`,
`MirToLlvm.emit_panic_trap_ir`, and `interp_enum_discriminant_raw`. Those are
separate failure roots and are not evidence against this focused correction.

## Integration policy

Submit this exact fix through the protected `main` integration authority. If a
release-line comparison proves the stale references are also present there,
backport the integrated fix through a separate release-targeted work branch
with renewed evidence. Never repoint or merge the whole release branch into
`main`.
