# HIR semantic pass transient scope: E-HIR-VISIT-UNHANDLED with `<unknown>` HirTypeKind (2026-11-24)

- **ID:** hir_semantic_pass_scope_dangling_hirtype_2026-11-24
- **Priority:** P1 (full-CLI Phase 4 bootstrap needs the workaround, ~57 GB HIR peak)
- **Status:** OPEN - root cause NOT pinned; diagnostics + per-pass bisect switch landed

## Symptom
With per-module transient scoping of the HIR semantic passes
(`driver_hir_pipeline_passes.spl`, `hir_semantic_pass_scope_enabled_v1`), the
representation-manifest walk (`representation_missing_manifest_observations_v1`
-> `walk_hir_block`/`walk_hir_param` -> `walk_hir_type`) aborts with
`E-HIR-VISIT-UNHANDLED: HirTypeKind variant <unknown>`, i.e. a garbage HirType tag.

## Workaround
`SIMPLE_HIR_SEMANTIC_PASS_SCOPE=0` (all passes unscoped; costs the memory the scoping saves).

## Static analysis (no build run)
Scoped passes: typecheck, safety_warn, any_escape, enum_contract,
representation_manifest, representation_bind. Only receipts (texts) and the bind
result (`[RepresentationDeclarationV1]`) are promoted; no pass writes HirType into
module/global state inside a scope. `RepresentationDeclarationV1` holds no HirType.
So the leading "HirType created in scope stored in long-lived state" hypothesis was
not confirmed in source. Remaining suspects: promotion of the bind result not
covering nested children (Span arrays, Option manifest) of the declarations that are
then written into `hir_modules`, or a runtime free of a walk-time allocation that the
module graph still references. Needs a run to decide.

## What this change does (diagnostic + bisect, not a root-cause fix)
- `SIMPLE_HIR_SEMANTIC_PASS_SCOPE_SKIP=<comma pass names>` runs only those passes unscoped
  (names above). Bisect with e.g. `=representation_bind` then `=representation_manifest`.
- `SIMPLE_HIR_SEMANTIC_PASS_TRACE=1` prints `[hir-pass-scope] trace pass=.. module=..` per
  scoped pass and `trace walk owner=.. symbol=..` per function in the representation walk;
  the last line before E-HIR-VISIT-UNHANDLED names the failing module and owner.
- Spec: `test/01_unit/compiler/80.driver/hir_pass_scope_skip_spec.spl`.

## Related memory docs reviewed
- `stage3_c_runtime_worker_memory_2x_2026-11-20.md`: fix already landed in source; skipped.
- `stage2_whole_program_mir_memory_growth_2026-11-01.md`: OPEN, launch-only workaround,
  not a small fix; skipped.
