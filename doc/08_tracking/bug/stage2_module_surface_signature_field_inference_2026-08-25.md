# Stage-2 cannot lower imported ModuleSurface signature arrays

Status: fixed in source; source admission advanced to a later independent
self-host crash.

## Exact evidence

- Compiler: admitted pure-Simple Stage 2, SHA-256
  `112a11f6e9e0076ff44e164aabaf14069aa51e91d2bc0f6af4076e59e55d7004`.
- Source: `/mnt/data/worktrees/simple-work-20260824` after expanding the sparse
  checkout to the complete tracked `src/lib` tree.
- Cache: `build/bootstrap/abnormality-source-stage3/x86_64-unknown-linux-gnu/native-cache`.
- Final log: `build/native_probe/abnormality-source-stage3-retry2.log`.
- Result after 1,428 cached files and `--timeout 600`: one failed file,
  `src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl`.
- Diagnostic: `cannot infer field type while lowering
  HirLowering.declared_imported_surface_signature_type: struct 'ModuleSurface'
  field 'signature_names'`.

A concrete local `val imported_surface: ModuleSurface = surface` rebind did not
change the diagnostic and was removed rather than retained as a workaround.
The subsequent definition audit proved the method was stale: `ModuleSurface`
no longer defines any `signature_*` fields, the referenced
`module_surface_signature_arrays_aligned` helper no longer exists, and the
method itself has no callers. The obsolete method was therefore removed.

## Resume plan

Owner: HIR field-access/type-preservation maintainer.

Reuse the existing cache with stub fallback disabled and the 600-second
per-file timeout. Do not delete successful cache entries. If the build exposes
a live caller that depended on the removed method, restore the behavior against
the current retained `ModuleSurfaceCallable` representation rather than
reintroducing fields removed from the schema.

Acceptance is a no-stub source-matched Stage-3 artifact followed by admitted
Stage 4; Rust or Stage-2 parser/check results are diagnostic only.

## Resolution evidence

The source-matched retry compiled all 2,179 selected artifacts after this dead
method was removed. No `ModuleSurface.signature_names` diagnostic recurred.
The first link attempt used a non-canonical broad `--source` invocation and is
not admission evidence. The subsequent canonical Stage-3 command completed its
687-file surface pass without diagnostics and reached MIR lowering, proving
this HIR blocker is resolved. That command then crashed independently with
SIGSEGV; see
`stage2_canonical_stage3_mir_lowering_segfault_2026-08-25.md`.
