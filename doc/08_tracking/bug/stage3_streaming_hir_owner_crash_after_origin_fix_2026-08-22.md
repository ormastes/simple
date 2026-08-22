# Stage 3 streaming HIR owner crashes after export-origin convergence

Status: OPEN  
Priority: P0 bootstrap blocker  
Platform: aarch64-apple-darwin  
Observed: 2026-08-22

## Failure

The strict pure-Simple Stage 3 build exits with SIGSEGV immediately after the
streaming surface phase succeeds and HIR typechecking starts:

```text
[EXPORT-ORIGINS] fixpoint pass 2 complete changed=false
[EXPORT-ORIGINS] exit passes_run=2 changed=false
[BOOTSTRAP-PHASE] phase2:parse:done n_modules=0
[BOOTSTRAP-PHASE] phase3:hir_typecheck:start
Segmentation fault: 11
```

`n_modules=0` is intentional for the streaming lane: phase 2 stores the frozen
surface owner in `streaming_module_surfaces_owner` and clears `ctx.modules`.
The crash therefore lies at or immediately inside
`lower_and_check_streaming_surfaces_impl`, before its first HIR progress
receipt.

## Reproduction

Run the admitted low-memory bootstrap on macOS ARM64 with one worker and no
fallback:

```sh
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_HIR_EXPORT_ORIGIN_TRACE=1 \
sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --bootstrap-receipt=build/bootstrap/admission/stage4-scalar-fix.receipt \
  --backend=cranelift --mode=dynload --strategy=normal \
  --jobs=1 --progress --no-mcp
```

The preceding null dereference in
`module_surface_explicit_import_origin` is independently fixed by keeping its
loop-carried route selection scalar. This report tracks the next ownership
failure only.

## Investigation boundary

Inspect the native representation and receiver-field handoff for:

- `CompilerDriver.streaming_module_surfaces_owner`
- `CompilerDriver.streaming_surface_owner_ready`
- the call from `lower_and_check_impl` to
  `lower_and_check_streaming_surfaces_impl`
- `Option<ModuleSurfacesByName>.unwrap()` at the streaming HIR entry

Do not restore `ctx.modules`, disable streaming, permit seed fallback, or hide
the crash with a nil/default surface. The repair must preserve the retained
surface owner and fail closed on absence.

## Acceptance

1. A focused native reproducer reaches the first streaming HIR progress
   receipt with the retained surface count intact.
2. Strict Stage 3 completes with no seed fallback.
3. Stage 3 provenance/self-verification passes.
4. A regression test exercises the owner handoff under native execution.
