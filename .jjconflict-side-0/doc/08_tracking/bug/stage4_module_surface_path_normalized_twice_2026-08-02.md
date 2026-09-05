# Stage 4 module-surface builder normalizes every source path twice

## Status and claim

FIXED IN SOURCE — claimed by `stage4_perf_profile` on 2026-08-02. The owned
surface is the ModuleSurfaceBuilder path API and its Phase-2 callers. The
active Stage-4 closure agent confirmed it is not editing `module_surface.spl`.

## Measured reproduction

The retained Stage-4 trace reports 2,103 logical closure sources and 1,422
unique physical sources. For every logical source, both production builders do:

1. `builder.has_path(source.path)`, which calls
   `module_surface_canonical_path`; then
2. `builder.add_parsed(...)` or `builder.add_alias(...)`, which calls the same
   normalization again for the identical path.

Therefore the observed closure executes exactly 4,206 canonicalizations where
2,103 are sufficient. Each pass performs absolute-path resolution, separator
replacement, split, parent-component slicing, and join. On the no-GC bootstrap
tier, the text intermediates are not transient-owned, so the redundant pass is
both CPU work and retained memory.

The same duplication exists in `module_surfaces_from_modules`, affecting
non-streaming tests and tools.

## Repair and acceptance

Add an explicit canonical-path builder API. Each caller computes the canonical
path once, uses it for the membership decision, and passes the same value to
the selected insert/alias operation. Keep path-taking wrappers for compatibility
but make their single normalization explicit.

- Production source contract proves one normalization per loop and canonical
  APIs for membership plus mutation.
- Exact alias behavior still maps two module names for one physical source.
- Adjacent `\\` and `/` separators canonicalize to the same physical source.
- A same-path alias with different content continues to fail closed.

This bounded repair does not claim to solve parser-string ownership, promoted
AST declaration graphs, or serial Phase-2 execution.

## Verification

- Measured call-count reduction for the retained 2,103-source closure:
  4,206 path normalization calls to 2,103 (50%).
- Canonical-once source contract: 2/2 PASS.
- Module-surface resolver, separator alias, conflicting-content regressions:
  21/21 PASS.
- Optimizer analysis completed for both changed pure-Simple compiler files.
- Direct environment-runtime guards PASS for working and staged scopes.
