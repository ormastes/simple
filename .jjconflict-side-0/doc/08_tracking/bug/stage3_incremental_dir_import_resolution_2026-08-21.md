# Stage-3 incremental directory import resolution (2026-08-21)

## Status

Reclassified as a downstream cascade symptom. The direct runtime-backed import
is retained as a defensive compiler hot-path route, but it was not the first
Stage-3 HIR failure.

## Evidence

The receipt-bound Stage-3 compiler completed all 954 streaming surface parses.
HIR lowering later reported four errors in
`src/compiler/80.driver/driver_build/incremental.spl`:

- unresolved name `dir_list` at the named `std.io_runtime` import;
- unresolved name `dir_create_all` at the same import.

The full log begins earlier with unresolved `FrontendAsmTargetSpec`, followed by
shared `Span`, `Type`, and `ProcessResult` failures. The directory errors cannot
serve as an independent first-cause diagnosis. The compiler fingerprint path
now imports the runtime-backed owner directly to avoid a compatibility-facade
hop without changing behavior.

## Next bounded action

Verify the named-over-glob callable dependency fix recorded in
`stage3_callable_dependency_named_glob_precedence_2026-08-21.md`. If directory
symbols remain unresolved after the imported-type cascade is gone, reopen this
record with the new first-cause log. Do not route fingerprint traversal through
`std.nogc_sync_mut.io.dir_ops`: its listing implementation shells out to `ls`.
