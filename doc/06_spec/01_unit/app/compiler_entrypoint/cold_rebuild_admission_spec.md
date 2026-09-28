# Target 6 cold graph rebuild admission

The executable scenario is
`test/01_unit/app/compiler_entrypoint/cold_rebuild_admission_spec.spl`.

1. Publish a schema-valid synthetic one-module V2 graph for SCV revision A.
2. Present revision B. Warm admission requires an explicit graph rebuild;
   explicit cold admission enters a pending state.
3. Read `CURRENT` again. It still names the prior complete graph, so a failed
   or interrupted cold build cannot replace it with a binding-only record.
4. Present unchanged revision A. The same graph remains bound.

This is policy and pointer-preservation evidence. A complete Target 6 pass
still needs typed graph publication after successful compilation and the
production performance matrix.

The no-stub native fixture
`test/fixtures/compiler/target6_cold_graph_admission_native_probe.spl`
also exercises the production entrypoint in a one-source Git worktree. It
passes seed, stale warm refusal, and explicit cold admission against the same
cache. The cold step verifies the new frozen source, empty warm compatibility
markers, an unchanged prior graph pointer, and clearing of pending authority
when a later warm retry fails.
