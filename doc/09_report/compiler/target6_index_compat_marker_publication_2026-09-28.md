# Target 6 index compatibility marker publication (2026-09-28)

## Change

Entrypoint admission now publishes the producer, root generation, and variant
digest from an admitted V2 graph into the compiler's existing warm-route
compatibility fields. A binding-only generation clears all three fields, so
an earlier request in the same process cannot make a later binding look like
a graph. Publication failure rejects admission.

This is a bridge into the current driver interface. The production cold
publisher still creates a binding-only generation, so this change alone does
not activate the warm package route or satisfy Target 6 cutover.

## Native evidence

- Compiler: Stage2 pure-Simple binary at
  `build/bootstrap-target56/phase2-runtime-capsules/d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c/simple`.
- No-stub `host-gpu` entry-closure build of
  `test/01_unit/app/compiler_entrypoint_index_compatibility_spec.spl`:
  48 units compiled, 0 failed; executable SHA-256
  `f584aac1e83862a9d1efd241b782abb79f329a872c597b6cf0f101bbd1e2522c`,
  89,552 bytes. Execution: 1 example, 0 failures.
- No-stub `host-gpu` entry-closure build of a build-local probe calling
  `compiler_entrypoint_admit_v1`: 112 units compiled, 0 failed; executable
  SHA-256 `3d9619ba2eaff953452cc093c502212e919201b98a7404164cbfe1db2d8dfed2`,
  323,032 bytes. This is a compile/link check, not an admission runtime pass.

The full CLI Stage4 link remains blocked by optional provider symbols, so
compiler/lib/MCP/LSP checks and a production warm performance cohort remain
unqualified. No time or RSS improvement is claimed from these focused builds.
