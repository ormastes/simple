# HIR unit specs run longer than 300 s (hang) on the seed

- **Found:** 2026-11-06 during the W2b before/after directory runs (data plan W2b).
- **Seed:** a Rust seed built from release `4d7dda0c117`, which includes the W2a change.
- **Tree:** the unmodified base `4d7dda0c117`, so the hangs are pre-existing and do not come from W2b.
- **Specs:** each ran past 300 s with no output and was killed. Before W2a's seed rebuild, `module_surface_semantic_projection_spec` also ran past 12 min.
  - `test/01_unit/compiler/hir/module_surface_semantic_projection_spec.spl`
  - `test/01_unit/compiler/hir/field_index_erased_receiver_spec.spl`
  - Only these two hit the 300 s reaper in that run, which covered 139 of the directory's 287 specs before it was stopped.
- **Repro:** `simple test test/01_unit/compiler/hir/module_surface_semantic_projection_spec.spl`. The `[route] mode=interpreter` line prints, then the process stays busy with no further output.
- **Expected:** a verdict, or a failing assertion, within the runner's per-file budget. A hang is a defect: it blocks every directory-lane run of `test/01_unit/compiler/hir`.
- **Next step:** run each spec with `SIMPLE_JIT_STRICT=0` and a stack sampler to find the looping pass. Whether the cause is the seed interpreter or the spec's own fixture size is not known yet.
