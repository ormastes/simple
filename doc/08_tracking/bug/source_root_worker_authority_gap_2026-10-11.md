# Native worker loses ordered source authority before closure resolution

Status: confirmed failure; no source repair in this evidence commit.

Producer `e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491`
contains selected-root tri-state lookup and direct Missing fallback. Actual
native builds still admit the default CUDA provider in two negative cases.

1. `test/fixtures/compiler/source_root_ambiguous_loader_probe.spl` uses explicit
   roots `test/fixtures/compiler/ambiguous_composition_overlay`, `src/plugins`,
   `src/compiler`, `src/lib`, `test/fixtures/compiler`, in that order. The loader
   produced no `SOURCE_ROOT_AMBIGUOUS` error, admitted the default selected
   module and its four CUDA implementation files, then parsed 178/350 modules
   before timeout 124. Rejection failed before the timeout.
2. `test/fixtures/compiler/cuda_disabled_selection_probe.spl` uses explicit
   roots `src/compositions/cuda_disabled`, `src/plugins`, `src/compiler`,
   `src/lib`, `src/os`, `test/fixtures/compiler`, in that order. Phase 1 completed
   with 507 physical sources; the default selected module and CUDA backend,
   port, mapper and PTX builder were present. The bounded build later timed
   out 124. No executable or linked-symbol exclusion receipt exists.

Both use LLVM, entry closure, one thread pinned to CPU 1, one-binary mode and
`SIMPLE_NO_STUB_FALLBACK=1`. The ambiguity bound was 120 seconds; disabled was
180 seconds. Evidence: `build/cuda-policy/ambiguous-e9e8-receipt.json`,
`source-ambiguous-frozen-e9e8-build.log`,
`disabled-selection-e9e8-receipt.json`, `disabled-selection-e9e8-build.log`.
An earlier ambiguity attempt was rejected for SCV snapshot-index drift because
the agent changed a separate fixture while the shared source root was being
snapshotted. It is retained separately and is not a resolver result.

Read-only source diagnosis identifies three gaps:

- `native_build_closure._nb_resolve_under_root` uses the legacy text wrapper;
  ambiguity becomes empty text and `_nb_resolve_segs` can select a later root.
- The worker loader sets `closure_source_roots = driver_inputs`. Input source
  files are not the original ordered `--source` authority. That ordered list
  must cross the admitted worker/options boundary explicitly.
- `closure_loaded_mods` skips validation before the selected-root lookup, so a
  default provider preloaded by the outer scanner can bypass ambiguity checks.

Required repair: propagate ordered admitted roots and their identity through
the outer closure/cache and worker contracts, preserve tri-state failures at
both boundaries, and validate authoritative ownership before loaded-name
shortcuts. Do not weaken SCV admission or restore a silent fallback. Re-run
these fixtures only after a changed producer, then qualify full disabled
bootstrap closure and linked symbols. Static PTX remains separately pending.
