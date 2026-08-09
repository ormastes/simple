# Stage-2 seed incremental bootstrap silently spins before first artifact

**Status:** inconclusive bounded attempt — no Stage-2 admission, Stage-3,
Stage-4, ML-KEM coverage, or GPU runner evidence may cite this run.

## Reproduction

From the repository root on 2026-08-08:

```sh
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --backend=cranelift --jobs=1 \
  --output=build/bootstrap-mlkem-stage2-20260808 \
  --progress=build/bootstrap-mlkem-stage2-20260808/progress.log
```

This is intentionally incremental-only: it reuses the existing Rust seed,
does not invoke Cargo, and does not deploy `bin/simple`.

## Observed evidence

The Stage-2 seed command was the canonical entry-closure build of
`src/app/cli/bootstrap_main.spl` over `src/compiler`, `src/app`, and `src/lib`.
For 5 minutes 32 seconds it consumed one core at ~100%, grew to roughly 400 MB
RSS for the process tree, wrote **zero** bytes to `stage2-native-build.log`,
wrote no incremental-cache file, and produced no Stage-2 binary. The bounded
safety stop sent SIGTERM; the progress receipt records `milestone=exit-143`.

The output tree and its progress receipt are retained at
`build/bootstrap-mlkem-stage2-20260808`. The run was interrupted before a
terminal compiler result, so five minutes of CPU-heavy first-pass closure
loading alone does **not** prove a loop. It only proves that the pre-emission
portion has no useful progress signal in that seed version. Commit
`b73786ff941` adds a pure-Simple FFI-boundary heartbeat; a later, longer,
timeout-bounded run must establish whether the work completes or stalls inside
the seed builder.

## Impact

Without a fresh admissible Stage-2 compiler, the project cannot produce the
self-hosted Stage-3/Stage-4 CLI required for measured 346-outcome ML-KEM
coverage or provenance-bound CUDA/Vulkan/Metal full-operation runners.
