# Stage-2 sanity rejects every self-hosted candidate: SCV snapshot entry collects zero sources (2026-10-22)

**Status:** OPEN — blocks all Stage-2+ bootstrap on `release_phase3` (observed at `84841547934`).
**Impact:** `bootstrap-from-scratch.sh --full-bootstrap` cannot pass the Stage-2
frontend sanity; the Stage-2 binary is rejected, Stage 3/4 unreachable.
**Severity:** release-blocking for the phase-4 full-CLI goal.

## Symptom

Stage 2 native build succeeds (`1482 compiled, 0 cached, 0 failed`, 946 s), then
the wrapper's pinned frontend sanity fails both passes:

```
error: compiler entry 'src/compiler/bootstrap_admission/p2_add.spl' collected zero source files:
  the entry must be a path to a .spl file ... and the path is resolved relative to the current working directory
candidate_frontend_smoke: p2_add-build failed (raw rc=1)
bootstrap-sanity-error: version_status=0 version_output=simple-bootstrap 1.0.0-rc.1 unsupported_status=1 frontend_status=1 candidate_unchanged=true
```

Evidence set (lane attempt 3, 2026-10-22 ~09:16):
`.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-sanity.env.frontend-{driver,failure}.log`,
rejected binary preserved at
`.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected`.

## Reproduction (no lane required)

With the SCV inventory present (`build/scv/source-inventory/CURRENT`, published by
the sanity's own scv_prime step — i.e. the failure is inherent to the sanity flow,
not this checkout's state):

```
SIMPLE_LIB="$PWD/src" SIMPLE_BOOTSTRAP=0 timeout 60 \
  .simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected \
  native-build --backend llvm --runtime-bundle core-c-bootstrap --entry-closure \
  --entry src/compiler/bootstrap_admission/p2_add.spl \
  --cache-dir /tmp/repro-cache --mode one-binary --output /tmp/repro-p2_add.exe
```

fails in ~5 ms at `phase 1 load_sources`. The same command against the Rust seed
(`bin/simple`, tracked rc.1 binary) passes load_sources and compiles.

## Evidence chain

1. `SIMPLE_COMPILER_TRACE=1` shows the pipeline received ONE input, rewritten to a
   snapshot path:
   `phase1:load_sources:input:start index=0 path=D:/dev/simple/build/scv/snapshots/scv-revision-v1-28f7afe6.../src/compiler/bootstrap_admission/p2_add.spl`
   then `input:done index=0 loaded=0 total=0` → zero-source gate fires
   (`src/compiler/80.driver/driver_source_pipeline_loading.spl:950-951`).
2. `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_SCAN_PHASES=1` shows the scan itself RAN for
   the snapshot path: `read:start` → `read:done` → `imports:done` →
   `siblings:done` → `cached_scan:done` → `closure_node:scanned`, then
   `cached_scan:hit` on rescan. So `_driver_cached_entry_source_scan`
   (`driver_source_loading.spl:825`) completed, yet
   `_driver_collect_explicit_compiler_source` (`driver_source_loading.spl:1662`)
   still yielded zero sources — i.e. after `read:done` the collected content was
   empty or the alias list came back empty **only in the self-hosted binary**.
3. The snapshot file exists, is a plain 487-byte ASCII file, and the SEED compiles
   the identical snapshot path successfully:
   `bin/simple compile --format=smf D:/dev/simple/build/scv/snapshots/.../p2_add.spl`
   → `Compiled ... -> t4.smf`. The candidate's own `compile --format=smf` on the
   same absolute snapshot path fails identically at load_sources.
4. p2_add.spl has NO imports, so import-closure resolution cannot explain zero
   aliases; the entry file itself is what fails to materialize as a SourceFile.
5. The rewrite is conditional on `SIMPLE_PACKAGE_INDEX_COLD_INIT` (set in-process
   by the probe) plus `SIMPLE_SCV_SNAPSHOT_ROOT` (set by the native-build
   entrypoint: `src/app/compiler_entrypoint/source_authority.spl:175` and
   `src/app/cli/native_build_warm_receipt.spl:383`), executing
   `driver_source_pipeline_loading.spl:343-392` →
   `native_cold_entry_snapshot_path_v1` + `phase_compatibility_existing_artifact_io_v1`
   admit the snapshot copy, so `cold_entry_input = admitted.canonical_path`.

## Localization

- Rewrite: `src/compiler/80.driver/driver_source_pipeline_loading.spl:343-392`.
- Zero-source gate: same file, lines 950-953.
- Scan that returns empty/alias-less for the snapshot path ONLY under the
  self-hosted binary: `src/compiler/80.driver/driver_source_loading.spl:825-870`
  (`_driver_cached_entry_source_scan`) and `:1662-1670`
  (`_driver_collect_explicit_compiler_source`).
- Suspect: a self-hosted-only behavioral difference in the sosix file-read layer
  or the module-identity/alias path for `build/scv/snapshots/...` paths
  (`_driver_physical_module_identity`, `driver_admitted_epoch_normalize_v1`-style
  normalization). The admitted-epoch read path was checked and excluded: with an
  active epoch and no task, load_sources fails loudly at
  `driver_source_pipeline_loading.spl:206-208`, which is NOT the observed error.

## Notes for the fixing lane

- The sanity is DESIGNED to create this state (scv_prime publishes the inventory,
  then the p2_add probe re-runs the candidate, which rewrites to the snapshot), so
  no in-lane workaround exists; the candidate must read snapshot paths correctly.
- Rebuild cost per fix attempt: Stage-2 native build ~16 min + lane overhead;
  the repro above gives a 5-second signal without a lane.
- Seed comparison is meaningful only with identical env: the seed's JIT demotion
  on the full CLI (`bin/simple`) prints jit-fallback noise but does pass
  load_sources for both the working-tree and snapshot entry paths.
