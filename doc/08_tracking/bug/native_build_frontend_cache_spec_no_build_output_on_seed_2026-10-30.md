# native-build frontend-cache spec: seed native-build writes no output or cache (2026-10-30)

Status: open
Area: native-build driver / frontend parse cache; spec
`test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl`

## Symptom

Host: macOS arm64, Rust seed `src/compiler_rust/target/release/simple` (built 2026-10-30), `release/1.0.0`.

- Spec with `bin/simple test --all <spec>`: 5 of 5 examples fail. The cold build stores 0 entries
  (`expected 0 to equal 3`), the summary checks are false, and the corrupt-entry example indexes an
  empty list.
- By default the spec's builds are refused by the host memory guard:
  `error: build refused: 8899 MiB of RAM/commit headroom free, below the 24576 MiB reserve
  (SIMPLE_BUILD_MEMORY_RESERVE_BYTES)`. The spec never surfaces this; it only sees exit codes and
  missing files.
- With the guard lowered for that run (`SIMPLE_BUILD_MEMORY_RESERVE_BYTES=4294967296`), a direct
  `SIMPLE_FRONTEND_CACHE_DIR=<dir> bin/simple native-build --source <fixture> --entry-closure
  --threads 2 --cache-dir <c> --entry <fixture>/main.spl --output <out>` **hangs**. Two runs
  both hit a 1500 s timeout (exit 124) after their last log write about a minute in. It writes
  no `<out>` binary, no `<dir>` frontend cache directory, and no `[frontend-cache] hits=… misses=…
  parses=…` summary line. The log is only import/export warnings.
- The whole spec under the lowered guard exceeds the runner's 900 s per-file cap.

## Expected format change (prepared, not landed)

The cache now publishes packed `.spab` artifacts by default:
`<dir>/artifacts/v1/<algo>/<d2>/<digest>-<calgo>-<cdigest>.spab` (`frontend_spab_cache_v1.spl`,
`flat_pool_packed_v1.spl:module_artifact_path_v1`). `.fpc` is only the fallback when the packed
store is refused. Branch `work/fe-cache-spec-spab-20261030` (commit `9f601cda366`) updates the spec
to match. It walks the cache dir recursively for `.spab`, requires zero `.fpc` on a cold build, and
truncates the binary entry by bytes in the corruption case. It cannot be verified until native-build
on this lane produces output again, so it is not merged.

## Next steps

1. Find where seed `native-build` stalls on this 3-module fixture (attach lldb to the hung
   process). It never stores to the frontend cache dir (`frontend_parse_cache_dir()`, from `SIMPLE_FRONTEND_CACHE_DIR`). Check whether it routes to the pure-Simple driver or the
   `native_project` pipeline, and why that path returns success with no artifact.
2. Make the spec report a memory-guard refusal (or set a test-scoped reserve) instead of failing on
   missing files.
3. Then merge the spec branch above and confirm 5/5.
