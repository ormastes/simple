# core-C runtime archive build flakes with rename ENOENT, silently degrading to a 28x runtime

- **Filed:** 2026-07-26
- **Status:** OPEN — reproducible, trigger NOT root-caused
- **Component:** `src/compiler_rust/compiler/src/pipeline/native_project/{tools.rs,config.rs}`
- **Severity:** medium (flaky CI; the silent-degradation half is fixed, the race is not)

## Symptom

`build_c_runtime_library` compiles the core-C runtime sources one at a time into
`<repo>/.simple/native-objects-XXXXXX/core_c_runtime/`. Intermittently one clang
invocation fails:

```
error: unable to rename temporary
  '<repo>/.simple/native-objects-NJkdgG/core_c_runtime/runtime_native-9dd12f74.o.tmp'
  to output file
  '<repo>/.simple/native-objects-NJkdgG/core_c_runtime/runtime_native.o':
  'No such file or directory'
```

A *different* source file fails on each occurrence (`runtime_native.c`,
`runtime_simd_dispatch.c`, ...), so it is not source-specific.

Until this was fixed (see *Fixed* below) the failure was silent: the lane fell
through to `find_runtime_library()`, linked a generic runtime roughly 28x
larger, and the only visible symptom was a size assertion far from the cause:

```
hello too large: 3630824                        (budget 128_000)
startup-only simple_lsp_mcp too large: 3684200  (budget 128_000)
```

Affected tests (both in `pipeline::native_project::tests`):
- `test_core_c_lane_builds_and_runs_hello_world_small`
- `test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source`

## Reproduction

```bash
cd src/compiler_rust
cargo test -p simple-compiler --lib -- --exact --nocapture \
  pipeline::native_project::tests::test_core_c_lane_builds_and_runs_hello_world_small
```

Observed **2 failures in 6 runs** with no observer attached. **0 failures in 22
runs** with any observer (`strace -f`, or a `ps`-sampling watcher). The failure
is timing-sensitive and disappears under observation — plan any further
investigation around in-process probes, not external tracing.

Set `SIMPLE_NATIVE_BUILD_RUST_TRACE=1` to get the directory state at the moment
clang fails (probe added in `tools.rs`, default off).

## Ruled out — do not re-investigate without new evidence

| Hypothesis | Evidence against |
|---|---|
| External sweeper / cron / `*.tmp` cleaner | None exists; no crontab, no systemd timer but `launchpadlib-cache-clean` |
| `scripts/resource/disk-retention.shs` | Only scans `build/`, never `.simple/`; has age + in-use guards |
| Anything deletes the dir mid-build | `strace -f` on a captured failure: the ONLY `unlinkat`/`rmdir` of the staging dir is at teardown, AFTER the test already failed (`si_status=101`) |
| Concurrent clang sharing an output `.o` | `ps` sampling found zero duplicate `-o` targets; `concurrent=2` was the clang driver plus its own `cc1` child |
| cargo test parallelism | Reproduces with a single test (`0 passed; 1 failed`) |
| Disk / tmp pressure | btrfs, 1.3T free; `/tmp` cleanup is 30d |
| Watchdog (`compiler/src/watchdog.rs`) | Memory limit defaults to 0 (disabled); zero `[watchdog]` lines in any failing run |
| In-process race in the build path | `link_objects` runs once per build (`mod.rs:1032`); `build_c_runtime_library` runs on the link thread after all rayon work joins; nothing deletes `.o` files (`ar rcs` does not remove inputs; no `read_dir`+delete over `build_dir`) |
| `config.rs` double-build of the same dir (sites ~346 and ~368) | Both CAN run in one call, but strictly sequentially on one thread; an overwrite yields clobber semantics, never a rename ENOENT |
| External deleter of `<repo>/.simple` | 13 orphaned `native-objects-*` dirs from Jul 22-25 were still present on Jul 26 at 03:06. Any sweeper — or a concurrent `--clean` build with `--cache-dir <repo>/.simple` — would have removed those too |

## Current state of the evidence

Both structural explanations are eliminated: there is no in-process race, and
nothing external removes the staging directory. The directory demonstrably
survives until teardown, so the ENOENT concerns the **source `.tmp`**, not the
destination directory — but no deleter of that `.tmp` has been identified.

The trigger is unexplained. It is deliberately NOT papered over with a retry
loop: a retry would hide an unexplained failure rather than fix it.

## Fixed (separately, in this same change)

The *silent degradation* is fixed even though the race is not. In a source
checkout a failed core-C archive build is now a hard error instead of a silent
fallback to a generic runtime, so the next occurrence names itself at the point
of failure. Gated on `find_core_c_runtime_source_root().is_some()` so that a
deployed compiler with no `src/runtime` checkout still legitimately uses a
prebuilt archive.

## Follow-ups

1. **Root-cause the `.tmp` disappearance.** Next step is an in-process probe
   (external tracing suppresses the race). Capture `read_dir(build_dir)` plus
   the `.tmp` file's existence at the instant clang reports failure.
2. **Fallback asymmetry.** `config.rs` ~354 pushes whatever `find_runtime_library()`
   returns *unfiltered*, while the structurally identical fallback at ~371-372
   filters with `runtime_archive_has_bootstrap_cli_symbols`. That unfiltered path
   is the mechanism by which the oversized archive got selected. Not changed here:
   with the hard error in place, ~354 is only reachable when no core-C sources
   exist (deployed compiler), where an unfiltered prebuilt archive is the correct
   result — adding the bootstrap-CLI filter there could break that supported case.
   Revisit only with evidence.
3. **Staging dirs leak.** 13 `native-objects-*` dirs accumulated in `.simple/`
   over 4 days because the success path calls `TempDir::keep()`. Unbounded growth;
   `disk-retention.shs` does not cover `.simple/`.
