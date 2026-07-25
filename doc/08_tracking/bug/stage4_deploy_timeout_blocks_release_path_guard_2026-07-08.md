# stage4 deploy timeout blocks direct release-path guard

Date: 2026-07-08
Status: open
Owner: bootstrap/deploy lane

## Summary

The source fix for the CLI self-exec guard is present in `src/app/io/cli_ops.spl`:
`_cli_is_current_exe()` now compares candidates with `/proc/$PPID/exe` so the
shell helper checks the parent Simple process instead of `/bin/sh`.

The deployed `release/x86_64-unknown-linux-gnu/simple` binary still carries the
old code because the deploy rebuild did not finish.

## Reproduction

Direct release invocation crashes before user code:

```sh
SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple run /tmp/simple_native_row_probe.spl --mode=interpreter --clean
```

GDB backtrace from the failing binary:

```text
startup.launch_metadata.startup_normalize_program_args
io___CliCommands__run_commands__cli_run_file
io___CliCommands__handler_commands__cli_handle_run
cli___CliMain__main
```

The same probe succeeds through `bin/simple` after source resolution because the
source-level guard returns no delegate driver.

## 2026-07-13 isolated-worktree recheck

`release/x86_64-unknown-linux-gnu/simple` in the isolated host-GPU worktree is
a pure-Simple artifact, not the Rust seed, but it still predates the startup
fix. `run examples/01_getting_started/hello_native.spl` reproduces the
`startup_normalize_program_args` crash. Even a one-thread cached Hello World
`native-build` exits 139 in `rt_env_set`: GDB shows `SIMPLE_OS_LOG_MODE` paired
with the invalid value pointer `0x12`. The shared checkout is a separate state:
its deployed `bin/simple` still points to a Rust seed and emits the mandatory
seed warning.

The QEMU runner and host-GPU wrapper now fail closed on seed provenance and
abnormal bounded native-build parser probes. Those guards prevent stale output
from being accepted, but they cannot replace the required compiler redeployment.

## Deploy attempts

Both deploy attempts reached stage4 and failed to produce a new
`build/bootstrap/full/x86_64-unknown-linux-gnu/simple`:

- `sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy --no-mcp --jobs=min`
  was terminated after roughly 30 minutes with the stage4 native-build worker
  still CPU-bound and no new output.
- `timeout --kill-after=10s 1800s sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy --no-mcp --jobs=half`
  timed out after 30 minutes. Stage3 still failed with exit 139, the wrapper
  fell back to the seed for stage4, and the stage4 worker stayed CPU-bound
  without writing a new full CLI binary.

Worker stderr only reported:

```text
warning: failed to initialize runtime provider DynamicPath(".../src/compiler_rust/target/bootstrap"): load error: ... cannot read file data: Is a directory; falling back to static
```

## Impact

The source fix is synced, but direct `release/.../simple run ...` cannot be
claimed fixed until a bootstrap deploy completes and swaps in a rebuilt binary.

The CPU-SIMD evidence remains valid through `bin/simple`:
`doc/09_report/cpu_simd_engine2d_evidence_2026-07-08.md` reports
`native_simd_executed=true`, `native_simd_bit_exact=true`, and zero bitmap
mismatches on x86_64 AVX2.

## Next fix

Make stage4 deploy finish again before rechecking the direct release-path guard.
The likely first target is the stage3 exit 139 / stage4 seed fallback path; the
stage4 worker gives no useful diagnostics before timing out.
