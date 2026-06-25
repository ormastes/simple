# Optimize Native CLI Stub Segfault (2026-05-27)

Status: RESOLVED (2026-05-27)

## Status

RESOLVED (2026-05-27)

## Summary

`src/app/optimize/main.spl` builds as a native standalone smoke binary, but the binary segfaults before producing help output.

## Evidence

Build command:

```bash
bin/simple native-build --source src/app --source src/lib --entry-closure --entry src/app/optimize/main.spl --strip --output build/tmp/optimize_cli_native_smoke
```

Observed build result:

- Build succeeds.
- The native builder generates host CLI/runtime stubs, including `sys_get_args`, `rt_cli_get_args`, and process/file helpers.
- Binary size: 86 KB.

Runtime smoke:

```bash
timeout 5s build/tmp/optimize_cli_native_smoke --help
```

Observed result:

```text
Segmentation fault
EXIT=139
```

Running the binary with no arguments also exits `139`.

## Resolution

The crash had two native CLI startup causes and one analyze-path failure:

**Phase 1 — CLI startup segfault (.spl fixes):**

- `std.sffi.cli.cli_get_args()` used `?? []`, which lowered through `rt_unwrap_or_self`; the selected `simple-core` runtime did not provide that helper, so the linker weak-stubbed it to nil.
- `std.cli.cli_util.get_cli_args()` assigned the boolean result of `args.push(...)` back into `args`, causing native callers to receive `1` instead of an array.
- The shared CLI helper skipped any second `.spl` argument as a launcher script path, which broke standalone native binaries whose first user argument is a source file.
- `optimize.main` used a native-fragile optional binding for parsed arguments and assumed `args[0]` was always the `optimize` launcher subcommand.
- The analyze path read files through `shell_output("cat ...")`, which depends on `rt_process_run`; the standalone native runtime did not provide that safely.

These were fixed in the `.spl` layer: `?? []` replaced with explicit nil checks, `args.push(...)` without assignment, `.spl` launcher-path skip scoped to `is_simple_launcher()`, optimizer args parsed without optional binding, and `std.io.file_read` used for optimizer analysis.

**Phase 2 — Analyze path returning exit 1 (runtime C fix):**

After the `.spl` fixes, `--help` worked but `analyze` returned exit 1 with "could not read file". Root cause: `std.io.file_read` calls `rt_file_read_text`, which was absent from the core-c bootstrap runtime (`build/simple-core/libsimple_runtime.a`). The `CoreCBootstrap` lane compiles only `runtime_native.c`, `runtime_legacy_core.c`, and `runtime_mcp_core.c` — but `rt_file_read_text` (and `rt_file_exists`, `rt_file_delete`, `rt_env_get`) were defined only in `runtime.c`, which is not part of that set. The stale `build/simple-core/libsimple_runtime.a` passed the `runtime_archive_has_core_required_symbols` check (none of these symbols are in `CORE_REQUIRED_RUNTIME_SYMBOLS`), so it was selected without triggering a rebuild.

The fix adds `rt_file_read_text`, `rt_file_exists`, `rt_file_delete`, and `rt_env_get` to `src/runtime/runtime_native.c` (all implemented via existing `spl_*` helpers that are already compiled into the core-c archive). The `build/simple-core/libsimple_runtime.a` archive was rebuilt to include the updated `runtime_native.o`.

Verified:

```bash
bin/simple native-build --source src/app --source src/lib --entry-closure --entry src/app/optimize/main.spl --strip --output build/tmp/optimize_cli_native_smoke
timeout 5s build/tmp/optimize_cli_native_smoke --help
```

Observed result: help text printed and `EXIT=0`.

Also verified:

```bash
timeout 15s build/tmp/optimize_cli_native_smoke src/app/optimize/main.spl --level=O1
```

Observed result: analysis completed and `ANALYZE_EXIT=0`.

## Impact

The optimizer interpreter tests pass, but native standalone execution is not currently a valid smoke signal. This blocks claiming that the optimize plugin is fully native-runtime healthy.

## Suspected Cause

The native build falls back to generated stubs for argument/runtime functions that return arrays. The crash happens before help text is printed, making the CLI argument retrieval path the likely failure point.

## Follow-up

- `sys_get_args`, `rt_getpid`, and the `rt_cli_*` dispatch symbols remain weak-stubbed to nil in the standalone optimize binary. These are only needed for the full Simple launcher environment and do not affect the optimize CLI paths exercised above.
- The `build/simple-core/libsimple_runtime.a` rebuild above is a manual step. Future native builds that select the `SimpleCore` lane via `find_abi_complete_simple_core_runtime_library` should either include `rt_file_read_text` in `CORE_REQUIRED_RUNTIME_SYMBOLS` to force a rebuild when it is missing, or add a freshness check before returning the cached archive.
