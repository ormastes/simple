# Optimize Native CLI Stub Segfault (2026-05-27)

## Status

Fixed in follow-up.

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

The crash had two native CLI startup causes:

- `std.sffi.cli.cli_get_args()` used `?? []`, which lowered through `rt_unwrap_or_self`; the selected `simple-core` runtime did not provide that helper, so the linker weak-stubbed it to nil.
- `std.cli.cli_util.get_cli_args()` assigned the boolean result of `args.push(...)` back into `args`, causing native callers to receive `1` instead of an array.
- The shared CLI helper skipped any second `.spl` argument as a launcher script path, which broke standalone native binaries whose first user argument is a source file.
- `optimize.main` used a native-fragile optional binding for parsed arguments and assumed `args[0]` was always the `optimize` launcher subcommand.
- The analyze path read files through `shell_output("cat ...")`, which depends on `rt_process_run`; the standalone native runtime did not provide that safely.

The fix replaces the `?? []` calls with explicit nil checks, mutates CLI argument arrays with `args.push(...)` without assignment, skips `.spl` launcher paths only for the Simple launcher/runtime, parses optimizer args without optional binding, and uses `std.io.file_read` for optimizer analysis.

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

- Link the native optimize smoke with a runtime that provides `sys_get_args`/`rt_cli_get_args`, or
- Make generated array-returning stubs safe enough for no-argument/help-path smoke tests, or
- Add a native-build mode that rejects these stubs for CLI entrypoints instead of producing a crashing binary.
