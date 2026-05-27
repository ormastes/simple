# Optimize Native CLI Stub Segfault (2026-05-27)

## Status

Open.

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

## Impact

The optimizer interpreter tests pass, but native standalone execution is not currently a valid smoke signal. This blocks claiming that the optimize plugin is fully native-runtime healthy.

## Suspected Cause

The native build falls back to generated stubs for argument/runtime functions that return arrays. The crash happens before help text is printed, making the CLI argument retrieval path the likely failure point.

## Follow-up

- Link the native optimize smoke with a runtime that provides `sys_get_args`/`rt_cli_get_args`, or
- Make generated array-returning stubs safe enough for no-argument/help-path smoke tests, or
- Add a native-build mode that rejects these stubs for CLI entrypoints instead of producing a crashing binary.
