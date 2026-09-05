# Core-C Stage4 missing runtime symbols — 2026-07-19

**Status:** SOURCE FIXED / STAGE 4 QUALIFICATION PENDING

## Reproduction

The incremental pure-Simple Stage4 CLI build reached its final core-C link and
failed with undefined `rt_string_trim_start` and `rt_cli_run_file` symbols.

## Root cause

- String lowering emitted `rt_string_trim_start`, but the core-C and
  pure-Simple runtimes only implemented its `trim` and `trim_end` siblings.
- The test runner imports its optional fork executor into the CLI closure.
  Core-C had no fail-closed equivalent of the hosted runtime's unsupported
  `rt_cli_run_file` fallback, so even the default process mode could not link.

## Fix and regression

- Implement `rt_string_trim_start` in both core runtimes.
- Compile a strong `rt_cli_run_file` fallback only for standalone core-C; it
  reports that `--fork` requires hosted interpreter support and returns failure
  without colliding with the hosted driver owner.
- Extend `runtime_native_focus_test.c` to check both contracts.

Stage4 qualification remains pending until the retained incremental build
finishes and the exact candidate passes the bounded source and essential-tools
checks.

The settled-tree replay reached its 1200-second cap with exit 124, produced no
candidate, and left an empty diagnostic log. The 222 MiB cache (2,713 files) is
retained; do not start another replay without first instrumenting the silent
pre-output phase.
