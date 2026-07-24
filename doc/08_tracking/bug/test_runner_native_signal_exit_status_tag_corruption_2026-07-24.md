# Test-runner native signal exit status tag corruption — 2026-07-24

**Status:** CURRENT SOURCE FIXED / FRESH STAGE-4 QUALIFICATION PENDING

## Reproduction

Running the focused phase-2 spec through the deployed pure-Simple test runner
failed with:

```text
Error: Process exited with code 2305843009213693951
```

The direct child emitted parser errors and then SIGILL. Evidence:

- `build/mini_builds/duplicate-incremental-phase2-current-interpreter.log`
- `build/mini_builds/duplicate-incremental-phase2-current-direct.log`

`2305843009213693951` is `0x1fffffffffffffff`, consistent with an older or
mixed compiler artifact incorrectly decoding or unsigned-shifting native `-1`.

## Root cause boundary

The runner does not manufacture this value. `process_run_bounded` returns the
corrupted exit field and `make_result_from_structured_evidence` reports it
verbatim. Existing bounded-process tests cover positive exit 17, spawn failure,
and timeout, but do not prove a native signal/negative-status round trip.

Do not map this sentinel to a friendly runner error. That would hide the actual
compiler/runtime crash and leave every other `process_run_bounded` caller
corrupted.

## Current-source audit

Current source already has the correct shared-owner path:

- native calls remap `rt_process_run_bounded` to its tuple facade;
- `rt_process_result_to_tuple` applies signed `rt_value_as_int` exactly once;
- typed tuple-field lowering loads the raw `i64`;
- raw `i64` formatting uses signed `%lld`.

The focused regression in
`test/01_unit/app/test_runner_bounded_output_contract_spec.spl` terminates a
POSIX child by signal and requires both status `-1` and formatted text `"-1"`.
Run it once in interpreter mode and once with a fresh admitted Stage-4 native
binary. Only if the fresh artifact still produces the sentinel should emitted
LLVM for tuple field 2 and signed shifts be inspected.
