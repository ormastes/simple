# go-to-end under default `--mode dynload` emits 0 objects when any module fails

- **ID:** go_to_end_dynload_zero_objects_2026-11-01
- **Severity:** P1 (phase 3 diagnostics: no codegen evidence for passing modules)
- **Status:** open (stage2 workaround: `--mode one-binary`)
- **Component:** 80.driver (driver_aot_pipeline.spl), app/cli native_build_output_plan.spl

## Symptom

Run 12 (`native-build --keep-going --go-to-end`, default `--mode dynload`):
HIR 1516/1516 and MIR 1503/1516 passed, and borrow, optimize and weave ran
for all 1503. Then:

```
[mir-shard] disabled: output format re-reads MIR set
[go-to-end] go-to-end: 72 failure(s) (... mir=72 ... codegen=0); 0 object(s) in cache; link skipped
```

## Root cause

`native_build_output_format_v1` maps `dynload` (without an explicit native
output) to `OutputFormat.Both`.
`native_staged_codegen_eligible_reason_v1` refuses `Both` ("output format
re-reads MIR set"), and `stage_emit_object` returns
`go_to_end_finish_v1(0, [])` whenever go-to-end has failures and the
per-module lane is not eligible. The good modules never reach a backend.

## Workaround

Pass `--mode one-binary`. The output format becomes `Native`, the MIR-shard
lane is eligible, and real `aot-*.o` objects are written for every lowered
module, while the link stays blocked on the failures. Objects are written to
the cwd, not under `--cache-dir`.

## Real fix (current source)

Under go-to-end with failures, either emit the per-module objects for the
`Both` format too (the SMF half is not needed when the link is blocked), or
downgrade to `Native` once failures are recorded. Do not silently return 0
objects. The objects should also be written under `--cache-dir`.
