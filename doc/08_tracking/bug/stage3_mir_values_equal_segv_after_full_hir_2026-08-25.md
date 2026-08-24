# Stage 3 self-host SIGSEGV while lowering `values_equal` after full HIR

**Date:** 2026-08-25  
**Status:** OPEN — blocks Stage 4 deployment and self-hosted GPU verification  
**Platform:** `x86_64-unknown-linux-gnu`, LLVM backend, dynload runtime

## Reproduction

The fresh trust-root run used an isolated jj workspace and a newly rebuilt Rust
seed/runtime. Stage 2 passed compiler sanity plus struct receiver/runtime
capability and was admitted. Stage 3 was then resumed from that immutable
artifact:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh \
  --resume-stage3-from-admitted=build/bootstrap-gpu-r3 --jobs=1 \
  --bootstrap-receipt=build/bootstrap-gpu-r3/planner-admission-stage3.env
```

The wrapper exited 139 (`Segmentation fault (core dumped)`). Evidence is in
`build/bootstrap-gpu-r3/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

## Established boundary

- Parse/HIR completed for all **693/693** modules.
- HIR finalization completed **948/948** and post-HIR validation completed
  **693/693**.
- The earlier fabricated `unresolved name: __p-1` diagnostic did not recur.
- MIR lowering reached `src/compiler/backend/backend/interpreter.spl`.
- The last function marker is `lower_function:body-start values_equal`; the
  final expression marker is `block:stmt 0`.
- Immediately beforehand, `resolve_sym_name` completed, but its body emitted
  `WARNING: unresolved method call 'get' lowered to const-0 placeholder
  (silent-null risk, Task #145)`.

This is not the older `n_modules=0` failure: this run retained the complete
module set through HIR and entered real MIR function lowering.

## Next investigation

Trace the first expression in `BackendInterpreter.values_equal` and remove the
unresolved method-call-to-zero path rather than masking the crash. Inspect the
`Value` enum comparison arms and the static owner/type available to each `.get`
call. A focused MIR-lowering fixture must reproduce the failure before another
full bootstrap attempt.

The repository's mandatory three-cycle bootstrap cap was reached in the GPU
dynamic-loading lane. Do not retry this full bootstrap in the same session.
