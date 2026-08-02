# Stage4 test-runner main HIR names

## Reproduction

Stage4 reached `src/app/test_runner_new/test_runner_main.spl` and reported
unresolved `time_now_unix_micros`, `duration_ms`, `to_int`, and
`file_atomic_write` names.

## Fix

Time and atomic-file helpers now come from their concrete `time_ops` and
`file_ops` owners. Text conversion uses the supported optional method form.
The daemon elapsed duration is computed before the success/failure branch, so
both branches see the same value. The adjacent library runner mirror receives
the same time, conversion, and duration-scope fixes.

## Regression evidence

`test_runner_main_hir_contract_spec.spl` checks concrete owners, conversion,
scope order, and mirror parity.
