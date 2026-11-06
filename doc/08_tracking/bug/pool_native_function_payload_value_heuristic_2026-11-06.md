# Pool native function-value decode guesses pointer vs int-tag by value

Status: OPEN (P1)
Date: 2026-11-06
Found by: similar-pattern audit for
`isolated_thread_raw_worker_argument_heuristic_flake_2026-08-12` (P0).

## Defect

Two pool entry paths decode a native Simple function value with the same
value-based rule the isolated-thread spawn used before it moved to an
explicit worker-closure kind:

- `src/runtime/runtime_pool.c` `rt_pool_native_function_payload`
- `src/runtime/runtime_thread.c` `rt_native_closure_payload`, now used only by
  `rt_pool_v1_scalar_task_create`

Rule: a word above the user-VA ceiling is read as int-tagged (`>> 3`), a
TAG_HEAP word is stripped, and any other word is used as a machine address.
Below the ceiling, an 8-aligned word is ambiguous. It can be a record address
or the int-tagged `addr << 3` of one. On a Windows heap (~2^40), the tagged
form (~2^43) stays under the 2^47 ceiling, so it is used as an address. That
is the same wrong guess the P0 fixed for thread spawn.

## Required fix

Use the explicit-kind decode that thread spawn now uses (`RT_WORKER_CLOSURE_*`
in `runtime_thread.c` and `executor.rs`). The submitter states whether the
word is a machine address or a tagged Simple value. The pool then decodes it by
that kind and never by the word's value. Pool callers (the Simple pool facade
and the C/Rust pool tests) must pass the matching kind. Add a dual-decodable
fixture that maps records at A and A << 3 (see
`executor_tests.rs` `DualDecodeFixture`) as the regression.

## Not in scope of the P0

The pool is a separate API with its own callers and tests. It was left
unchanged so that the thread-spawn ABI change stays reviewable.
