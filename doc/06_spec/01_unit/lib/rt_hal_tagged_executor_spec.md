# RT/HAL Tagged Executor — Unit Manual

Executable: `test/01_unit/lib/rt_hal_tagged_executor_spec.spl`  
Status: **unverified** — the self-hosted `bin/simple` runtime is absent in this
worktree, so SPipe generation was not executed.

## Scenarios

The spec resets the compiler-registered boundary and confirms its Pure binding
materializes without manual setup. It also confirms that Pure-only policy
returns only the Pure result, while enabled scalar callback comparators fail
closed before submission because they cannot establish exact I/O, frozen
transfer, cancellation, or reaping. Finally, an unavailable safe process
comparator is surfaced as typed unsupported.

This is an admission/fail-closed unit contract. C/Rust process parity and any
irreversible effect replay require the system differential suite.

## Regeneration

```text
bin/simple spipe-docgen test/01_unit/lib/rt_hal_tagged_executor_spec.spl --output doc/06_spec --no-index
bin/simple test test/01_unit/lib/rt_hal_tagged_executor_spec.spl --mode=interpreter
```
