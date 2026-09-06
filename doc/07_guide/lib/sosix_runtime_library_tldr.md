# SOSIX runtime library — TL;DR

`std.common.contracts.sosix.*` holds the pure contracts (operation lifecycle,
completions, wait protocol, positioned descriptors, frozen IDs, typed errors);
`std.nogc_async_mut.sosix` is the hosted composition (`fs` async over
`SimpleRing`, `sync` with one native wait per completion, `time` leaves,
`host_facade`). SimpleOS binds the same contracts through `os.sosix.core.*`
shims. Exact POSIX aliases, native providers, GPU proxy, and device queues are
BLOCKED rows, not stubs.

```sdn
call:
  read_at -> file_operation_v1.validate -> SimpleRing.reserve+commit -> op slot PENDING
  provider completes -> pump -> operation_v1.complete -> completion FIFO
  poll -> Ready(Result<SosixCompletion,SosixError>) | Pending(RingToken)
  release -> refused until ring retired the lease (timeout != retirement)
sync:
  submit -> SosixSyncWaitState.before_wait -> driver.wait_once (exactly 1) -> after_wait
gate:
  scripts/check/check-sosix-capsule-boundaries.shs   # PASS/FAIL/ERROR last line
```

Full guide: `sosix_runtime_library.md`.
- Real files: `SosixHostedFileDriver` (`open_path`, `buffer_from`, `buffer_bytes`) + the sync leg; sync calls release their slot on return. Perf: one ring hop per op, ~38× a direct read on the seed interpreter (report in `doc/10_metrics/runtime/`).
