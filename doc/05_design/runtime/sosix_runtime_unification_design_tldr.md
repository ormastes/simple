# SOSIX Runtime Library Unification — TL;DR

Unify the contract and the library, not every provider. One operation lifecycle
(lifted from the already-pure `src/os/sosix/core/` into
`src/lib/common/contracts/sosix/`), one canonical `Future`, one frozen
service-ID table, one `std.nogc_async_mut.sosix` capsule (`fs`, `time`, `sync`,
`posix`, `provider`) bound by hosted code and SimpleOS alike. SimpleOS legacy
`io_rw.spl` (busy-wait, fabricated serial write, dead duplicate in `io.spl`) is
retired onto the existing v1 positioned stack. Host service IDs
`0x1001/0x1002/0x1101/0x1201` already exist and are frozen, not redesigned.

Perf is an acceptance axis: `posix.pread` must disassemble to `pread@plt` with
no wrapper, sync read_at = 1 reserve + 1 commit + ≤1 native wait, async
rejection allocates nothing, import closure ≤ 25 files, every new file ≤ 300
lines, startup unchanged vs baseline B0. Blocked rows (io_uring, macOS/Windows,
GPU proxy, device queues, `export use ... as` fix) stay visible with owners.

```sdn
flow:
  caller -> std.nogc_async_mut.sosix.{fs,sync,posix,time}
  fs/sync -> common.contracts.sosix.operation_v1 -> async_ring.SimpleRing -> provider
  provider: [SoftwareRingProvider (hosted ref), src/os/sosix/fs v1 stack (SimpleOS)]
  posix -> rt_fd_pread/pwrite (runtime-owned, BLOCKED until landed) -> libc
  os.sosix.core.* -> export use common.contracts.sosix.*   # 56 importers untouched
```

Full design: `sosix_runtime_unification_design.md`. Plan:
`doc/03_plan/agent_tasks/sosix_runtime_unification_parallel_plan_2026-09-05.md`.
