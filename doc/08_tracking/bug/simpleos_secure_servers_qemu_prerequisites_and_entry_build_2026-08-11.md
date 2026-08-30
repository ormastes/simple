# SimpleOS secure-server QEMU evidence blocked before launch

The filesystem server evidence lane cannot currently reach QEMU. The canonical image is absent, `mcopy` is unavailable, the SimpleOS cross `ld.lld` is absent, and `bin/simple` identifies itself as the Rust bootstrap seed rather than the required pure-Simple self-hosted compiler.

Bounded build attempts also exposed two source/toolchain failures: the DB adapter used compact assignment statements rejected by the parser (expanded in the feature lane), and the web entry closure resolved `nogc_async_mut.platform` as an undefined `platform` identifier (changed to the canonical `std.nogc_async_mut.platform` import). Evidence logs are `build/os/server-artifacts/db-build.log` and `web-build.log`.

No runnable receipt is permitted until a fresh build produces pinned server artifacts, stages them into `/SYS/APPS/WEBSRV.SMF` and `/SYS/APPS/DBSRV.SMF`, launches them through filesystem exec, proves socket exchanges, and records shutdown/exit. The existing kernel-linked HTTP/RESP smoke is not equivalent.

## Hosted native evidence

A second, Cranelift-hosted web build produced a 3,583,232-byte artifact with SHA-256 `97f3afb04882d3801bf60014923ad572aa2d46de3aff7110117c36925fa2bdb8`; `--check` took 0.01s and 3,840 KiB RSS. Live launch still failed because the entry closure emitted unresolved stubs for aliased synchronous TCP classes, `chr`, and CPU feature globals. The TCP alias and ECH `chr` owners were corrected after the bounded build lane ended; CPU feature global linkage remains unverified. See `doc/06_spec/05_perf/web/simple_web_server_live_smoke_2026_08_11.md`.

The DB native build remained CPU-bound for 10m37s, reached approximately 2.76 GiB RSS, and emitted no artifact or diagnostic before the runaway cap stopped it. Therefore no pgwire, persistence, nginx, or PostgreSQL comparison is accepted.

## Filesystem-launch runner wiring (2026-08-12)

The FAT32 writer now accepts only explicitly supplied
`SIMPLEOS_WEB_SERVER_BINARY` and `SIMPLEOS_DB_SERVER_BINARY` payloads, validates
their target ELF machine, and publishes their exact bytes at
`/SYS/APPS/WEBSRV.SMF` and `/SYS/APPS/DBSRV.SMF`. There is no synthesized server
fallback. `scripts/check/check-simpleos-server-fs-launch-qemu.shs` rejects the
older kernel-linked combined-server image, verifies both staged files byte for
byte, and reserves live promotion for a nonce-correlated filesystem-launch
marker plus independent HTTP and pgwire exchanges.

The gate is currently fail-fast before QEMU: neither server artifact exists,
no kernel contains the `SIMPLEOS_FS_SERVER_LAUNCHER_V1` concurrent launcher
contract, and this host lacks `mcopy` and `psql`. QEMU itself is installed.
Consequently this update is runner/staging readiness, not live SimpleOS server
evidence.

## Scheduler-owned launcher gap (2026-08-12)

The missing launcher is not just an entry-file omission. The existing
`fs_exec_prepare_spawn_from_bytes` path creates a fresh bootstrap scheduler,
and the x86 streaming fs-exec path enters one program synchronously. A
persistent web server therefore prevents a second sequential DB launch.

The dedicated launcher must instead read both filesystem images, construct
both user process images, and register them with distinct PIDs in one live
`Scheduler`. Existing x86 trap-runtime installation can hold that scheduler,
but no x86 timer ISR currently feeds the saved `TaskContext` through
`Scheduler.timer_tick`, switches to the selected task's CR3, and resumes its
saved context. First-entry `arch_x86_64_enter_user_task` alone cannot provide
preemptive coexistence for two non-terminating servers.

The present scheduler bridge has an additional launch-contract gap: it
revalidates the exact web/DB `--simpleos` profiles, but
`Scheduler.create_user_task_from_bytes_pid` accepts no argv/environment
payload and the bridge drops those validated profiles before task image
creation. A future launcher must extend the staged user-process image boundary
to carry a bounded argv vector and prove that the two ring-3 processes receive
their nonce-bound profiles. Treating admission-string validation alone as
argument delivery would be fabricated evidence.

Required owners are:

- `src/os/kernel/loader/x86_64_server_admission.spl` for bounded image
  validation without scheduler mutation;
- `src/os/kernel/loader/x86_64_server_scheduler_bridge.spl` for two distinct
  task registrations in one scheduler;
- `src/os/kernel/arch/x86_64/scheduler_dispatch.spl` plus the matching ISR
  return assembly for timer-tick context/CR3 handoff;
- `examples/09_embedded/simple_os/arch/x86_64/server_fs_entry.spl` and a
  dedicated producer script.

Until all four owners exist and the QEMU gate observes both nonce-bound socket
exchanges concurrently, a kernel containing only the launcher marker is
explicitly rejected evidence.
