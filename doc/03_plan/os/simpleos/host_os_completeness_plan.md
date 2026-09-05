# Plan: SimpleOS as a complete host OS (FreeBSD-referenced)

Status: ACTIVE 2026-07-13. Goal: make SimpleOS a general host OS (reference:
FreeBSD mainly, Linux secondarily). Method: parallel small-model lanes with
written guides, higher-model review, evidence-gated landings.

## Verified foundations (recon 2026-07-13, file:line in source)

- **L4 IPC — IMPLEMENTED in Simple**: synchronous message passing over named
  ports (`src/os/kernel/ipc/l4_fast_ipc.spl` inline-register messages;
  `ipc.spl:27-150` bounded queues, 1024 ports; `syscall_ipc.spl` blocking
  recv + waiter unblocking = rendezvous RPC). Capability tokens with
  generation counters + pledge/unveil (`capability.spl`, 830 lines).
  Services ride ports (netstack = port 2, `syscall_net.spl`).
- **Multiprocess — IMPLEMENTED**: fork (COW + fd-table prep), exec-in-place,
  spawn, blocking waitpid, exit reaping (`syscall_process.spl`); per-PID
  isolation levels (`scheduler/process_isolation.spl`); full context switch
  (`context_switch.spl`); fair virtual-deadline timesharing
  (`scheduler_algorithm.spl`); green-thread carriers with CPU affinity.
- **SMP**: per-CPU state, RESCHED/TLB_FLUSH/HALT/CALL_FUNC IPIs, riscv AP
  bringup landed (rv32 3-core proven). **x86_64 INIT/SIPI trampoline is
  future work** (the one scaffold gap).
- **Paging+swap**: x86_64 transactional NVMe swap proven; multiarch plan at
  `doc/03_plan/os/memory/paging_swap_multiarch_plan.md` (P0 hook-trait
  extraction pending toolchain).
- **Userland (landed `76dc1967008`)**: FHS dirs, /usr/bin/clang, PATH
  resolution + memoized cache, real envp, exit 127 — OVMF-gated.
- **VFS**: `trait Filesystem` (`services/vfs/vfs.spl:18`) + VfsManager;
  Fat32Driver implements; DbFsDriver impl written (held, gate pending);
  production boot still bypasses the trait (follow-up).
- **In flight (held/running lanes)**: DBFS bootable root + mkfs; real
  std.http_server + RESP redis server in-guest; real shell on SSH login +
  /etc/shrc + ~/.shrc + /etc/rc.conf reader (default=enabled).

## Second recon wave (2026-07-13) — most lanes are WIRE+PROVE, not build

- **tty_service.spl EXISTS** (userspace POSIX terminal service): TTY_CONSOLE/
  PTY_MASTER/PTY_SLAVE kinds, termios lflags (ISIG/ICANON/ECHO), VINTR
  Ctrl-C → `signal_deliver(pgid, SIGINT)` (tty_service.spl:34,216). No
  kernel-side tty device or controlling-terminal linkage yet; sshd bridge
  bypasses it. smux app = tmux-like multiplexer.
- **devfs_service.spl + procfs_service.spl + pipefs_service.spl EXIST**
  (ECS-backed /dev and /proc node models); win_vfs mounts at /win through
  VfsManager (`win_vfs_mount.spl:35`) — a working precedent for subpath
  trait mounts.
- **init_service.spl EXISTS**: dependency-aware userspace service manager
  (ServiceDef: binary, args, dependencies, capabilities, restart policy);
  boot spawns `/sbin/init` (`boot_fs.spl:386,397`). rc_conf.spl reader just
  added (Lane E).
- **libc reality**: 36 files/6.2k lines; sockets ALL ENOSYS
  (simpleos_socket.c), pthread = 241 lines of no-op stubs, no termios
  header; dual-mode Linux fallback confirmed. **No llvm-libc anywhere**
  (checked repo + /home/ormastes/llvm-project) — use it as a
  header/conformance REFERENCE only; impl targets Simple-written services
  (user directive).
- **Scheduler**: Fair/Deadline/RtRoundRobin/Background policy classes, APIC
  periodic timer preemption. **x86_64 INIT/SIPI code EXISTS**
  (cpu.spl:268, rt_x86_prepare_ap_startup) + a gated live gate
  `test/system/simpleos_smp_ap_live_spec.spl` (-smp 2, env
  SIMPLEOS_QEMU_SMP_AP_LIVE=1).
- **Security**: W^X/NX enforced (EFER.NXE, cpu.spl:47); no uid/gid
  enforcement; no KASLR.
- **Net perf**: benchmark framework exists (lib perf.spl, BenchmarkSuite,
  http_benchmark_* harness); NO in-guest network speed gate yet.

## Gap table → lanes (H-series)

| # | Lane | Content (revised per recon) | FreeBSD reference |
|---|------|---------|-------------------|
| H1 | Multiprocess prove+harden | Concurrent ring-3 processes QEMU gate (N processes timesharing via APIC preemption), zombie reaping proof, SIGCHLD delivery e2e | proc lifecycle, signals |
| H2 | TTY/PTY wire+prove | Wire tty_service PTY pairs into sshd shell channel (replace raw byte bridge), controlling-terminal pgid per session, gate: Ctrl-C over SSH delivers SIGINT to the foreground program (kills a running exec, shell survives) | tty(4), pts(4) |
| H3 | libc over Simple services | Replace ENOSYS socket stubs with wrappers over netstack port-2 IPC; termios.h backed by tty_service calls; real pthread over green-thread carriers LATER (design first). llvm-libc = conformance reference only | libc, syscalls(2) |
| H4 | Pseudo FS integrate | Adapt devfs/procfs services onto the `Filesystem` trait and mount /dev + /proc via VfsManager (precedent: /win). Gate: cat /proc/<pid>/status of a live process; echo >/dev/null; read /dev/urandom | devfs(5), procfs(5) |
| H5 | Net + speed gates | In-guest throughput/latency gate over hostfwd using existing BenchmarkSuite + http_benchmark harness; record baselines in doc/10_metrics | netperf practice |
| H6 | BSD init/services | Wire rc_conf → init_service ServiceDefs (deps + restart policy already modeled); gate: kill a supervised service, watch restart; ordered boot markers; clean shutdown | rc(8), rc.conf(5) |
| H7 | SMP live | Un-gate + green the existing simpleos_smp_ap_live_spec (-smp 2), per-CPU run queues executing real tasks, cross-CPU reschedule IPI proof | SMP scheduling |
| H8 | SMF dyload gate | Recon verdict: SMF dyload is ALREADY production-ready in-guest (kernel `loader_api.spl:27-77` dispatch → `smf_load`/`elf64_load`, `dylib_registry` symbol lookup, arch/ABI/role validation; TemplateCode monomorphized at load — no relocations needed). BUT zero in-guest .smf usage exists outside the loader = unproven in practice. Lane = author a gate: build a small .smf library, load it in-guest via `loader_dynopen_path`, call a symbol, assert output. ELF .so stays unprioritized (needs R_X86_64_* engine + PLT + .init/.fini vs SMF's simpler model) | (SMF native) |
| H9 | Privileges (LATER — design only) | uid/gid over DBFS (FAT32 has no modes); pledge/unveil + capability manager already exist — design doc maps them to ucred-style model | ucred, chmod |

## Cross-arch requirement (STANDING, user 2026-07-13)

Every host-OS feature must target **x86 (32/64), arm (32/aarch64), riscv
(32/64)**. Current per-arch reality (recon-verified) — lanes must state their
arch coverage and record non-x86 ports as explicit TODOs, never silently ship
x86-only:

| Capability | x86_64 | x86_32 | aarch64 | arm32 | riscv64 | riscv32 |
|---|---|---|---|---|---|---|
| Paging + per-proc AS | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Bootable QEMU lane | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Transactional swap | ✅ | ⬜ | ⬜ | ⬜ | ⬜ | ⬜ (P2/P3 of paging plan) |
| SMP AP bringup | INIT/SIPI present, gated | ⬜ | partial | partial | proven | proven (rv32 3-core) |
| Ring-3 FS-exec + PATH | ✅ (landed) | ⬜ | scaffolding (arm_fs_exec_*) | ⬜ | ⬜ | ⬜ |
| SMF dyload (format) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ (arch byte in trailer) |
| libc simpleos_syscall ABI | ✅ | ABI neutral; Linux-fallback asm x86_64-only | " | " | " | " |
| OVMF/clang capstone | ✅ | n/a | needs arm UEFI | n/a | n/a | n/a |

Implication: paging/SMF are broadly arch-ready; the **FS-exec/loader, libc
fallback asm, and per-arch swap** are the x86_64-heavy areas needing ports.
Lane W (WM) already reuses one compositor across arches (framebuffer on
baremetal, winit on host). New lanes: prefer arch-neutral Simple + @cfg or
HAL-trait dispatch (per the paging plan's MmuSwapHooks pattern); put
per-arch asm/regs behind the existing arch/hal.spl seam.

## Rules of engagement
- Board-workable: no `-kernel`/`isa-debug-exit` pass semantics; OVMF or
  scenario-catalog gates; virtio-only pieces flagged vs the board plan.
- Evidence bar: durable serial/host transcripts quoted per PASS; no
  verbal claims (repeatedly caught false-complete claims this way).
- Freestanding discipline (Lane A findings, see fs_exec_resolve.spl header):
  no module-level array initializers; no class/trait-object dispatch in
  freestanding kernel paths; raw [u8] accessors for dynamic strings.
- Landing: coordinator-only, 3-way apply of lane patches onto the live
  origin tip via temp GIT_INDEX_FILE; never `jj commit` on the shared WC.
