# SimpleOS Host-OS Guide — what exists and how the userland works

Updated 2026-07-13. Companion plan:
`doc/03_plan/os/simpleos/host_os_completeness_plan.md`.

## Userland model (FreeBSD-referenced)

- **FHS layout** on the boot volume: `/bin /usr/bin /usr/local/bin /etc /tmp
  /home/root`, with `/usr/bin/clang` (landed `76dc1967008`).
- **Exec**: `ssh root@host <cmd>` → sshd tokenizes → PATH resolution
  (`src/os/kernel/loader/fs_exec_resolve.spl`: absolute passthrough, else
  probe `/bin:/usr/bin:/usr/local/bin`, memoized name→path cache, exit 127
  on miss) → ring-3 streaming spawn with envp (PATH/HOME/TERM). Gate:
  `scripts/os/fhs_path_exec_gate_uefi.shs` (OVMF pflash).
- **Shell**: real shell app (`src/os/apps/shell/` — builtins, env, pipes,
  jobs, `.shs` scripting) bridged onto the SSH shell channel
  (`ssh_shell_bridge.spl`), sourcing `/etc/shrc` then `~/.shrc` (in flight).
- **Boot config**: FreeBSD-style `/etc/rc.conf` (`name_enable="YES|NO"`,
  default enabled) read by `src/os/kernel/boot/rc_conf.spl`; init spawns
  `/sbin/init` (`boot_fs.spl:386`); dependency-aware service manager with
  restart policy exists at `src/os/services/init/init_service.spl`.

## Kernel facilities (verified 2026-07-13)

- **L4 IPC**: synchronous named-port message passing
  (`src/os/kernel/ipc/ipc.spl`, `l4_fast_ipc.spl`), blocking recv/waiter
  wakeup, capability tokens + pledge/unveil (`capability.spl`). Services on
  ports (netstack = port 2).
- **Multiprocess**: fork(COW)/exec/spawn/waitpid/exit
  (`syscall_process.spl`), per-PID isolation levels, fair virtual-deadline
  scheduler + Deadline/RtRoundRobin/Background classes, APIC periodic-timer
  preemption, green-thread carriers with CPU affinity.
- **SMP**: per-CPU state + IPIs; riscv AP bringup proven; x86_64 INIT/SIPI
  code present with a gated live spec
  (`test/system/simpleos_smp_ap_live_spec.spl`, SIMPLEOS_QEMU_SMP_AP_LIVE=1).
- **Memory**: per-process address spaces on 6 arches; transactional
  checksummed NVMe swap wired to the page-fault owner (x86_64); multiarch
  hook plan in `doc/03_plan/os/memory/paging_swap_multiarch_plan.md`.
- **W^X** enforced (EFER.NXE; NX on writable user pages).

## Filesystems

- `trait Filesystem` + VfsManager (`src/os/services/vfs/vfs.spl:18,:435`) is
  THE switchability contract: Fat32Driver implements it; DbFsDriver impl
  written (gate pending); `/win` (win_vfs) is the working subpath-mount
  precedent. ECS-backed devfs/procfs/pipefs service models exist
  (`src/os/services/{devfs,procfs,pipefs}_service.spl`) awaiting trait
  mounts. Production FAT32 boot still bypasses the trait (recorded
  follow-up). Boot root order: NVFS → DBFS → FAT32 fallback (`boot_fs.spl`).
- FAT32: LFN read both stacks; in-guest creation 8.3-only (root dir).
  DBFS: POSIX shim (D10), no modes/symlinks (fail-closed Errs).

## Terminal stack

- Userspace `tty_service.spl`: console + PTY master/slave kinds, termios
  lflags (ISIG/ICANON/ECHO), VINTR Ctrl-C → `signal_deliver(pgid, SIGINT)`.
  NOT yet wired into the sshd shell channel (raw byte bridge today) — H2.
- `terminal` app = UI emulator; `smux` = tmux-like multiplexer.

## libc (`src/os/libc/`, 36 files)

`simpleos_syscall(id, a0..a4)` ABI with dual-mode Linux fallback. Covered:
fs, process/fork, ipc/pipes, signal, epoll, math/string/stdlib. NOT covered:
sockets (all ENOSYS — netstack is IPC-port-2 only), termios header, real
pthreads (no-op stubs). No llvm-libc in tree — reference only; libc grows
over Simple-written system services (H3).

## Freestanding discipline (MUST-KNOW before writing kernel-path .spl)

1. Module-level array/`[text]` initializers DO NOT RUN — use
   function-returning constants + lazy-init bool (zeroed-.bss scalars are
   safe). 2. class/trait-object dynamic dispatch corrupts ring-0 — direct
   externs or @cfg dispatch only. 3. `char_at`/`starts_with` unreliable on
   dynamically-built strings — use raw `[u8]` accessors. (All three:
   `fs_exec_resolve.spl` header, discovered under gate.)
