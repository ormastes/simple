# SimpleOS — What Is Actually Missing to Be a Real Desktop and Server OS

**Scope:** Honest, code-anchored assessment of `src/os` (and `src/lib` where a subsystem lives there) against the bar of a *real* desktop AND server OS — multi-process, isolated, filesystem-launched programs, networking, users, services — not a demo.
**Method:** Eleven per-domain source audits, reconciled against direct code spot-checks across six domains (all confirmed — see citations inline).
**Status:** Assessment only. Nothing here was committed.

---

## 1. Honest verdict

SimpleOS today is **a large, genuinely-written body of kernel-grade code that is not yet an operating system, because the kernel image that actually boots never runs a filesystem-launched program in ring-3 and never runs its own scheduler.** The subsystems read like a real OS on paper — a ~4850-line multiclass SMP scheduler with COW fork and context-switch assembly, a bitmap PMM with per-page refcounting and per-process PML4s, a writable block-level FAT32, page-table-walking user-pointer validation with grant-table safecopy, W^X enforced in x86_64 paging, fail-closed capabilities, a real Simple TCP/IP stack, and a real-crypto SSH daemon. But there is **one keystone failure and most of the other "foundational" verdicts are its children**: on the RISC-V boot, `os_main()` reaches only `start_http_server_baremetal()` or `serial_shell_main()` (`src/os/kernel/boot/os_main.spl:43,50`) — no scheduler loop, no ring-3; on the x86_64 boot, the entry the QEMU spec runs is the `fs_exec_entry.spl` probe fixture that prints fabricated success and never installs the GDT/TSS/IDT/SYSCALL runtime (session fact; `install_syscall_entry` lives only in `arch/x86_64/cpu.spl` + `arch_init.spl`, harness-only). Because no isolated user process ever runs in the booted image, the scheduler, syscall dispatcher, capability gates, demand-paging ISR, IPC, and signal paths are all *untriggered libraries*. **SimpleOS is at the "kernel bring-up / single-address-space monitor" stage of the desktop/server spectrum — not multi-process, not self-hosting, not yet a platform you can launch a program on.** The distance to a real OS is not "write more subsystems"; it is "make the booted kernel run one real ring-3 FS-launched process, then a second one preemptively," after which most of the existing code becomes reachable.

---

## 2. Capability matrix

Rated by **runtime truth in the booted image at the real-OS bar**, not by code presence. "Partial (code, unwired)" = substantial correct code exists but is never reached by the shipped boot.

| Domain | Desktop | Server | Severity | One-line gap |
|---|---|---|---|---|
| process-exec | Partial (code, unwired) | Partial (code, unwired) | foundational | 4850-line scheduler never triggered; preemption not wired (`timer.spl:166` `# scheduler_tick()` commented); `kernel_stack:0` everywhere; no threads, no POSIX signals |
| memory-vm | Partial (code, unwired) | Missing | foundational | COW fork broken (`vmm_handle_cow_fault` has zero callers); demand-paging ISR dead in boot; no swap, no OOM killer, no reclaim; PMM capped at 4GB |
| storage-fs | Partial (code, unwired) | Missing | foundational | **Three filesystems exist as code** — a full **FAT32** driver (`services/fat32/` + `fat32_write` + `fat32_hardening` + lib `fs_driver/fat32_*`, Lean-proved in `src/verification/fat32/Fat32.lean`), **NVFS** (`services/nvfs`, in-memory arena only), and **DBFS** (`lib/**/db/dbfs_*`) — but the boot path mounts **none** of them: it uses a minimal single-cluster read-only reader (`vfs_boot_init.spl` `vfs_boot_read_pure_nvme_fat32_path_bytes`, first 4 KB only). No journal/permissions/cache/LFN-write in the live path; `BlockCache` dead; `fsync` no-op (now flushes durable length at the nvfs arena layer, session fix); VFS routes to `mounts[0]` only |
| syscall-abi | Partial (code, unwired) | Missing | foundational | No dynamic linker / ELF interp (ET_DYN rejected, zero relocations); no Linux ABI; x86_64 userland syscall asm is a no-op stub; SYSCALL MSR entry not installed in production boot |
| ipc-sync | Partial (code, unwired) | Missing | foundational | No futex / AF_UNIX / epoll / shm_open / mq_open; signal delivery is stubbed externs; IPC/pipe/signal state is module-global, not per-process |
| networking | Missing | Missing | foundational | App `socket()` (syscalls 70-77) returns `-38 ENOSYS`; Simple stack never bound to NIC; only real wire path is a single hardcoded RISC-V C connection with canned payloads; no x86_64 net runtime |
| devices-drivers | Partial (code, unwired) | Partial (code, unwired) | **major** | Real register-level drivers (NVMe/APIC/IDT/xHCI/PS2/RTC) exist but bring-up doesn't run in the booted image; poll-only, no IRQ handlers; audio stubbed; NVMe read returns first 4KB only |
| desktop-gui | Partial (code, unwired) | N/A (optional) | foundational (desktop) | Compositor/WM/desktop-shell run only as a **hosted** SDL2/Cocoa/Win32 app; never launched by `os_main`; `_init_display_service()` is a stub returning true |
| multiuser-sec | Missing | Missing | foundational | No uid/gid/euid credential model; file permission bits modeled but never enforced (no DAC on open); ASLR seed collected but never applied; capability gates dead (ring-3 never runs) |
| init-services | Partial (code, unwired) | Partial (code, unwired) | foundational | No init/PID1 actually runs; topo-sort service manager never instantiated; `init_all_services()` test-only; no persistent log, no graceful shutdown, no NTP |
| server-ops | Partial (code, unwired) | Missing | foundational | SSH remote exec is a fixture / 6-builtin toy REPL; sshd single-connection; daemons launch via the broken spawn primitive; zero rlimit/cgroups/quotas |

---

## 3. Foundational gaps — the shared roots underneath everything

These are **cross-cutting root causes**, not a re-list of the 11 domains. Ordered by dependency: each unlocks the next. The first is the keystone; #2–#6 are largely dead at runtime until #1 runs.

### G1 — KEYSTONE: no real ring-3, FS-launched process in the booted kernel
The generic `fs_exec_spawn` returns a **phantom pid** and never maps PT_LOADs or enters ring-3 (session fact). The real handoff (`x86_64_fs_exec_ring3.spl`) is reachable only from harness/`app_loader`, and it is **single-shot** (QEMU exit, no return-to-caller — the scheduler is bypassed). The two boots that actually run:
- **RISC-V:** `os_main()` branches only to `start_http_server_baremetal()` or `serial_shell_main()` — `src/os/kernel/boot/os_main.spl:43,50`. No scheduler loop, no ring-3.
- **x86_64:** the QEMU-spec entry is the `fs_exec_entry.spl` probe fixture; it prints fabricated `ELF_LOAD_OK`/`pid=1002` via C stubs and never creates a task.

Until a filesystem program runs as an isolated ring-3 process **and control returns to the scheduler on its exit**, every subsystem below is unreachable in the shipped image. This is the single highest-leverage fix.

### G2 — no per-process kernel stack (precondition for safe preemption)
`TaskControlBlock.kernel_stack` is hardcoded `0` at **every** task-creation site — `scheduler_task_mgmt.spl:80`, `scheduler_exec.spl:212` and `:263`, `scheduler_arm_bootstrap.spl:127`. There is no kernel-stack allocator anywhere, and nothing sets `TSS.RSP0` on switch. Without a distinct kernel stack per task, safe preemption, nested syscalls, and per-task trap entry are impossible.

### G3 — the trap/syscall/paging runtime is never installed in the production boot
`install_syscall_entry` (programs `MSR_EFER.SCE`/`STAR`/`LSTAR`/`SFMASK`) exists only in `arch/x86_64/cpu.spl` and `arch_init.spl`, invoked only from example/harness entries — not from the booted kernel. The IDT install (`x86_install_runtime` / `Idt.install_runtime`), the page-fault ISR (IDT vec 14), and `arch_x86_64_early_init` are likewise harness-only on x86_64. So even if a ring-3 program ran, it could not trap into the kernel, take a page fault, or issue a syscall. (`gdt_init` is additionally reported dead + non-compiling — session fact.)

### G4 — timer IRQ is not wired to the scheduler; the handoff never returns
`.timer_tick(` / `.schedule(` are called only from unit-test specs, never from an arch interrupt handler. The RISC-V timer IRQ leaves the hook commented: `# scheduler_tick()` at `arch/riscv64/timer.spl:166`. Combined with the single-shot G1 handoff, this means **no preemption and no return-to-scheduler**: a hung app freezes the machine and `exit/wait/reap`/pick-next never run against a live process.

### G5 — COW fork and demand paging do not work end-to-end
`vmm_handle_cow_fault` (`vmm_vma.spl:330`) has **zero callers** — the page-fault ISR routes write faults to the anon handler, which allocates a fresh zeroed page over the RO page → **silent data corruption after fork**. Separately, the kernel `fork` syscall (`syscall_process.spl:161`) does not COW-clone the address space at all (only `pm_service.fork` does). The ISR also ignores the x86 error code, so there is no protection-fault routing and no stack/guard-page auto-grow. And the wired demand-paging ISR never fires in the booted image (G3). Real `fork/exec` of programs is therefore unusable.

### G6 — no user identity, no enforced DAC, no real signal delivery
There is **no uid/gid/euid credential model** anywhere in the kernel; tasks carry `TaskId` but no user. `FsNode.permissions`/`owner` are modeled (`fs_types.spl:55-56`) but **never checked on open** — any process could read/write any file. ASLR entropy is collected but never applied (no `randomize`/`load_base` usage). POSIX signal *delivery* is a stubbed extern ("real implementations live in C", `signal_dispatch.spl`) — no `sigaction`, trampoline, or per-process mask. The capability subsystem is genuinely fail-closed (`capability.spl:78` `return false` on no record) but its gates are dead because ring-3 never runs (G1). Multi-user isolation and privilege separation cannot exist without these.

> **Note on layering:** journaled/cached persistent FS, a functional socket API + running netstack + x86_64 net, init/PID1 + graceful shutdown + persistent log, a GUI compositor boot, AF_UNIX/futex/epoll, and resource limits/cgroups all layer **above** G1–G6. They are captured in §4 and the build order, not here.

---

## 4. Domain-specific gap lists (layered above the foundation)

### Desktop-specific
- **No native display server boot.** The compositor is only ever constructed with **hosted** backends (`HostedSdl2Backend`/`HostedCocoaBackend`/`HostedWin32Backend`) — a demo app running *on* Linux/macOS/Windows. `os_main` never launches it; `_init_display_service()` (`init_services.spl:132`) is a stub that returns `true` without instantiating `DisplayService`.
- **PS/2 keyboard/mouse never routed into a running in-guest compositor** — the drivers read real ports but have no boot-time event-loop consumer and are not interrupt-driven (no IDT handler registered).
- **Audio entirely stubbed** — `hda_controller.spl:216` "Hardware register writes are stubbed."
- **App launch is faked** — `launcher_launch` calls `posix_spawn`, which fails on the baremetal lane; the main loop "returns true regardless of spawn errno."
- **No cross-app clipboard, drag-and-drop between processes, session manager, or login/seat.**
- Multi-window desktop is impossible until G1 (isolated ring-3 apps) + real IPC exist.

### Server-specific
- **App networking is `ENOSYS`.** `socket/bind/connect/listen/accept/send/recv` (syscalls 70-77) forward to `_forward_net_ipc`, which returns `-38 ENOSYS` (`syscall_net.spl:136`). No program can open a connection.
- **The Simple TCP/IP stack is never bound to a NIC and never started as a service** — `net_boot_init` initializes the C `rt_net` driver, not `VirtioNetDriver`, so `driver.initialized=false`; the stack is only invoked from `tools_test.spl`.
- **The only real wire path is a single hardcoded RISC-V C connection** (globals; listen fd 100 / client fd 200) with **canned HTTP/SSH payloads**; no per-connection table, no backlog, no x86_64 net runtime.
- **SSH remote exec is a fixture / 6-builtin toy REPL** (`ssh_remote_shell.spl`, `ssh_session_channel.spl:42`); sshd is **single-connection** (sequential `accept_loop`).
- **No AF_UNIX, futex, epoll, POSIX shm/mq** — scalable event-driven and shared-memory server architectures are impossible; only a 64-fd `poll` exists.
- **No storage durability:** no journaling/crash-consistency on the persistent FS → data loss on power failure; `fsync` is a no-op / never reaches the NVMe flush command; no page/buffer cache in the live path (`BlockCache` is dead code); NVMe pure-Simple read returns only the first 4KB cluster.
- **No swap, no OOM killer, no reclaim, no per-process memory limits, PMM capped at 4GB** — a server under memory pressure panics.
- **No resource limits / quotas / cgroups anywhere** (grep-clean) — no safe multi-tenant or under-load operation.
- **No real init/PID1, no reaping, no persistent log (journald-equivalent), no time sync (NTP), no graceful shutdown** — `reboot()` is a hard `0xCF9` reset with no fs sync/unmount.

---

## 5. What already works — due credit (grounded)

The through-line: **substantial, honest, kernel-grade code exists; the gap is that it is untriggered in the booted image, not that it is fake.**

- **Real context switching:** inline-asm GPR save/restore for x86_64 (`scheduler/context_switch.spl:32-121`) plus per-arch `rt_<arch>_context_switch` bridges. A real EEVDF/CFS-like + RT + deadline multiclass SMP scheduler with COW fork, exec image build, and capability-aware exit/reap (~4850 lines).
- **Real memory building blocks:** bitmap PMM with per-page refcounting for COW; fresh per-process PML4 that copies only the kernel half (`vmm_address_space.spl:64`); VMA-based `mmap/munmap/mprotect`; anon+file demand-paging handlers wired to IDT vec 14; mimalloc kernel heap.
- **Real storage I/O:** NVMe driver programming BAR0 MMIO CAP/VS/CC/CSTS/AQA with DMA (1674 lines); **writable block-level FAT32** with cluster allocation, FAT-chain extend/free/truncate, directory-entry create, and `write_file_data` submitting opcode 0x01 to the NVMe I/O queue.
- **Production-grade syscall safety:** page-table-walking user-pointer validation checking PRESENT|USER|WRITABLE with overflow guards and per-page VMA-flag checks returning `EFAULT` (`vmm_copy.spl:255-521`), plus grant-table bounded safecopy. This is not a demo — it is real.
- **Real security primitives:** **W^X genuinely enforced** in x86_64 paging (`paging.spl:284-301`, never W+X, sets NX bit 63); **fail-closed capabilities** with monotonic pledge/unveil and generation-counter revocation (`capability.spl:78`); compiler-lowered pledged cap sets with fail-closed baremetal MPU.
- **Real networking code:** a ~5000-LOC Simple TCP/IP suite (ARP/IPv4/IPv6/ICMP/TCP state machine/UDP/SCTP) + a real Simple VirtIO-net driver; a real minimal baremetal TCP that does a genuine 3-way handshake on RISC-V; an SSH daemon with **real crypto** (curve25519/ed25519/AES-GCM) that proves login + auth.
- **Real device programming:** PCI method-1 scan, APIC/IDT/PIC, HPET/TSC timers, CMOS RTC, PS/2 keyboard/mouse port reads, xHCI 64-bit MMIO, framebuffer MMIO pixel writes with 8x16 font glyphs.
- **Real design surface for ops:** Kahn topo-sort service manager with restart/backoff/quarantine policy, a Minix-style reincarnation server, an IPC-based driver supervisor health loop, a kernel log ring buffer.

---

## 6. Recommended build order (dependency-correct milestones)

Each milestone is a runtime gate: it is "done" only when demonstrable in the **booted** kernel, not a harness.

**M0 — Boot the real kernel (not the probe fixture).** Replace the x86_64 `fs_exec_entry.spl` probe with a real entry that runs `arch_x86_64_early_init`: install GDT + TSS, IDT (with the page-fault ISR), and the SYSCALL MSR entry. Fix the dead/non-compiling `gdt_init`. *Gate: booted kernel installs a working trap runtime.* (Closes G3.)

**M1 — One real ring-3 FS-launched process.** Allocate a per-process kernel stack (kill `kernel_stack:0`) and set `TSS.RSP0` on entry; map the ELF's PT_LOADs; enter ring-3; complete a `ring3 → syscall → ring3` round-trip; and **return to the scheduler on the process's `exit`** instead of exiting QEMU. *Gate: `/bin/hello` runs from FAT32, prints via a real syscall, exits, and the kernel keeps running.* (Closes G1, G2; the keystone.)

**M2 — Preemptive multitasking.** Wire the arch timer IRQ to `scheduler.timer_tick` (uncomment/implement `arch/riscv64/timer.spl:166` and the x86_64 APIC-timer equivalent); context-switch between two ring-3 tasks; verify a spinning task does not freeze the machine. *Gate: two processes time-slice.* (Closes G4.)

**M3 — Correct fork/exec + demand paging.** Wire `vmm_handle_cow_fault` into the page-fault ISR (route by error-code write/present bit); make the kernel `fork` syscall COW-clone the address space; add stack guard-page auto-grow; drive `exit/wait/reap` against live children. *Gate: `fork`+`exec`+`wait` of a real program with no post-fork corruption.* (Closes G5.)

**M4 — Signals + threads.** Real signal delivery (`sigaction`, user trampoline, `sigreturn`, per-process pending/mask) and a minimal thread model (tid, CLONE_VM). *Gate: Ctrl-C and SIGCHLD reaping work.* (Closes the rest of G6's signal half.)

**M5 — Persistent, durable, cached FS.** Add journaling/crash-consistency to the writable FS (or persist `nvfs`'s intent-log to disk); route reads/writes through the `BlockCache` (LRU + writeback); make `fsync` reach the NVMe flush command; add a handle→mount table so multiple mounts work by fd; fix the NVMe reader to follow full cluster chains. *Gate: survives power-cut without corruption; multiple mounts usable.*

**M5.5 — Memory at scale.** Swap (page-out/in, kswapd), an OOM killer, reclaim/writeback, per-process memory limits, and lift the 4GB PMM ceiling. *Gate: server survives memory pressure without panic.*

**M6 — Real networking.** Make `socket()` (syscalls 70-77) functional instead of `ENOSYS`; run `NetstackService` bound to the initialized `VirtioNetDriver` on IPC port 2; provide an x86_64 `rt_net`/`rt_boot_tcp` runtime; add loopback, DHCP client, and an in-OS DNS resolver; generalize TCP to a multi-connection socket table. *Gate: an ordinary FS-launched program opens an outbound connection and a server accepts multiple clients.*

**M7 — Users & security.** Add a uid/gid/euid credential model carried to the syscall boundary; enforce DAC on `open` (return `EACCES`); apply the ASLR seed to load/mmap bases; add a persistent account DB + console login. *Gate: two users cannot read each other's files; services drop privilege.* (Closes G6's identity/DAC half.)

**M8 — init/PID1 + services.** Instantiate the `InitService` topo-sort manager as a real PID1 launching supervised isolated daemons; route real process exits into `handle_service_exit` (reaping/restart); add a persistent, rotated log (journald-equivalent) and a graceful shutdown that drains services + syncs/unmounts filesystems + does ACPI S5; add RTC→clock seeding and an NTP client. *Gate: a crashed daemon is restarted; a clean shutdown loses no data.*

**M9-desktop — Native display server.** Wire a boot-time compositor run loop binding `fb_driver` + PS/2 input (interrupt-driven) + the WM IPC protocol; launch it from `os_main` (not a hosted backend); add a session/login manager and a cross-app clipboard. *Gate: a filesystem-launched program opens an isolated window on the SimpleOS framebuffer with routed input.*

**M9-server — Concurrency & multi-tenancy.** Thread-per-connection / worker pools / `epoll`; AF_UNIX sockets; futex; real SSH remote exec (launch actual programs, not the fixture REPL); resource limits / cgroups for CPU/memory/process caps. *Gate: sshd serves concurrent real sessions under enforced limits.*

---

## Open questions carried forward (unclear — needs deeper check; not laundered into claims)

- Whether `desktop_e2e_entry`'s installed path actually completes a `ring3 → syscall → ring3` round-trip (out of the audited domains' confirmable scope).
- Whether any arch's `kernel_main → memory_init` tail eventually reaches `init_all_services` on a non-x86 target (x86_64 confirmed it does not; not all arches traced).
- xHCI port/device enumeration completeness and whether any keyboard/NIC IRQ fires end-to-end.
- Whether an alternate x86_64 `rt_net`/`rt_boot_tcp` provider exists outside `arch/riscv64` (grep found these symbols only under RISC-V).
- Whether `green_carrier`/`green_task` (cooperative userspace runtime) is intended as the real concurrency path vs. the preemptive TCB scheduler.
- Whether `loader_exec` (`kernel/loader/loader_api.spl:159`) maps PT_LOADs when reached (the reachable generic path does not, per session facts).
