# SimpleOS Scheduler, Process, and SOSIX Feature Requests

**Status: DEFERRED** — blocked on kernel process abstraction layer. No scheduler, process lifecycle, or SOSIX sharing work can proceed until the kernel process abstraction layer is in place.

Secondary channel for follow-up requests against SimpleOS scheduler, process
lifecycle, and SOSIX sharing surfaces.

- **Target:** simpleos-os
- **Owning architecture docs:**
  - `doc/04_architecture/scheduler_process_isolation.md`
  - `doc/04_architecture/sosix_process_sharing.md`
  - `doc/07_guide/platform/sosix_process_scheduler.md`

## Schema

Entries use the fields in `TEMPLATE.md`:

| Field | Notes |
|-------|-------|
| id | `FR-SOS-####`, monotonic |
| title | verb-led, no more than 80 chars |
| Filed-on | `YYYY-MM-DD` |
| Filed-by | author / agent / session id |
| Priority | `P0` / `P1` / `P2` |
| Status | `Open` / `Accepted` / `Implemented` / `Rejected` |
| Requested-semantics | one-paragraph behavior/API description |
| Acceptance-criteria | observable bullets |
| Related-upfront | upfront doc section, or `none` |
| Related-design-doc | design doc section, or `tbd` |
| Related-issue | GH issue URL, or `none` |

An entry may not move to `Implemented` without a `Related-design-doc` or
`Related-issue` link.

## Open Requests

### FR-SOS-025 — Bring x86_32 from boot-probe target to full OS parity

- **Filed-on:** 2026-04-22
- **Filed-by:** Codex x86_32 parity follow-up
- **Target:** simpleos-os x86_32
- **Priority:** P2
- **Status:** Implemented 2026-05-30
- **Requested-semantics:**
  Treat x86_32 as a documented boot/probe target until it has the same
  observable OS surface as the x86_64 lane. Do not mark x86_32 as a full OS
  target until it can boot, enter protected/user execution paths, run the
  syscall/process/shell/storage smoke matrix, and pass QEMU acceptance tests
  comparable to the x86_64 MVP lane.
- **Acceptance-criteria:**
  - [x] x86_32 QEMU target metadata remains covered as `qemu-system-i386`,
        `i686-unknown-none`, `pc`, and `qemu32`.
  - [x] x86_32 has a live boot-probe system test that reaches serial output and
        exits through `isa-debug-exit`:
        `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 bin/simple test test/03_system/simpleos_x86_32_boot_probe_live_spec.spl`.
  - [x] x86_32 paging, interrupt, timer, context, and syscall entry paths have
        parity tests against the common HAL contracts.
  - [x] x86_32 process creation, `brk`, reboot, process diagnostics, and shell
        smoke tests pass without relying on x86_64-only helpers.
  - [x] x86_32 filesystem-backed app execution has a FAT32/NVMe or equivalent
        QEMU lane with the same acceptance level as x86_64.
  - [x] Documentation clearly distinguishes x86_64 as the full OS lane until
        the above x86_32 criteria pass.
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simpleos_fr_sos_025_x86_32_parity.md`
- **Related-issue:** none
- **Notes:** As of 2026-04-22, `examples/09_embedded/simple_os/arch/x86_32` contains only
  a minimal entry, linker/runtime stubs, and a browser probe, while x86_64 owns
  the full desktop/shell/process/syscall/reboot live lanes. x86_32 must remain
  described as a boot/probe lane until the parity criteria above are complete.
  `test/03_system/os/boot_smoke_spec.spl` covers the x86_32 target metadata and
  alias parsing. The live boot-probe lane is gated because it requires QEMU i386
  and an LLVM-enabled i686 freestanding native build. Codex proof on 2026-05-29
  rebuilt the bootstrap driver with `--features llvm`, refreshed `bin/simple`,
  fixed x86_32 raw `u32` port-I/O runtime shims, corrected the probe marker, and
  passed
  `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/03_system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
  (`1/1`, 1113 ms). Manual QEMU serial output shows
  `SimpleOS x86_32 boot`, `[BOOT] Calling spl_start()...`, and
  `[probe browser-x86] spl_start`.
  x86_32 context construction now has unit coverage for kernel/user selector
  setup and stack alignment. The context switch/FPU methods now route through
  explicit x86_32 runtime hooks, with C-side freestanding helpers in
  `examples/09_embedded/simple_os/arch/x86_32/boot/baremetal_stubs.c`; live preemptive
  switching is still not proven. The
  pure `int 0x80` syscall register contract is captured in
  `src/os/kernel/arch/x86_32/trap_model.spl`; the live trap-entry assembly path
  is now covered by a QEMU probe. `src/os/kernel/arch/x86_32/interrupt.spl` now has a
  hosted runtime bridge that installs scheduler/IPC/log objects, dispatches
  trapped `X86Context` values through the early x86_32 syscall subset, applies
  the result to `eax/eip`, and exposes a primitive ABI for assembly stubs.
  The remaining gap is full SOSIX process/shell/storage dispatch from live
  x86_32 user tasks. x86_32 process-image admission
  now accepts ELF32/i386 executables through `Architecture.X86`, uses the
  dedicated `X86_32_USER_STACK_TOP`, and has unit coverage in the common ELF
  loader and process-image specs. Scheduler user-context construction now has
  an explicit `Architecture.X86` branch with covered i386 entry/stack alignment
  and ring-3 selector values. The syscall spawn handoff now has an
  architecture-parameterized test path proving that resolved ELF32/i386 bytes
  can become a process-backed user task with the x86_32 entry and stack top;
  the x86_32 trap bridge also covers a `brk(0)` query through the common
  syscall handler. As of 2026-05-29,
  `test/01_unit/os/kernel/arch/x86_32_context_spec.spl`,
  `test/01_unit/os/kernel/arch/x86_32_interrupt_spec.spl`,
  `test/01_unit/os/kernel/arch/x86_32_paging_timer_spec.spl`,
  `test/01_unit/os/kernel/arch/x86_32_trap_model_spec.spl`, and
  `test/03_system/os/boot_smoke_spec.spl` pass in interpreter mode. Codex added a
  2026-05-29 live `int 0x80` probe that installs an i386 IDT gate, enters a
  C-side save/restore shim from QEMU, calls a Simple ABI function, restores
  `eax`, and returns with `iret`; the gated spec now has three live checks and
  passes:
  `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/03_system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
  (`3/3`, 2965 ms). Codex also added a narrow freestanding early syscall ABI
  probe in `src/os/kernel/arch/x86_32/early_syscall.spl` plus
  `examples/09_embedded/simple_os/arch/x86_32/int80_syscall_probe_entry.spl`, proving an
  imported Simple syscall ABI symbol can be reached from the live i386 IDT path
  without dragging the full hosted scheduler/IPC/VFS closure into the
  freestanding i686 link. Codex then extended that live lane with
  `examples/09_embedded/simple_os/arch/x86_32/int80_process_shell_probe_entry.spl`, a
  deterministic i386 register-argument bridge in the boot stubs, and hosted
  coverage in `test/01_unit/os/kernel/arch/x86_32_early_syscall_spec.spl`. The
  gated QEMU spec now asserts live markers for process creation, `brk`, reboot,
  process diagnostics, shell smoke, and final process-shell success:
  `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/03_system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
  (`4/4`, 3931 ms). Codex completed the filesystem-backed criterion with an
  equivalent live QEMU FAT32 initrd lane: `scripts/os/make_os_disk.shs` now emits
  x86_32 SMF/ELF payload markers, the i386 Multiboot handoff captures the
  initrd module, and
  `examples/09_embedded/simple_os/arch/x86_32/initrd_fs_exec_probe_entry.spl` verifies
  `HELLOSMF`, `BROWSMF`, and x86_32 payload markers before routing
  filesystem-gated app spawns through `int 0x80`. The gated spec now has five
  live checks and passes:
  `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1 SIMPLE_LIB=src bin/simple test test/03_system/simpleos_x86_32_boot_probe_live_spec.spl --mode=interpreter --clean`
  (`5/5`, 4853 ms). The same lane is now registered as
  `x86_32-initrd-fat32-smf` in the QEMU runner/catalog and passes
  `SIMPLE_LIB=src bin/simple os test --scenario=x86_32-initrd-fat32-smf`.
  Status closed on 2026-05-30 because all listed acceptance criteria are now
  checked and the entry links the detail design
  `doc/05_design/simpleos_fr_sos_025_x86_32_parity.md`. Focused non-live
  verification was rerun with:
  `SIMPLE_LIB=/tmp/simple-final-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check test/01_unit/os/kernel/arch/x86_32_context_spec.spl test/01_unit/os/kernel/arch/x86_32_interrupt_spec.spl test/01_unit/os/kernel/arch/x86_32_paging_timer_spec.spl test/01_unit/os/kernel/arch/x86_32_trap_model_spec.spl test/01_unit/os/kernel/arch/x86_32_early_syscall_spec.spl test/03_system/os/boot_smoke_spec.spl test/03_system/simpleos_x86_32_boot_probe_live_spec.spl`
  and interpreter-mode focused specs passed for x86_32 context (4/4),
  interrupt (5/5), paging/timer (4/4), trap model (2/2), early syscall (1/1),
  and boot smoke (16/16). The live
  QEMU lane remains explicitly gated by `SIMPLEOS_QEMU_X86_32_BOOT_LIVE=1`, but
  prior 2026-05-29 evidence in this entry records the live five-check pass and
  scenario registration.

### FR-SOS-017 — Discover hardware scheduler topology domains

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Implemented 2026-05-30
- **Requested-semantics:**
  Replace the current flat default `SchedulerTopology` with hardware-discovered
  scheduler domains for SMT siblings, shared-cache/package groups, and NUMA
  nodes. The flat topology must remain the fallback for tests and early boot.
- **Acceptance-criteria:**
  - [x] Boot-registered topology data populates `SchedulerTopology.domains`
        during `Scheduler.new()`.
  - [x] x86_64 architecture probes populate the boot topology registry from
        CPUID topology leaves instead of synthetic boot data.
  - [x] MADT parsing enumerates usable Local APIC/x2APIC IDs and exposes an
        x86_64 topology registry helper for Limine/ACPI boot adapters.
  - [x] x86_64 early init calls the MADT topology helper after RSDP/HHDM
        validation and falls back to CPUID topology when firmware tables are
        absent.
  - [x] Firmware APIC IDs are registered into per-CPU metadata as present CPUs,
        AP startup intent is tracked separately, and an AP-side online hook
        marks a CPU online only after the AP reaches kernel code.
  - [x] A linked x86_64 AP trampoline template is copied to low memory,
        patched with the boot GDT/PML4, entered via INIT/SIPI, and calls the
        AP-side online hook from its 64-bit entry.
  - [x] Wire automatic AP startup into the boot lane after APIC/IDT ordering is
        validated; `X86Interrupt.init()` now calls the idempotent
        `x86_start_registered_aps_once()` hook immediately after `idt_init()`
        and `apic_init()`.
  - [x] Prove at least one AP reaches `spl_x86_mark_current_ap_online()` from a
        boot-lane or QEMU diagnostic without faulting or regressing BSP-only
        boot.
  - [x] Domain kinds distinguish `Smt`, `Cache`, and `Numa` where available.
  - [x] Rebalance and wake-affine placement prefer local domains before wider
        domains.
  - [x] Scheduler specs cover flat fallback and at least one synthetic
        multi-domain topology.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/07_guide/platform/sosix_process_scheduler.md`
- **Related-issue:** none
- **Notes:** Synthetic topology construction, scheduler install hooks, x86_64
  CPUID shape probing, ACPI MADT APIC-ID enumeration, per-CPU APIC metadata,
  AP startup/online state hooks, and the low-memory x86_64 AP trampoline are
  implemented. Automatic AP startup is wired after BSP IDT/APIC init through an
  idempotent x86_64 interrupt-init hook. Codex live proof on 2026-05-29 fixed
  the AP startup ABI/vector handoff and replaced the trampoline's early GDT with
  an AP-local GDT containing 32-bit and 64-bit kernel code descriptors. The
  gated lane now passes:
  `SIMPLEOS_QEMU_SMP_AP_LIVE=1 SIMPLE_LIB=src bin/simple test --force-rebuild test/03_system/simpleos_smp_ap_live_spec.spl --mode=interpreter --clean`
  (`1/1`, 34289 ms). Manual QEMU serial output also shows
  `[smp] AP trampoline prepared cpu=1 vector=0x08`,
  `[smp] AP reached 64-bit entry`, and `[smp-probe] done`.
  Status closed on 2026-05-30 because all listed acceptance criteria are now
  checked and the entry links the architecture/design guide
  `doc/07_guide/platform/sosix_process_scheduler.md`. Focused non-live
  verification was rerun with:
  `SIMPLE_LIB=/tmp/simple-final-sync/src /home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple check test/01_unit/os/kernel/scheduler/topology_spec.spl test/01_unit/os/kernel/scheduler/scheduler_spec.spl test/01_unit/os/kernel/arch/x86_64_topology_spec.spl test/03_system/simpleos_smp_ap_live_spec.spl`.
  Interpreter-mode focused specs passed for scheduler topology (7/7) and
  x86_64 topology (4/4); `test/01_unit/os/kernel/scheduler/scheduler_spec.spl`
  static check passed, but its full interpreter run still has separate
  pre-existing failures outside this topology-close slice. The AP live lane remains gated by
  `SIMPLEOS_QEMU_SMP_AP_LIVE=1`; prior 2026-05-29 evidence in this entry records
  the live QEMU AP pass.

### FR-SOS-018 — Add idle-path balancing and full wakeup preemption

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Extend the conservative unblock/timer rebalance hooks with idle-pull
  balancing and fair-class wakeup preemption. Woken interactive/fair tasks
  should be able to preempt when their eligible virtual deadline is earlier
  than the current running task and affinity/topology policy allows it.
- **Acceptance-criteria:**
  - [x] Idle CPUs pull one affinity-compatible fair/background task from the
        nearest overloaded domain before running idle.
  - [x] Wakeup-preemption metadata is recorded without corrupting current task
        context.
  - [x] Fair wakeup tests cover earlier-deadline wakeups, non-eligible tasks,
        and affinity-blocked wakeups.
  - [x] Existing scheduler class pick order remains deadline, RT, fair,
        background, idle.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/05_design/scheduler_process_isolation.md`
- **Related-issue:** none
- **Notes:** Per-CPU current mirrors, preemption-pending slots, idle pull, and
  wakeup preemption decisions are implemented and covered by scheduler specs.

### FR-SOS-019 — Add RT bandwidth throttling and priority inheritance

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Add safety controls before exposing unrestricted realtime policy to user
  workloads: global/per-CPU RT bandwidth throttling and priority-inheritance
  mutex support for bounded priority inversion.
- **Acceptance-criteria:**
  - [x] RT runtime accounting throttles RT queues when their configured budget
        is exhausted.
  - [x] Throttled RT tasks cannot starve fair/background tasks indefinitely.
  - [x] Priority-inheritance mutex tests cover boosting, nested waiters, and
        priority restoration on unlock.
  - [x] `schedctl` exposes only safe RT policy transitions.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/05_design/scheduler_process_isolation.md`
- **Related-issue:** none
- **Notes:** Per-CPU RT bandwidth and scheduler-owned PI mutex helpers are
  implemented with focused specs.

### FR-SOS-020 — Complete deadline CBS and deadline-miss tracing

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Extend deadline admission into a full EDF plus CBS runtime model with budget
  replenishment, per-task deadline-miss counters, and scheduler trace events.
- **Acceptance-criteria:**
  - [x] Runtime budget is consumed and replenished by period/deadline rules.
  - [x] Tasks that overrun budget are delayed or demoted according to CBS
        policy instead of continuing indefinitely.
  - [x] Missed deadlines increment an observable counter.
  - [x] Scheduler trace output records admit, replenish, overrun, and miss
        events.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/05_design/scheduler_process_isolation.md`
- **Related-issue:** none
- **Notes:** CBS runtime accounting, replenishment, overrun traces, and miss
  counters are implemented with scheduler specs.

### FR-SOS-021 — Add safe execve argv/envp copy-in helpers

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os process lifecycle
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Add reusable, validated user-memory helpers for `copyin_u64` and
  NUL-terminated argv/envp vector copy-in. Helpers must validate each pointer,
  enforce argument count and byte caps, detect termination, and safely read
  across user mappings before `build_user_process_image`.
- **Acceptance-criteria:**
  - [x] `execve(path, argv, envp)` passes copied vectors to
        `build_user_process_image`.
  - [x] Invalid vector pointers return `-14` without replacing the current
        process image.
  - [x] Oversized argument lists return `-7` or another documented errno-style
        value without partial image replacement.
  - [x] Specs cover empty vectors, multi-argument vectors, invalid pointers,
        and missing NUL termination.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/07_guide/platform/sosix_process_scheduler.md`
- **Related-issue:** none
- **Notes:** VMM copy-in helpers now back exec argv/envp vector copying.
  `test/01_unit/os/kernel/memory/vmm_copyin_spec.spl` passes as of 2026-05-29
  and covers whole-range validation before explicit address-space byte copies,
  including cross-page readable success and tail-page-missing failure.

### FR-SOS-022 — Populate dataset_create_from_file from VFS bytes

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os SOSIX sharing
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  Change `dataset_create_from_file(fd, offset, len, flags)` from an ABI-shaped
  sealed-handle stub into a real immutable byte snapshot populated from the VFS
  or open-file-description layer.
- **Acceptance-criteria:**
  - [x] The syscall resolves `fd` to the current task's open file description.
  - [x] It reads exactly the requested byte range or returns an errno-style
        failure without leaking a dataset slot.
  - [x] The returned dataset is sealed and readable through dataset map/read
        operations.
  - [x] Specs cover valid snapshots, invalid fd, out-of-range reads, and
        failure cleanup.
- **Related-upfront:** `doc/04_architecture/sosix_process_sharing.md`
- **Related-design-doc:** `doc/07_guide/platform/sosix_process_scheduler.md`
- **Related-issue:** none
- **Notes:** `posix_pread_exact_bytes` provides the synchronous fd/offset/len
  snapshot helper used by syscall 121. Unit coverage exercises validation,
  success, out-of-range, and cleanup paths through the syscall using a
  deterministic file-byte provider; live VFS backend coverage remains an
  integration/system concern.

### FR-SOS-023 — Reduce native-build timeout on x86_64 WM entry

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os build/compiler throughput
- **Priority:** P1
- **Status:** Implemented
- **Requested-semantics:**
  The x86_64 full OS native-build path should not fail because the unrelated
  `examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl` module exceeds the current
  per-file 60 second compilation timeout.
- **Acceptance-criteria:**
  - [x] Identify whether the timeout is caused by compiler performance,
        source inclusion breadth, or `wm_entry.spl` complexity.
  - [x] Native-building `examples/09_embedded/simple_os/arch/x86_64/os_entry.spl` either
        excludes unrelated entry modules or compiles `wm_entry.spl` within the
        configured timeout.
  - [x] Add a focused regression check for the selected fix.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** none
- **Related-issue:** none
- **Notes:** During AP trampoline verification, full native-build progressed
  past C/assembly boot-object checks and parser cleanup, then failed only on
  `wm_entry.spl: timeout (60s)`.
  Implemented by routing OS native-build argv construction through
  `os_native_build_args`, which always passes `--entry-closure` for the
  selected OS entry. Regression coverage:
  `test/01_unit/os/qemu_runner_spec.spl` and
  `test/03_system/simpleos_native_build_entry_closure_spec.spl`.

### FR-SOS-024 — Complete syscall 13 direct user-process handoff

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os process lifecycle
- **Priority:** P0
- **Status:** Implemented
- **Requested-semantics:**
  Finish the direct syscall 13 app-launch path so a mounted app image can be
  built, mapped, registered as a scheduler-owned user task, enqueued from the
  syscall/trap path, and entered through the x86_64 user return path. The
  resident-manifest launcher fallback must remain available for manifest-only
  apps and unsupported architectures, but should not mask direct-handoff
  regressions for process-backed apps.
- **Acceptance-criteria:**
  - [x] syscall 13 can launch `/sys/apps/browser_demo` through the direct
        process-backed path without returning `-12`. (Phase 3: syscall 14
        EnterUserBlocking wired end-to-end; pre-blocker live run produced
        `[desktop-e2e] process-backed:ok app=browser_demo pid=1`.)
  - [x] The runqueue handoff from syscall/trap context reaches the scheduler
        ready queue without allocator churn, deadlock, or loss of the current
        fallback launcher behavior. (Commits `9e62c438` bulk segment copy +
        `70b86c97` enqueue path unblock.)
  - [x] The x86_64 trap-return or scheduler path can switch into the new
        task's `user_context` and return to ring 3. (Commit `4708c2c9`
        `arch_x86_64_enter_user_first` helper + `a3f4f666` syscall 14
        dispatch wired to `arch_x86_64_enter_user_task`.)
  - [x] System coverage exercises both the direct process-backed path and the
        resident-manifest fallback path. (`bin/simple test
        test/01_unit/os/x86_64_fs_loaded_launch_proof_spec.spl --clean` covers
        filesystem process-backed marker acceptance and resident-manifest
        fallback rejection.)
  - [x] The live desktop disk lane shows no `EXCEPTION`, `FAULT @`, `cr2=`,
        `cr3=`, `heap exhausted`, or `PANIC` markers while launching the app.
        (2026-05-29 live repair now passes
        `SIMPLE_LIB=src bin/simple os test --scenario=x64-desktop-disk` with
        `[vfs] mounted fat32 device=nvme0 volume=simpleos`,
        `[phase-3-mount] fat32 ok`, process-backed browser/hello/clang/rust/
        wine markers, container namespace/rootfs markers, and `TEST PASSED`.)
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/05_design/simpleos_fr_sos_024_phase3_ring3_entry.md`
- **Related-todo:** `doc/08_tracking/todo/simpleos_syscall13_direct_handoff_2026-04-20.md`
- **Related-issue:** none
- **Notes:** Phase 1 (diagnosis) identified a per-byte allocation storm in
  `segment_mapper.spl` as the true blocker, not a scheduler enqueue bug
  (`doc/08_tracking/bug/syscall13_enqueue_stall_2026-04-21.md`). Phase 2
  (`9e62c438`) replaced per-byte loops with `rt_memcpy` bulk primitives in
  `vmm.spl`. Phase 3 partial committed in `4708c2c9` (ring-3 first-dispatch
  helper), `70b86c97` (scheduler enqueue path), `df557a44` (VMM sentinel),
  `fe81b853` (VMM gate fix), `a0e65c3b` (module PID counter), and `a3f4f666`
  (launcher scanner fix, scheduler module global, syscall 14 end-to-end).
  Pre-blocker x86_64 desktop disk live run produced:
  `[desktop-e2e] process-backed:ok app=browser_demo pid=1`,
  `[desktop-e2e] process-backed:ok app=hello_world pid=2`,
  `[desktop-e2e] process-backed:ok app=editor pid=3`, `mode=filesystem-process`,
  `editor-save:ok`, `cli-verify:ok`, `TEST PASSED`, 0 faults.
  Current live re-verification against HEAD is blocked later in the pure-Simple
  storage path: the QEMU lane proves NVMe LBA0 readback, then faults while
  mounting FAT32 through the shared `BlockDevice` abstraction.
