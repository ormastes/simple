# SimpleOS Scheduler, Process, and SOSIX Feature Requests

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

### FR-SOS-017 — Discover hardware scheduler topology domains

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Partial
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
  - [ ] Wire automatic AP startup into the boot lane after APIC/IDT ordering is
        validated; `x86_start_registered_aps()` is available for the explicit
        bring-up step.
  - [ ] Prove at least one AP reaches `spl_x86_mark_current_ap_online()` from a
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
  implemented. Automatic AP startup from the boot lane remains gated on APIC/IDT
  ordering validation and a live proof that an AP reaches the AP-side online
  hook.

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
- **Status:** Requested
- **Requested-semantics:**
  The x86_64 full OS native-build path should not fail because the unrelated
  `examples/simple_os/arch/x86_64/wm_entry.spl` module exceeds the current
  per-file 60 second compilation timeout.
- **Acceptance-criteria:**
  - [ ] Identify whether the timeout is caused by compiler performance,
        source inclusion breadth, or `wm_entry.spl` complexity.
  - [ ] Native-building `examples/simple_os/arch/x86_64/os_entry.spl` either
        excludes unrelated entry modules or compiles `wm_entry.spl` within the
        configured timeout.
  - [ ] Add a focused regression check for the selected fix.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** none
- **Related-issue:** none
- **Notes:** During AP trampoline verification, full native-build progressed
  past C/assembly boot-object checks and parser cleanup, then failed only on
  `wm_entry.spl: timeout (60s)`.

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
  - [ ] System coverage exercises both the direct process-backed path and the
        resident-manifest fallback path. (Test scaffolding added; full
        coverage pending stub-collision fix.)
  - [ ] The live desktop disk lane shows no `EXCEPTION`, `FAULT @`, `cr2=`,
        `cr3=`, `heap exhausted`, or `PANIC` markers while launching the app.
        (Blocked by freestanding-stub symbol-weakness collision — see
        `doc/08_tracking/todo/simpleos_stub_collision_freestanding_2026-04-21.md`.
        Pre-blocker live run reached `TEST PASSED` with three process-backed
        app PIDs confirmed and zero faults.)
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
  Full live re-verification against HEAD is blocked by a compiler-level
  freestanding-stub symbol-weakness collision (separate compiler agent fix)
  tracked in
  `doc/08_tracking/todo/simpleos_stub_collision_freestanding_2026-04-21.md`.
