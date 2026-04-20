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
- **Status:** Open
- **Requested-semantics:**
  Replace the current flat default `SchedulerTopology` with hardware-discovered
  scheduler domains for SMT siblings, shared-cache/package groups, and NUMA
  nodes. The flat topology must remain the fallback for tests and early boot.
- **Acceptance-criteria:**
  - [ ] Boot-time topology discovery populates `SchedulerTopology.domains`.
  - [ ] Domain kinds distinguish `Smt`, `Cache`, and `Numa` where available.
  - [ ] Rebalance and wake-affine placement prefer local domains before wider
        domains.
  - [ ] Scheduler specs cover flat fallback and at least one synthetic
        multi-domain topology.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/07_guide/platform/sosix_process_scheduler.md`
- **Related-issue:** none
- **Notes:** The current implementation has typed topology records but one flat
  domain over the logical CPU catalog.

### FR-SOS-018 — Add idle-path balancing and full wakeup preemption

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Extend the conservative unblock/timer rebalance hooks with idle-pull
  balancing and fair-class wakeup preemption. Woken interactive/fair tasks
  should be able to preempt when their eligible virtual deadline is earlier
  than the current running task and affinity/topology policy allows it.
- **Acceptance-criteria:**
  - [ ] Idle CPUs pull one affinity-compatible fair/background task from the
        nearest overloaded domain before running idle.
  - [ ] Wakeup-preemption metadata is recorded without corrupting current task
        context.
  - [ ] Fair wakeup tests cover earlier-deadline wakeups, non-eligible tasks,
        and affinity-blocked wakeups.
  - [ ] Existing scheduler class pick order remains deadline, RT, fair,
        background, idle.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/05_design/scheduler_process_isolation.md`
- **Related-issue:** none
- **Notes:** Current hooks are deliberately conservative and do not yet model
  full EEVDF sleeper decay or preemption.

### FR-SOS-019 — Add RT bandwidth throttling and priority inheritance

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Add safety controls before exposing unrestricted realtime policy to user
  workloads: global/per-CPU RT bandwidth throttling and priority-inheritance
  mutex support for bounded priority inversion.
- **Acceptance-criteria:**
  - [ ] RT runtime accounting throttles RT queues when their configured budget
        is exhausted.
  - [ ] Throttled RT tasks cannot starve fair/background tasks indefinitely.
  - [ ] Priority-inheritance mutex tests cover boosting, nested waiters, and
        priority restoration on unlock.
  - [ ] `schedctl` exposes only safe RT policy transitions.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/05_design/scheduler_process_isolation.md`
- **Related-issue:** none
- **Notes:** Current RT behavior picks by static priority but does not enforce
  bandwidth reservations.

### FR-SOS-020 — Complete deadline CBS and deadline-miss tracing

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os scheduler
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Extend deadline admission into a full EDF plus CBS runtime model with budget
  replenishment, per-task deadline-miss counters, and scheduler trace events.
- **Acceptance-criteria:**
  - [ ] Runtime budget is consumed and replenished by period/deadline rules.
  - [ ] Tasks that overrun budget are delayed or demoted according to CBS
        policy instead of continuing indefinitely.
  - [ ] Missed deadlines increment an observable counter.
  - [ ] Scheduler trace output records admit, replenish, overrun, and miss
        events.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/05_design/scheduler_process_isolation.md`
- **Related-issue:** none
- **Notes:** Current deadline support validates budget tuples and per-CPU
  utilization but does not yet implement replenishment.

### FR-SOS-021 — Add safe execve argv/envp copy-in helpers

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os process lifecycle
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Add reusable, validated user-memory helpers for `copyin_u64` and
  NUL-terminated argv/envp vector copy-in. Helpers must validate each pointer,
  enforce argument count and byte caps, detect termination, and safely read
  across user mappings before `build_user_process_image`.
- **Acceptance-criteria:**
  - [ ] `execve(path, argv, envp)` passes copied vectors to
        `build_user_process_image`.
  - [ ] Invalid vector pointers return `-14` without replacing the current
        process image.
  - [ ] Oversized argument lists return `-7` or another documented errno-style
        value without partial image replacement.
  - [ ] Specs cover empty vectors, multi-argument vectors, invalid pointers,
        and missing NUL termination.
- **Related-upfront:** `doc/04_architecture/scheduler_process_isolation.md`
- **Related-design-doc:** `doc/07_guide/platform/sosix_process_scheduler.md`
- **Related-issue:** none
- **Notes:** The current kernel has bounded byte-copy helpers and copyout
  validation, but not a shared string-vector copy-in primitive.

### FR-SOS-022 — Populate dataset_create_from_file from VFS bytes

- **Filed-on:** 2026-04-20
- **Filed-by:** Codex scheduler/process follow-up
- **Target:** simpleos-os SOSIX sharing
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Change `dataset_create_from_file(fd, offset, len, flags)` from an ABI-shaped
  sealed-handle stub into a real immutable byte snapshot populated from the VFS
  or open-file-description layer.
- **Acceptance-criteria:**
  - [ ] The syscall resolves `fd` to the current task's open file description.
  - [ ] It reads exactly the requested byte range or returns an errno-style
        failure without leaking a dataset slot.
  - [ ] The returned dataset is sealed and readable through dataset map/read
        operations.
  - [ ] Specs cover valid snapshots, invalid fd, out-of-range reads, and
        failure cleanup.
- **Related-upfront:** `doc/04_architecture/sosix_process_sharing.md`
- **Related-design-doc:** `doc/07_guide/platform/sosix_process_scheduler.md`
- **Related-issue:** none
- **Notes:** The current syscall path lacks a clean synchronous fd/offset/len
  byte snapshot API that does not couple directly to VFS service internals.
