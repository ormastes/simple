# ARM32 scheduler user-entry adoption remains blocked

Status: prerequisite implemented, unverified by user instruction.

The authenticated ARM32 mapper now uses the shared four-byte SysV stack
builder, maps the occupied stack pages, binds PT_LOAD mapping and teardown to
the canonical load-consumer lifecycle, and provides generation-bound
`MappedBlocked -> AdoptionReserved -> MappedBlocked` rollback before loader
token consumption. These transitions remain non-authorizing.

ARM32 execution readiness must remain false until one scheduler-owned
transaction consumes the reserved mapping as an owned move, reserves a TCB and
lifecycle generation, installs capability/vmspace/observation state with full
rollback, consumes the matching loader joint reservation exactly once, and
performs the architecture handoff. The architecture leaf must install TTBR0,
invalidate and synchronize translation state, enter unprivileged mode at the
exact ELF entry and initial SP, handle SVC result/exit, and reap the exact PID.

Static source/spec review cannot prove those runtime transitions. Resume with
the ARM32 scheduler adoption owner and entry leaf; keep
`executable_target_arch_process_image_ready_v1("arm") == false` until the
filesystem-backed QEMU transcript proves guest entry, mounted program output,
exit 37, exact reap, and `TEST PASSED`.

## 2026-08-24 scheduler-move prerequisite

The page-table capsule now supports an exact
`AdoptionReserved -> SchedulerOwnedUnpublished -> SchedulerOwnedPublished ->
SchedulerTerminal -> Destroyed` move bound to task ID and lifecycle generation.
A stale receipt cannot roll back, publish, terminate, or reap a later state.
Only the unpublished state can roll back; only terminal state can reap.
The immutable entry state binds the 16 KiB-aligned TTBR0 root, word-aligned
entry, eight-byte-aligned SP, and one-shot execution token. Its hardware
installer uses `DSB -> TTBR0 -> TLBIALL -> DSB -> ISB` and reads back the root.

Global readiness remains false. Scheduler must still publish the receipt with
its TCB, invoke entry, bind SVC/exit to the same lifecycle, restore the kernel
root, and reap during wait collection. No runtime verification ran.
