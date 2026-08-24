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

## 2026-08-24 canonical-lifecycle wiring audit

An attempted direct wiring was rejected rather than introducing a second task
owner or a copyable destruction capability. The exact blockers in the current
canonical scheduler are:

1. `TaskControlBlock` has no architecture-owned mapping handle. Adding the full
   `SchedulerArm32MappingMoveV1` receipt to this `@repr("C")` ABI record would
   copy an authority-bearing receipt through every task-table update and would
   change the ABI shared by every architecture. A parallel module-global map
   keyed only by PID/lifecycle would instead become a second scheduler owner.
   The safe next step is an opaque, generation-bound mapping handle backed by
   one bounded scheduler-owned table; only that table may retain the ARM32
   owner receipt. Even appending that opaque handle changes this record's size
   and possibly its alignment, so it requires a cross-architecture ABI/layout
   audit and updates to every TCB constructor and whole-record copy site.
2. The generic exit helpers mutate a copied `[TaskControlBlock?]` directly.
   They cannot atomically perform
   `SchedulerOwnedPublished -> SchedulerTerminal` beside the exact Zombie
   publication, nor can `sched_wait_for_collect_impl` prove destruction before
   clearing the TCB slot. These transitions must move under a Scheduler method
   that owns both the task table and the opaque mapping table. The current exit
   path also publishes execution observation before the helper, then closes
   FDs and revokes the launch grant before setting Zombie. Those effects must
   be deferred into the same terminal transaction or gain exact rollback;
   otherwise a failed terminal mark would leave a live task with its resources
   already revoked. Failure to mark terminal must leave the task non-Zombie and
   otherwise unchanged. Failure to reap must leave the Zombie and its handle
   collectable for a bounded retry, and reap observation must occur only after
   mapping destruction succeeds and before success is returned.
3. `address_space_switch.as_switch_to(0)` records the kernel sentinel but does
   not write TTBR0. Therefore it cannot restore a kernel root before ARM32
   mapping destruction. `arch/arm32/paging.spl` does expose the boot kernel root
   to its package through `arm32_active_root_v1`, but this is not a sealed
   restore authority and `user_entry_state_v1` retains only the user root. A boot-sealed,
   read-only kernel-root handle plus a checked
   `DSB -> TTBR0 -> TLBIALL -> DSB -> ISB` restore/readback operation is required
   before SVC exit may mark the mapping terminal.
4. `arch/arm32/user_entry.spl` consumes a runtime `rt_arm32_exec_reap` result;
   it is not wired to the canonical Scheduler's current TCB, Zombie transition,
   or wait/reap transaction. The SVC owner must return an encoded result bound
   to task ID, lifecycle generation, mapping generation/nonce, and execution
   token generation. Raw status alone is insufficient and may not authorize
   teardown.

## 2026-08-24 opaque TCB handle prerequisite

`TaskControlBlock` now appends only a generation-bound opaque mapping locator.
The full ARM32 mapping remains in the canonical page-table owner's existing
four-slot bounded table. Every operation checks handle generation plus task ID and lifecycle
generation; slot reuse cannot make a stale copied TCB authoritative. All seven
constructors initialize the handle explicitly, fork starts absent, and generic
exec rejects a present handle before side effects rather than aliasing or
orphaning the old mapping.
The owner serializes each lookup/transition/store through its existing mutex.
Raw scheduler-ownership transitions are module-private; admission mutates the
canonical slot and returns only its locator, so no caller receives a second
destruction receipt. The shared TCB imports only the architecture-neutral locator contract,
and its size change is encoded as ABI revision 2.

The table exposes the owner-side attach, pre-publication rollback, publication,
terminal, and reap prerequisites. It is not wired into generic exit/wait: the
existing order closes FDs and revokes grants before Zombie publication and
cannot roll those effects back if ARM32 terminal marking fails. Kernel-root
restore and the atomic Scheduler lifecycle transaction remain required before
this blocker can close. This change is statically specified but unverified by
explicit instruction.

The required transaction order is now explicit: reserve the opaque TCB handle;
move mapping ownership; consume the exact loader joint reservation; publish the
TCB without runnable visibility; publish the mapping owner; bind entry and the
one-shot execution-token generation; enqueue only after those publications;
on pre-publication failure remove the unpublished TCB and roll back every
reversible reservation and move exactly once. If a fallible publication fails
after the one-shot loader authority was consumed, the same owner must move that
authority to its explicit terminal quarantine/release state; it may neither
recreate nor retry the consumed token. Exit must restore and read back
the sealed kernel root before terminal publication and before exit side effects
become observable. Wait collection must destroy the exact terminal mapping
successfully before it clears the TCB or publishes reap success. Until all of
those transitions share the canonical Scheduler owner, readiness stays false.
No source wiring was retained and no manual verification was run.

## 2026-08-24 exit/reap transaction review

An attempted source wiring was reverted after independent static ownership
review. Four prerequisites remain before the opaque handle can be connected to
generic exit/wait safely:

1. The scheduler needs an authoritative per-CPU quiescence receipt proving the
   exact task generation is absent from every CPU before its mapping is freed.
   A local TTBR0 read and process-global root value are insufficient on SMP.
2. FD close and server-data grant revoke need explicit complete/retry results.
   Current exit code discards both outcomes, so it cannot atomically publish
   observation and Zombie only after terminal cleanup is retained or complete.
3. The bounded ARM32 owner needs replay semantics for both `Quarantined`
   residual destruction and the case where physical destruction completed but
   load-lifecycle close reporting failed. Neither case may strand a Zombie or
   permanently consume one of four slots.
4. Both public scheduler exit helpers must return an explicit transaction
   result. The legacy `(tasks, id)` result cannot distinguish refusal from a
   successful terminal transition and could incorrectly wake waiters.

The safe implementation point is a canonical mutable Scheduler method that
holds scheduler exclusion, consumes per-CPU quiescence evidence, and commits
the mapping/cleanup/observation/TCB transition with owner-side retry records.
The SVC producer must then call that method with its task/lifecycle/execution
receipt. Readiness stays false. No build, test, SPipe, benchmark, optimizer,
bootstrap, or QEMU command was run.
