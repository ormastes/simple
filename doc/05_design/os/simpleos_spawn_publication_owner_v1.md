# SimpleOS spawn publication: owned-image prerequisite and remaining cut-set

Date: 2026-09-14. Audited base: `c09965ff667`.

Status: **prerequisite repair only; atomic spawn publication MissingEvidence**.
The user-selected goal remains compiler bootstrap and release inside SimpleOS.
This change neither completes that goal nor enables syscall-13 packet spawn.

## Repaired production path

`Scheduler.create_user_task_from_bytes_pid` now forwards the supplied kernel
values `path`, bytes, argv and envp to `build_user_process_image`. The result
owns its file/segment bytes and checked serialized initial stack. One successful
result flows into `sched_create_user_task_pid_impl`; a preparation error returns
PID zero without a root, VM registration, TCB or queue publication.

The previous scheduler branch referenced undefined staged-process symbols and
used separately written global root fields. That branch is removed, including
the now-unreferenced `g_staged_user_as_*` producer/accessors. The value-returning
architecture adapter now creates the root, preserving x86 private low mappings
and the selected architecture instead of bypassing it through x86 staging.
Legacy ELF/ARM global staging elsewhere remains an independently tracked gap.

The checked builder now returns the actual `Result<UserProcessImage, text>`
instead of `Ok(Result<...>)`; stack/ABI errors therefore reach the outer caller.
Generic and slot-zero image creation check exact stack geometry before root
allocation: nonempty bounded bytes, nonzero aligned SP, no unsigned underflow,
and `SP == stack_top - frame_length`. They do not independently round SP.
The common mapper still requires exact zero success and rejects synthetic roots.

Both image creation routes reserve the canonical paired task/lifecycle identity
after exact mapping and entry validation and store that lifecycle generation.
Root/mapping/entry refusal leaves the identity allocator unchanged. If identity
reservation itself fails, the still-unpublished candidate is passed to its
AddressSpace retirement owner before the producer returns failure.
Exec generation explicitly
remains zero: these generic routes still lack exec rotation and capability/boot
launch lease revocation. Initializing it to one would enable snapshot admission
and allow a lease armed before image replacement to survive that replacement.
Current-execution snapshot and boot launch lease admission therefore stay closed
until their complete lifecycle owner is implemented and verified.
Once a pair is issued it can never be guessed, rolled back, or reused. A later
publication/observation failure may burn that pair: an indeterminate external
owner could already have observed it. This does not justify reserving before
fallible mapping or entry validation that does not consume the identity.
A full task table rejects even for parent PID 0. The bytes path now uses
the common VM-registration call instead of omitting it. Priority, capability
pouch and parent are passed unchanged to that existing common owner.

Fork likewise validates the returned COW root before paired identity
reservation. The non-x86 shallow COW provider has no owned rollback receipt
for a valid root followed by identity refusal; it shares parent tables and
cannot use the generic subtree destructor. That explicit prerequisite is
tracked in `doc/08_tracking/bug/scheduler_cow_identity_refusal_rollback.md`.
The x86 provider still returns unavailable before changing parent mappings.

## Ownership and the unavailable publication API

Input arrays/text in this internal API are already kernel values, **not proof**
of an admitted user snapshot. No constructor turning ordinary arrays, a boolean,
physical addresses, or caller-provided receipts into a publication capability is
introduced. `SpawnPacketV1` remains shape-checked then `-ENOSYS` (`-38`).
`OwnedSpawnPacketSnapshotV1` and a callable `SpawnPublicationOwnerV1` must wait
for the real mapping snapshot producer; the rejected MappingReadLease candidate
is not retried or imported by this slice.

The intended next owner consumes that producer's one-shot snapshot under the
canonical scheduler lock, reserves all bounded state, prepares an unpublished
child mapping, revalidates parent lifecycle/cancellation and authority, then
commits VM record + capability record + TCB + ready queues in one owner revision.
Only its returned assigned PID may become a spawn result. Wait owns a terminal
child result until the parent consumes it once; physical cleanup uncertainty
retains a quarantine record and prevents slot reuse.

## Concrete missing physical authorities

| Needed authority | Current source evidence | Required next change |
|---|---|---|
| Mapping snapshot | `ipc/spawn_packet_admission_v1.spl` admits no user copy | Complete the VM mutation/lifetime cut-set described in `simpleos_spawn_mapping_read_lease_v1.md`; retain its existing NO-GO review history. |
| Root rollback | x86 `destroy_user_address_space` calls `x86_root_retire_v1` and retains root pins/tombstones and frames | Return an exact owner-issued rollback/quarantine receipt; do not infer subtree reuse from a void destructor. |
| VM registration | `ipc/capability.spl` stores by-value `ProcessVmSpace` in a mutable global array and returns no reservation/retirement result | Full lifecycle-bound registry reservation and retirement under the same commit authority. Current PID allocator bounds IDs below `0x40000000`; narrowing is not currently an overflow example, but remains the wrong long-term identity type. |
| Scheduler publication | `me`/returned Scheduler state has no demonstrated exclusion from every IRQ/CPU/legacy mutator | Supply one canonical serialized owner and bounded TCB, capability and both ready-queue reservations. A `me` receiver alone is not exclusion proof. |
| Queue completion | `ReadyQueue.enqueue` silently returns when full; `CpuRunQueue.enqueue` increments accounting even after refusal | Fallible reserve/commit operations with no accounting/publication on refusal. |
| Wait/exit result | `sched_wait_for_collect_impl` removes a zombie after a void address-space cleanup and no VM-registry retirement receipt | Bind terminal result to lifecycle/parent and distinguish consumed result from retained cleanup quarantine; never reuse a slot on unknown cleanup. |
| Exec-bound authority | Generic `sched_exec_image_impl` preserves exec generation while `boot_authenticated_launch_lease_consume_once_v1` compares task/lifecycle/exec coordinates | Keep generic exec generation zero until successful replacement rotates it and invalidates old capability/boot leases under the same owner. |
| Cross-architecture child entry | ARM direct-load mapping does not itself prove checked stack byte delivery; RV64 retirement differs from x86 | Architecture-specific map/stack/entry and retirement evidence before promotion. |

These are release blockers, not optional future enhancements. A host geometry
test or source-contract pass cannot close them. The complete release gate still
requires guest compiler version, compile/run, process exit, persistent NVFS
reboot, and captured candidate-bound evidence.

## Verification limits

Focused executable specs and authored manuals exist. No admitted pure-Simple
test or docgen runner is available in this session; the coordinator confirmed
that fact. SSpec execution, generated-manual completeness, native/CPL0 mapping,
child entry, cleanup fault injection and release evidence are **MissingEvidence**.
Source review and diff checks are useful only for this prerequisite repair.
The separate existing unchecked probe builder still declares `UserProcessImage`
while its selected helper returns `Result<UserProcessImage, text>`; that path
requires its own type/ABI repair before a whole-module readiness claim.
