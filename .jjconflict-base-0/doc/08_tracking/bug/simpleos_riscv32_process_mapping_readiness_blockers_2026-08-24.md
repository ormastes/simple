# SimpleOS RV32 process mapping readiness blockers — 2026-08-24

RV32 ELF admission exists and the bounded initial-stack owner can now serialize
four-byte SysV words, but canonical process-image readiness remains false.

1. `user_address_space.spl` delegates RV32 creation/mapping to generic VMM
   entrypoints instead of an authoritative RV32 paging owner.
2. RV32 paging copies kernel root indices 512 through 1023, while the current
   `0x81000000` user stack falls in copied Sv32 root index 516.
3. `Rv32ContextSwitch.create` sets `SSTATUS_SPP`, selecting supervisor return
   instead of U-mode return.
4. Detailed authenticated mapping evidence is currently available only after
   loader retrieval in image preparation; readiness requires a pre-commit gate
   so malformed evidence cannot consume the one-shot authority.

Until all four are resolved together, `executable_target_dispatch_v1` must
keep `riscv32.process_image_builder_ready = false`.

## 2026-08-24 user-entry prerequisite

The loader registry now has a bounded paired RV32 joint/user-entry lease design
and the architecture leaf prepares a correct U-mode `sret` state (SPP/SIE clear,
SPIE set) only after authenticated ELF layout evidence. This evidence is not an
ownership-bound Sv32 mapping receipt. Generic joint commit cannot
bypass the entry lease. This is intentionally not wired to scheduler
publication and does not change readiness: the authoritative Sv32 mapper and
ownership-bound mapping receipt remain the blocking prerequisites.

## 2026-08-24 rejected authoritative-registry design

Three independent static-review cycles rejected the attempted RV32 Sv32 owner,
so its source and specs were removed rather than retaining unsafe authority.
The final design had fixed caller-constructed PFNs, W+X, arbitrary pages,
replayable raw install plans, quadratic global scans, and direct-release UAF,
but two cross-capsule lifecycle defects remained:

1. Generic `executable_authority_abort_joint_reservation_v1` could still clear
   an active RV32 mapping pin and return the loader slot to `Armed`, reopening
   abort/reissue races while the mapping slot retained frames.
2. Mapping-pin release failure had no retained retry coordinate. Create rollback
   ignored it, while build abort retired an empty slot and reported success,
   permanently stranding the authority pin without observable recovery.

The next implementation must make the loader registry the single transaction
owner for mapping pin issue/release (including generic abort, commit, and revoke
paths), retain a bounded retry record on every indeterminate release, and let
only an architecture-owned exact root-unreachable receipt free frames. It must
also bind every page to authenticated ELF ranges or the computed RW+NX stack,
use PMM-issued provenance only, and expose no replayable physical plan. Until
that transaction is implemented and independently accepted, canonical RV32
process-image readiness remains false.

## 2026-08-24 loader transaction prerequisite

The loader registry now contains the bounded transaction prerequisite described
in `doc/05_design/os/loader/rv32_executable_mapping_transaction_owner_v1.md`.
Generic joint abort, commit, and revoke cannot clear a live RV32 mapping pin;
no RV32 mapping commit exists before authoritative scheduler adoption; and an
indeterminate root release remains `ReleaseRetryable` in the original bounded
slot with a generation-, nonce-, root-, and attempt-bound retry coordinate.

This fail-closes the two cross-capsule lifecycle defects in the rejected design.
It does not close the overall blocker: the authoritative PMM/Sv32 mapper, its
root-unreachable producer, and a registry-backed scheduler adoption consumer do
not yet exist, and readiness remains false.

## 2026-08-24 Sv32 mapper prerequisite

The bounded PMM-provenanced Sv32 mapping owner and architecture-produced
root-unreachable lifecycle now exist in
`src/os/kernel/loader/riscv32_sv32_mapping_owner_v1.spl` and
`src/os/kernel/arch/riscv32/sv32_user_root_owner_v1.spl`. The mapper binds its
create-issued root before installing exact authenticated pages, enforces W^X,
and retains rollback/quarantine state so a failed unmap or indeterminate
registry completion cannot free a reachable frame.

This source is static and unverified under the explicit no-verification
instruction. Readiness remains false. The remaining production boundary is a
registry-backed scheduler adoption move that takes sole mapping teardown
ownership, constructs and maps the RV32 four-byte initial stack, publishes the
TCB, switches SATP, and performs U-mode entry/reap. Filesystem-backed RV32 QEMU
evidence is also still required.

## 2026-08-24 scheduler-adoption static review

An attempted scheduler integration was removed after independent ownership
review rather than retaining an unsafe partial implementation. The existing
three prerequisites do not yet form a transferable process mapping:

1. `riscv32_sv32_mapping_owner_v1.spl` maps authenticated `PT_LOAD` pages but
   does not own or map the four-byte initial stack and retains neither the
   canonical initial SP nor an ownership-bound scheduler identity.
2. `sv32_user_root_owner_v1.spl` has an unused `AdoptionReserved` state, but no
   per-hart `Inactive <-> Active` transitions, SATP readback, kernel-root
   restoration receipt, or terminal transition. A single global active-root
   flag is insufficient for SMP and was rejected.
3. `address_space_switch.spl` can write an arbitrary RV32 root directly. Until
   managed roots are distinguishable and rejected by that raw path, an
   architecture owner cannot prove that detach makes a root unreachable.
4. `TaskControlBlock` carries no opaque RV32 mapping handle. Zombie transitions
   do not first restore the kernel root and mark the exact task generation
   terminal; `wait` destroys a generic address space and clears the TCB even
   when an RV32 registry/root release would need a retry.
5. The mapping-pin transaction is deliberately non-committable through the
   generic joint path while its pin is live. Scheduler adoption therefore needs
   one dedicated registry transition that consumes the exact prepared mapping
   move without reopening or double-consuming the retained executable source.

The required ownership sequence is:

`authenticated source + stack -> loader-owned prepared mapping -> registry
commit of the exact mapping transaction -> scheduler reserve -> TCB/ready/
vmspace publication -> scheduler publish -> per-hart activation -> kernel-root
restore -> inactive -> terminal Zombie -> retryable detach/registry completion
-> frame/table/root release -> TCB removal`.

Every boundary must use a bounded opaque `{slot,generation}` handle plus exact
`{task_id,lifecycle_generation}` validation. Activation must validate the
calling scheduler CPU/hart, perform SATP write/readback plus `sfence.vma`, and
record the active root under the architecture mutex. Reap failure must retain
the Zombie TCB and handle for retry. Fork must never alias the handle, and exec
requires a two-mapping transaction. `riscv32.process_image_builder_ready` stays
false until this complete sequence and filesystem-backed QEMU evidence exist.
