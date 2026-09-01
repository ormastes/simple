# RV32 Sv32 user-entry and trap-return owner is missing

The nonce-bound RV32 ELF and exact mounted-byte admission are ready, but the
repository cannot safely execute that image in U-mode yet.

The Sv32 paging module now exposes `riscv32_vmm_map_page_in` and
`riscv32_vmm_destroy_address_space`, and the architecture-neutral loader routes
RV32 construction and teardown through those owners. This closes the prior
cross-architecture bug where RV32 used the x86 PML4 adapter. A task-owned
SATP/ASID execution token is still absent, so the mapped image must not yet be
entered.

The interrupt module only manages PLIC configuration and declares exception
constants. It does not install an S-mode trap vector that saves U-mode
registers, authenticates the current task, decodes `ecall` 60/0, advances
`sepc`, or resumes a saved supervisor frame. The context module declares
`rt_rv32_context_save`, `rt_rv32_context_restore`, and
`rt_rv32_context_switch`, but no implementation exists in runtime, kernel, or
the RV32 examples. Its fresh context also sets `SSTATUS_SPP`, selecting
S-mode—not U-mode—on `sret`.

Consequently the live admission remains fail-closed with `-95` and
`rv32-sv32-live-entry-not-installed`. A simulator PASS is not live execution.

## Minimum unblock sequence

1. **Completed:** add `riscv32_vmm_map_page_in(root, virt, phys, flags)` and a
   matching Sv32 user-root destructor. Zero/sentinel/misaligned roots are
   rejected; stale-root authentication remains part of the execution token.
2. Add a task-owned RV32 trap frame and supervisor stack plus an assembly trap
   vector. The first-entry frame must clear `SSTATUS_SPP` before `sret`.
3. Save the exact S-mode continuation before switching SATP. Bind it to
   `(TaskId, address_space_id, expected_satp)` and consume it once.
4. Authenticate the token/current SATP on every U-mode ecall. Syscall 60 may
   append only the expected bounded nonce output; syscall 0 must accept 37,
   mark the same child exited, restore kernel SATP, and resume S-mode.
5. Reap the exact child through `Scheduler.wait_for_collect`, including Sv32
   page-table and user-frame cleanup.
6. Sabotage wrong root, stale generation, S-mode ecall, replayed exit, invalid
   user address, wrong stdout, wrong exit code, and missing reap before QEMU.

No RV32 live owner was added because the required U-mode trap, saved supervisor
continuation, and authenticated execution-token hooks remain absent. Adding
those is kernel context-ABI work; treating the current PLIC handler or declared
but unimplemented context externs as an owner would be fail-open.

## ABI freeze update

The source-only v1 ABI is now frozen in
`src/os/kernel/arch/riscv32/privilege_transition_abi.spl`, with architecture and
detail design in `doc/04_architecture/rv32_privilege_transition_abi.md` and
`doc/05_design/rv32_privilege_transition_abi.md`. It specifies the 416-byte
RV32IMAFD frame, FP policy, `stvec`/`sscratch` boundary, authenticated
SATP/ASID token, saved S continuation, dispatcher result, and scheduler
lifecycle. This does not unblock live admission: assembly, dispatcher,
scheduler wiring, target ISA admission, and executable evidence remain absent.

The profile ambiguity is resolved: deployable v1 is RV32IMAC/Zicsr with ILP32,
a 160-byte frame, no FP fields, and mandatory FS=Off. RV32IMAFD/ILP32D is a
distinct future v2 capability profile with the 416-byte FP frame and cannot be
selected until F/D admission and a matching privileged object exist. Live
entry remains blocked only on the still-missing assembly, dispatcher/token
registry, scheduler integration, and executable evidence.

The trap-to-token lookup rule is now resolved in ABI v1.1. `sscratch` points to
a privileged per-hart 16-byte anchor containing stack top, token pointer, hart
ID, and nesting. The token and keyed authentication tag bind the hart;
publication/lookup use release/acquire ordering, occupied anchors reject
replacement, nested S traps see zero `sscratch`, and accepted exit clears the
anchor only after consuming the continuation. Privileged assembly remains the
next unimplemented step.

Token authentication is frozen in ABI v1.2: SipHash-2-4, repository KAT, fixed
ILP32 C boundary, 128-bit per-boot registry-owned key, exact 80-byte
little-endian domain-separated serialization, constant-time 64-bit comparison,
fail-closed unavailable-key behavior, wipe on reset/shutdown, and rejection of
Entered-token hart migration. Registry/dispatcher implementation remains
absent.

The next implementation blocker is key provisioning. The RV32 entropy module
explicitly has no true-random QEMU/OpenSBI source and mixes timer/DTB/hart
metadata into one u64. That predictable mixer cannot seed the v1.2 128-bit MAC
key. Add a fail-closed RV32 production entropy provider for exactly 16 bytes or
a measured kernel-only boot-key injection interface; never fall back to
`entropy_seed_u64()`. The registry must remain unavailable until this exists.

Virtio-rng entropy discovery is now source-wired, exposing capability only
after device-ID/version/feature/queue admission. The next blocker is the absent
fixed C SipHash symbol and ambiguous runtime ownership: the RV32 platform admits
two separate `baremetal_stubs.c` surfaces, one independent example runtime and
one kernel shim that includes the RV64 freestanding runtime. Extract a single
shared strong SipHash owner (with the frozen KAT) or make those sources provably
exclusive before token registry and trap assembly can authenticate entry.

The shared strong owner and KAT now exist. The next blocker is packed storage:
RV32 freestanding `[u8]` arrays use tagged `spl_i64` elements and
`rt_array_data_ptr_u8` exposes that representation, while the frozen SipHash C
ABI expects contiguous raw 16/80-byte buffers. Add kernel-only fixed packed
storage with stable raw pointers and volatile wipe, or version the ABI to pass
scalar words and serialize inside C. Do not use long-lived device-visible DMA
storage for the secret and do not publish an anchor before this is resolved.
