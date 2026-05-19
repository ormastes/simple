# Process Isolation — Address Space, Process Table, Context Switch

## User Request
> Implement process isolation for SimpleOS scheduler: address space isolation,
> process table with owned AddressSpace handles, context switching with
> address-space swap on task dispatch.

## Task Type
feature

## Refined Goal
> Extend kernel context switch to swap address spaces (CR3/SATP) on dispatch,
> add a kernel-side process table that owns AddressSpace handles with full
> lifecycle (create/lookup/reap), and wire switch_context_with_as so the
> scheduler calls address-space switch atomically with GPR context switch.

## Acceptance Criteria
- [x] AC-1: address_space_switch.spl — arch-neutral AS switch (x86_64 CR3 write, riscv64 SATP write via arch_adapt), with `as_switch_current`, `as_phys_root`, `as_id` accessors
- [x] AC-2: process_table_extended.spl — kernel process table owning AddressSpace handles, supporting alloc_pid, register_with_as, lookup, reap_as (destroys address space), list_pids
- [x] AC-3: context_switch.spl extended — `switch_context_with_as(old_ctx, new_ctx, new_as_phys_root)` swaps CR3 before restoring GPRs; existing switch_context unchanged
- [x] AC-4: process_isolation_as_spec.spl — 15+ tests covering AS create/switch/destroy, process table lifecycle, and context switch with AS
- [x] AC-5: MDSOC-only (no ECS) — kernel files; no userland patterns introduced

## Phase Checklist
- [x] 1-research — 2026-05-19
- [x] 5-implement — 2026-05-19
- [x] 7-verify — 2026-05-19 (15 tests PASS)
- [x] 8-ship — 2026-05-19

## Phase Outputs

### 5-implement
3 new files + 1 extended:
- src/os/kernel/scheduler/address_space_switch.spl — AS switch primitives
- src/os/kernel/scheduler/process_table_extended.spl — process table with AS lifecycle
- src/os/kernel/scheduler/context_switch.spl — extended with switch_context_with_as
- test/unit/os/process_isolation_as_spec.spl — 15 tests
