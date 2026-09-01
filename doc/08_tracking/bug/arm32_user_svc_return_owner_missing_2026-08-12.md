# ARM32 user SVC-return owner is missing

The nonce-bound ARM32 ELF and exact mounted-byte admission are ready, but the
current architecture layer cannot execute them honestly in PL0/User mode.

ARM32 has partial scaffolding:

- `Arm32ContextSwitch.create_user` constructs a context with
  `CPSR_MODE_USR`;
- `Arm32Paging.create_address_space` allocates a private L1 table and copies
  upper-half kernel mappings; and
- scheduler creation/reap can own a child and its address-space handle.

Those declarations are not a live execution owner. `Arm32Paging.map_page` and
its `_map_page_internal` helper always mutate `g_root_table_phys`; there is no
map-into-explicit-L1 operation or private-root destructor. The QEMU ARM32
`rt_arm32_context_restore` implementation is a no-op, while context save writes
synthetic zero registers and an SVC-mode CPSR. The interrupt module owns only
GIC routing; no exception-vector table decodes SVC, saves user registers,
authenticates the active child/TTBR0, or returns through SPSR. No saved kernel
continuation exists for syscall 0.

Therefore live admission remains `-95` with
`arm32-user-cpsr-svc-return-not-installed`. Loading, simulating, or registering
a scheduler PID is not target execution.

## Minimum unblock sequence

1. Add `arm32_map_page_in(root, virt, phys, flags)` and an L1/L2 teardown
   walker. Reject zero, kernel root, misalignment, stale generation, and W+X.
2. Add real ARM assembly context entry/restore. Install the User-mode CPSR,
   banked user SP/LR, entry PC, expected TTBR0, and a private SVC stack.
3. Add an exception-vector table with an SVC entry that saves the complete user
   frame and binds `(TaskId, address_space_id, expected_ttbr0)` to one saved
   kernel continuation.
4. Authenticate current mode and TTBR0 before syscall 60/0. Capture only the
   bounded expected nonce output; consume exit 37 once and restore kernel
   TTBR0/SPSR/stack.
5. Mark and reap the exact scheduler child, releasing mapped frames and page
   tables only after supervisor control is restored.
6. Sabotage wrong TTBR0, stale generation, privileged-origin SVC, invalid user
   address, wrong output/status, replayed exit, and missing reap before QEMU.

No live ARM32 owner was added because these MMU and exception-return hooks are
absent or stubbed.

## Frozen resume contract

The missing ABI is now frozen in
`doc/04_architecture/os/simpleos/kernel/arm32_privilege_transition_abi.md`,
`doc/05_design/arm32_privilege_transition_abi.md`, and the paired Simple/C
layout contracts. This does not resolve the bug: no vector assembly, explicit-
root mapper, authenticated dispatcher, or scheduler handoff has been installed.
The v1.1 amendment freezes SipHash-2-4 authentication, exact covered bytes,
scheduler boot-key/per-CPU registry ownership, lifecycle registry ports, and
deterministic guarded-SVC-stack frame placement.
The v1.2 amendment freezes the closed map flags and short-descriptor truth
table, page-only L2 ownership/teardown, vector section/symbol/linker retention,
four-slot MPIDR identity, and fail-closed entropy initialization/wipe behavior.
The v1.3 amendment and C owner add the bounded identity-mapped table arena and
ledger plus an allocation-free fixed-buffer SipHash-2-4 port with canonical
KAT. Scheduler remains the sole state owner; the active token is a kernel-only
lease and child nonce data is frozen read-only.
The v1.4 C contract adds a bounded scalar SVC disposition and authenticated,
replay-resistant parent commit for stdout-byte and exit-37 transitions.
The v1.5 owner adds a separate zeroing user-frame arena, bounded ELF32 staging,
and a leased section-to-L2 kernel guard split with exact restoration. It also
adds a nonprinting bounded nonce reader. Canonical fs-exec admission remains
blocked on a fixed ABI that supplies and wipes 16 bytes of cryptographic boot
entropy; the existing timer-mixing Simple helper is not that owner.
The v1.6 C owner resolves that entropy gap with bounded device-ID-4
virtio-mmio discovery, exact short-fill accumulation to 16 bytes, explicit
provenance, all-zero rejection, and unconditional boot-key wipe. The canonical
ARM32 QEMU descriptor now supplies the RNG backend and device.
