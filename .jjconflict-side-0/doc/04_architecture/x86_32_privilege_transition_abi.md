<!-- codex-design -->
# x86_32 privilege-transition ABI v1

## Decision

Filesystem execution on x86_32 uses one architecture-owned privilege capsule:

```text
scheduler-prepared child
  -> private page directory + kernel stack
  -> armed token + TSS.esp0
  -> iret CPL3
  -> int80 common frame
  -> authenticated dispatcher
     -> return-user | resume-kernel-exit | reject
  -> scheduler exit/wait/reap
  -> page-directory destruction
```

The Simple contract and `privilege_abi_v1_4.h` are mirrored numeric/layout
authorities; their parity is release-gated. ABI v1.1 freezes the single strong
cdecl symbol `simpleos_x86_32_privilege_dispatch_v1_1`; weak probing is
forbidden. The boot runtime must install its own six-entry GDT rather than
trusting Multiboot's table. TSS `esp0` is rebound to the scheduled task's
kernel-stack top immediately before arming its token; scheduling or teardown
first disarms the token.

## Security boundary

The one-shot token binds TaskId, capability generation, address-space ID,
expected user CR3, kernel CR3, saved kernel continuation, and SHA-256 nonce
digest. The dispatcher accepts only vector `0x80`, CPL3 CS/SS, the current CR3,
and the scheduler's exact current task/generation. DebugWrite (60) additionally
validates bounded user memory and nonce bytes before emitting output. Exit (0)
accepts status 37 once, atomically changes armed to exiting, restores kernel
CR3/stack, resumes the saved continuation, marks that task exited, waits for
the same child, then destroys its address space. Any mismatch rejects without
UART output, user return, reap, or cleanup.

## Ownership

- GDT/TSS install and `esp0`: x86_32 architecture capsule.
- Trap-frame construction and control transfer: one assembly owner.
- Token validation/state transition: one Simple dispatcher owner with the
  frozen C-compatible disposition result.
- Exit/reap: scheduler; page-table cleanup occurs only after collection.
- PT_LOAD/user stack: existing explicit-root x86_32 paging owner.

ABI v1.2 adds a CPU-local active-token slot. Entry rejects an occupied slot,
sets `TSS.esp0` to the prepared kernel-stack top, then release-publishes the
token. Exit/fault compare-clears that exact pointer once before scheduler state
or memory is reclaimed. The scheduler allocates four contiguous pages, stores
base/top/count on the exact TCB, and frees them only after `wait_for_collect`.

ABI v1.3 binds the admitted nonce to `expected_nonce_user_va`, exact length,
and SHA-256 digest. The loader maps that exact range user-readable and
kernel-read-only. Entry seeds ECX/EDX from the token. Syscall 60 accepts only
the identical EBX pointer and ECX length, rejects wraparound or crossing the
3 GiB user ceiling, revalidates every page under expected CR3, and compares the
complete digest before producing output.

ABI v1.4 fixes nonce placement at `0x2FFFF000`, one page below the brk base.
Preparation rejects any PT_LOAD overlap, allocates and zeroes one frame, copies
and hashes the exact bytes, maps it user-readable/non-writable, and pins the
mapping to a bounded 16-slot kernel token lease. The scheduler alone mutates
the registry. The child receives a frozen mapping; exit produces only an
encoded disposition for parent validation and deterministic commit.

ABI v1.5 reserves PDE 1023 as the sole recursive self-map: current PD at
`0xFFFFF000`, PT windows at `0xFFC00000 + pde*4096`. PDE 1022/PTE 1023 owns the
single CPU-0 kmap VA `0xFFBFF000`. Child roots must install their own PDE 1023,
never copy the kernel self-reference, and teardown must exclude both reserved
PDEs. Every install validates collision-free supervisor-only entries and every
map/unmap invalidates the affected VA before lease publication/reuse.

ABI v1.6 reserves three linker-owned pages immediately after `.text.entry` and
asserts they end below 4 MiB: kernel PD, kmap PT, and serialized child staging.
`crt0.s` explicitly zeroes the NOLOAD pool and installs PDE1023/PDE1022 before
calling Simple. PMM's existing kernel-prefix reservation owns the frames after
initialization. Runtime accessors validate the complete address ledger before
VMM adopts the boot PD.

ABI v1.7 builds supervisor-only 4 MiB PSE identity mappings through aligned
`_kernel_end`. Boot requires Multiboot memory-size validity and rejects a live
range beyond the physical ceiling or recursive-window boundary. It proves the
next instruction and current stack remain mapped, loads CR3, enables CR4.PSE,
then sets CR0.PG and CR0.WP. Only the `.paging_live` continuation may call
Simple or use recursive/kmap virtual addresses.

ABI v1.8 moves the PMM bitmap into a 128 KiB aligned NOLOAD linker section
before `_kernel_end`, so the v1.7 identity range includes it. Capacity is
exactly 1,048,576 pages (4 GiB at 4 KiB/page). The reserved-bitmap initializer
rejects memory beyond capacity, validates address arithmetic and containment in
the kernel reservation, and never silently truncates physical memory.

No live assembly symbol is authorized by this design alone.
