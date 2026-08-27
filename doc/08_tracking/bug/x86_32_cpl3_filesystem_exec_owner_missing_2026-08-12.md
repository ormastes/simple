# x86_32 CPL3 filesystem execution owner is missing

The x86_32 initrd lane must not claim arbitrary filesystem-program execution.
`rt_x86_32_trigger_int80` executes `int $0x80` at the kernel's current
privilege. The IDT entry is DPL3, but the repository has no installed x86_32
GDT/TSS owner, user stack, `iret`-to-CPL3 handoff, or syscall-0 return/reap
frame. Its positive values 2001/2002 are synthetic dispatcher receipts, not
process identities. Private PT_LOAD mapping and teardown now exist through
`x86_32_vmm_map_page_in` and `x86_32_vmm_destroy_address_space`; the generic
loader adapter no longer routes x86_32 through the x86_64 PML4 owner.

A real target payload now exists at
`examples/09_embedded/simple_os/arch/x86_32/user_fsexec_src/mounted_elf32.S`.
It executes syscall 60 on a caller-supplied bounded nonce and exits 37 through
`int $0x80`; `scripts/check/check-simpleos-x86-32-user-elf.shs` validates the
ELF32/i386 executable PT_LOAD and instruction contract without booting it.

Live unblock contract: add an x86_32 architecture owner that maps every ELF32
PT_LOAD from the selected FAT dirent, creates GDT/TSS CPL3 state and a user
stack, enters the ELF entry with `iret`, validates syscall-60 user memory, and
returns syscall-0 status to a scheduler-owned child that is reaped by its
caller. Selection must use the resolved task/process object, never a fixed PID.
Only then may the lane emit target stdout and `[fs-program] END ... rc=37`.

The present `user_entry.spl` extern is not that owner: the assembly file it
names is absent, `rt_x86_32_context_switch` in the example runtime is a no-op,
and the installed int80 probe saves no authenticated supervisor continuation.
Live admission must remain fail-closed until one token binds the exact
`(TaskId, generation, CR3, nonce)` and both syscall 60 and exit 37 validate it
before output, resume, scheduler exit/reap, and address-space destruction.

## Context-ABI stop evidence

A source-only implementation attempt stopped before adding assembly because
the current contracts are contradictory rather than merely incomplete:

1. `boot/crt0.s` explicitly inherits the Multiboot loader's flat GDT. It does
   not install the selector layout assumed by `cpu.spl` (`0x18`, `0x20`, and
   `0x28`), and there is no x86_32 GDT/TSS object or task-owned `esp0` setter.
   Loading `ltr 0x28` against the inherited table is therefore unauthenticated
   and can raise `#TS`.
2. `x86_32_int80_probe_handler` uses `pusha` and fixed offsets for an interrupt
   raised at CPL0. A CPL3-to-CPL0 gate additionally pushes user `SS:ESP`; its
   frame cannot safely reuse those offsets. It also returns only with `iret`
   and owns no one-shot saved kernel continuation.
3. `rt_x86_32_context_switch` records fabricated zero registers and never
   restores the destination context. It cannot be used as the supervisor
   savepoint for exit 37.
4. The example C runtime declares several Simple dispatcher symbols as raw
   `int32_t(uint32_t, ...)`, while other runtime entrypoints use the
   `RuntimeValue` ABI. The canonical calling convention for a new trap bridge
   must be frozen before assembly passes a frame or token to Simple.
5. `capability_generation` exists in task security state, but no architecture
   handoff contract currently snapshots it together with TaskId, CR3, nonce,
   kernel stack, and continuation. Guessing that composition would make stale
   or replayed syscall authentication fail open.

Minimum prerequisite is a frozen packed i386 trap-frame/token ABI shared by C,
assembly, and Simple, followed by an owned GDT/TSS installer and per-task
kernel-stack lifecycle. Only after that can sabotage tests meaningfully cover
wrong CPL, altered frame offsets, stale generation/CR3, nonce substitution,
replayed exit, and reap-before-destroy ordering.

## Physical-access recursive bootstrap blocker

ABI v1.4 freezes a scheduler-owned nonce preparation lease, but its physical
copy owner cannot yet be implemented honestly. The x86_32 paging walker reads
and writes page-directory/page-table entries by dereferencing their physical
addresses directly. Only the first 4 MiB is identity mapped. If PMM supplies a
table above that range, `_ensure_table_entry` faults before a temporary kmap
window can be installed; using that same walker to create the window is
recursive and does not solve the bootstrap.

The paging owner must first reserve a recursive PDE or guarantee all paging
structure frames come from a permanently mapped low-memory pool. That choice
also needs collision and lifetime rules. Until then, arbitrary frames above
4 MiB cannot be copied, zeroed, read back, or used to verify a read-only nonce
PTE, so nonce preparation and privilege-entry assembly remain disabled.

The v1.6 linker pool resolves the first-PD physical-access bootstrap, but the
recursive mapping is not live yet: no x86_32 boot path sets `CR0.PG`, and the
current PD identity-maps only the first 4 MiB. The production linker places a
4 MiB heap after kernel code/data starting at 1 MiB, so enabling paging with
that PD would unmap a live portion of the kernel. Boot must construct bounded
identity mappings through aligned `_kernel_end`, validate that range against
physical memory, load CR3, set CR0.PG, and only then allow recursive-window or
kmap access.

ABI v1.7 implements that boot identity/PSE/PG/WP sequence and statically links
it against the production x86_32 linker script. Remaining live work starts at
the recursive-window physical-access owner and must not regress to direct
physical dereferences for PMM frames above the mapped kernel prefix.

The v1.8 recursive kmap and explicit-root address-space owner remove those raw
dereferences. Stable token storage is now also implemented: the architecture-
common fixed packed owner allocates a 96-byte aligned kernel record under a
generation lease; the scheduler registry serializes each frozen token one byte
at a time, publishes only its stable address, rejects stale leases, and
volatile-wipes the record before reuse. Its focused behavioral and x86_32
publication gates pass.

The remaining live blocker returns to the frozen privilege boundary itself:
the repository still lacks the installed x86_32 GDT/TSS, task-owned `esp0`,
the exact CPL3 int80 frame assembly consumer, and the one-shot parent
continuation/compare-clear implementation. Those owners must consume the
stable packed address and v1.8 explicit-root mapper; they must not reintroduce
raw Simple-array pointers or the old same-CPL probe frame. Live QEMU evidence
remains absent.

## Fresh truthful live boundary (2026-08-12)

The synthetic success path has now been removed from
`initrd_fs_exec_probe_entry.spl`. A fresh admitted-LLVM rebuild and bounded TCG
boot traversed the FAT32 root to `/SYS/APPS`, emitted ten actual short-name
dirents, read the exact per-run nonce from `/QEMUNONC.TXT`, and admitted the
staged root `/FSEXEC.ELF` as ET_EXEC/ELF32/EM_386. It then stopped with
`FS_PROGRAM_BLOCKED reason=x86_32-cpl3-lifecycle-owner-absent` and debug-exit
failure, without target stdout, exit/reap, or `TEST PASSED`.

Retained evidence:
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_32-live-closure-20260812/cycle1/x86_32/`.
Compiler SHA-256 is
`a3b9354cd6a8708625a48f81dc2ee929debd9169a6caaff5bd8926f6a3f8a478`.
This closes the boot/mount/list/nonce/ELF-admission ambiguity but deliberately
does not close the missing authenticated CPL3 entry/trap/continuation/reap
owner.
