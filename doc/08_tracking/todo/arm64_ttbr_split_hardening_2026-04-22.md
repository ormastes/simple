# ARM64 TTBR Split Hardening

Date: 2026-04-22
Priority: P1
Area: SimpleOS ARM64 process isolation

## Current State

ARM64 can launch `/sys/apps/hello_world.smf` from the FAT32 filesystem, stage
the embedded ELF PT_LOAD pages, install the user TTBR0 root, enable the MMU,
and enter EL0 at the ELF virtual entry. The QEMU acceptance lane reports
`[arm64-user] live virtual eret enter`, `svc exit ok`, and `TEST PASSED`.

The current acceptance bridge maps a compact EL1 support window into the user
root from linker `_start` through `_sbss`, plus the active EL1 stack page and
UART MMIO. This is sufficient for the proof SVC path, but it is not the final
kernel/user isolation model.

## Requirement

Replace the compact identity support window with a proper ARM64 kernel/user
translation split.

Acceptance requirements:

- Kernel text/data, exception vectors, EL1 stacks, UART/debug MMIO, and trap
  handlers remain reachable after switching to a process address space.
- User executable pages keep EL0 execute permission while preventing EL1 from
  executing user text.
- User TTBR activation has rollback/fault diagnostics for failed preflight,
  bad root, bad entry, bad stack, and lower-EL synchronous faults.
- The filesystem launch lane still enters the loaded SMF ELF at its virtual
  entry and reports `TEST PASSED`.
- `arm32-virtio-fat32-smf` remains unchanged and green.

## Suggested Implementation Path

1. Introduce a real kernel mapping half for ARM64 instead of identity-mapping
   EL1 support pages into every user root.
2. Configure TCR/TTBR state consistently for kernel and user translations.
3. Move the live handoff from proof-specific runtime helpers toward the common
   scheduler/context-switch path.
4. Add explicit lower-EL fault reporting and rollback diagnostics.
5. Remove the compact identity support window after the split is verified.

## Verification

- `LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 src/compiler_rust/target/debug/simple os test --scenario=arm64-virtio-fat32-smf`
- `LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 src/compiler_rust/target/debug/simple os test --scenario=arm32-virtio-fat32-smf`
