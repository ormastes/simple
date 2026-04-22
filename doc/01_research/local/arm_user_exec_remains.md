# ARM User Exec Remains — Local Research

Date: 2026-04-22

## Current Verified State

- `arm64-virtio-fat32-smf` loads `/sys/apps/hello_world.smf` from the FAT32 disk in QEMU, builds a process image, registers a scheduler task, and reports `TEST PASSED`.
- ARM64 no longer reports the legacy VMM sentinel path (`legacy AS=1` / `synthetic address space`) in the fs-exec lane. It now uses a direct-load arena root and stages ELF PT_LOAD bytes into RAM for this early boot acceptance path.
- ARM64 context switch facade now calls concrete `rt_arm64_context_*` runtime hooks instead of stopping at Simple-level `pass_todo` placeholders.
- ARM64 now verifies the loaded SMF/ELF bytes contain one PT_LOAD record, records that scalar count on `UserProcessImage`, stages PT_LOAD contents through the scalar ARM64 direct-load path, builds a concrete ARM64 user page-table image for those PT_LOAD virtual addresses, probes TTBR0_EL1 with that root when the MMU is off, resolves the task context entry to the staged direct-load address, verifies the user page table translates the ELF entry to that address, and verifies the bytes at that direct entry match the file-backed ELF source bytes.
- ARM64 now has an x86-shaped user-entry bridge (`dispatch_enter_user_blocking_probe`) that validates the scheduler handoff frame through one runtime helper. The bridge accepts the current direct physical entry only when it matches the page-table translation of the ELF virtual entry.
- ARM64 now performs live EL0 entry for the filesystem-loaded proof ELF: the runtime helper programs `SP_EL0`, `ELR_EL1`, and `SPSR_EL1`, executes `eret`, catches the proof ELF's `svc #0` in the lower-EL AArch64 synchronous vector, prints the success markers, and exits QEMU. The lower-EL SVC path now saves/restores a GPR frame, dispatches non-exit SVC IDs through `userlib__syscall_raw__syscall`, returns the result in user `x0`, advances `ELR_EL1`, and `eret`s back to EL0.
- ARM64 now runs a non-live virtual-entry preflight before direct live entry. The preflight maps/proves the EL1 support window in the user root, verifies ELF virtual entry translation, verifies the initial `SP_EL0` page, verifies vectors/lower-EL SVC handler/syscall handler/live handoff code, and verifies UART MMIO translation. User executable PTEs now set PXN while leaving UXN clear, so EL0 can execute text without allowing EL1 execution from user pages.
- The x86 user-entry lookup path now uses the same scheduler-owned handoff query as ARM64 instead of duplicating user-task scans in the arch bridge.
- ARM64 process-image construction now reads the ELF entry through a scalar runtime helper in the freestanding path. The aggregate `ElfImage.entry` read produced `0x75000000` for a disk stub whose ELF header entry is `0x400000`, so the scalar bridge is required until aggregate return/readback is stable.
- `arm32-virtio-fat32-smf` remains green on the existing trace-marker path.
- ARM32 text output and aggregate/return behavior remain unreliable; trace IDs are still the stable acceptance signal.

## Remaining Blockers

- ARM64 now builds a user page-table image for the loaded PT_LOAD pages and performs a controlled TTBR0_EL1 write/read/restore probe when SCTLR_EL1.M is off. It also passes the non-live virtual-entry preflight for ELF entry, `SP_EL0`, vectors, lower-EL handler code, current EL1 stack, UART MMIO, and live handoff code. The remaining MMU work is live TTBR0 activation while translations are enabled, with kernel/user split, TCR/MAIR/SCTLR programming, rollback, and fault handling.
- ARM64 freestanding aggregate readback remains unreliable for both segment arrays and some scalar fields returned through aggregate `ElfImage`, so the verified loading step uses scalar ELF header helpers for entry and PT_LOAD staging rather than the shared aggregate segment mapper. The next compiler investigation targets concrete struct identity loss to `ANY`, raw struct pointer tagging through arrays/results, and duplicated 8-byte field-slot layout assumptions.
- ARM64 context hooks are C ABI runtime helpers for the current QEMU closure; the proof ELF has a live `eret` path, but general task context restore still needs to move from proof-specific helper to scheduler/runtime integration.
- ARM64 lower-EL SVC handling now has a minimal syscall-return ABI for supported IDs. It is still not a complete trap subsystem: nested faults, signal/kill semantics, scheduler blocking, and full saved task trap frames remain follow-up work.
- ARM32 still needs ABI/output stabilization before replacing numeric traces with readable user-task markers.

## Implementation Decision

The implemented slice keeps the QEMU filesystem-load acceptance green, removes the old synthetic VMM sentinel from ARM64, verifies one PT_LOAD record at the scalar image level, stages PT_LOAD contents into the direct-load RAM arena, builds and verifies a user page-table translation for the staged entry, probes TTBR0_EL1 with restore, resolves and byte-checks the staged entry for the task context, validates an x86-shaped first-user handoff frame, proves the virtual-entry support mappings non-live, and completes a live EL0 `eret` plus lower-EL SVC dispatch/return path. Live ARM TTBR0 activation under MMU-on conditions, aggregate segment-array repair, full trap-frame/scheduler integration, and scheduler-integrated task context restore remain explicit follow-up work.
