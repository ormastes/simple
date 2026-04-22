# ARM User Exec Remains — Design Note

Date: 2026-04-22

## Design

- Scheduler address-space creation now routes through `os.kernel.memory.user_address_space` instead of directly importing the x86-shaped VMM helpers.
- Segment mapping now asks the same adapter for page allocation and page mapping, preserving the existing VMM path on non-ARM64 targets.
- ARM64 fs-exec uses a direct-load arena root in early boot and stages ELF PT_LOAD bytes into that arena through the ARM runtime helper. This is intentionally a bounded acceptance bridge, not the final user-mode memory design.
- ARM64 context save/restore/switch methods call runtime ABI hooks so HAL users have a concrete path instead of Simple-level placeholders.
- ARM64 process-image construction keeps the original VFS byte array in the unchecked freestanding path and records scalar ELF header fields because aggregate `ElfImage`/segment readback is not yet reliable there. The direct-load mapper uses the scalar ELF64 program-header path to stage PT_LOAD contents, creates an ARM64 user page-table image for the PT_LOAD virtual pages, probes TTBR0_EL1 with immediate restore when the MMU is off, resolves the task context entry to the staged physical address, verifies the page-table translation for that entry, and byte-checks that the staged entry matches the file-backed ELF source.
- ARM64 uses the same high-level user-entry bridge shape as x86: arch code asks the scheduler for a handoff-ready user task and calls one runtime helper with entry, stack, status, and address-space root. The current ARM64 fs-exec closure now records the verified ELF virtual entry, installs the user TTBR0 root, enables SCTLR_EL1.M, and performs a live `eret` into the loaded proof ELF at its virtual entry. The virtual-entry preflight verifies the ELF virtual entry, initial `SP_EL0`, EL1 vector/SVC/handoff code, current EL1 stack, and UART MMIO mappings in the user root. The lower-EL AArch64 synchronous vector handles SVC64 by saving a GPR frame, dispatching to the C syscall shim, returning the result in user `x0`, advancing `ELR_EL1`, and `eret`ing back to EL0. `svc #0` remains the QEMU proof exit path.
- x86 and ARM64 share `Scheduler.get_user_handoff_task(pid_hint)` for user-entry task selection.
- ARM32 keeps the existing VMM/synthetic behavior to avoid regressing the fragile trace-based lane.

## Acceptance

- ARM64 QEMU must show FAT32 SMF bytes loaded, process image built, scheduler registration completed, and `TEST PASSED`.
- ARM64 QEMU must show one PT_LOAD record detected from the loaded SMF/ELF bytes.
- ARM64 QEMU must show ELF PT_LOAD staging through the direct-load mapper.
- ARM64 QEMU must show the ARM64 user page-table image was built for the staged PT_LOAD pages.
- ARM64 QEMU must show a controlled TTBR0_EL1 probe succeeded or was explicitly deferred because the MMU is already on.
- ARM64 QEMU must show the bootstrap user task entry was mapped to the direct-load arena.
- ARM64 QEMU must show the direct-load entry page-table translation verified.
- ARM64 QEMU must show the direct-load entry bytes verified against the loaded filesystem image.
- ARM64 QEMU must show the virtual-entry preflight passed before live virtual entry.
- ARM64 QEMU must show the user-entry handoff probe succeeded.
- ARM64 QEMU must show live EL0 virtual-entry `eret` and SVC exit handling succeeded.
- ARM64 lower-EL SVC handling must preserve user registers across handled syscalls except for the `x0` return value.
- ARM64 QEMU must not show the old `synthetic address space` line for the fs-exec path.
- ARM32 QEMU must keep the existing trace-marker acceptance passing.

## Follow-up

- Replace the broad early identity support window with a real kernel/user TTBR split, then add rollback and fault handling around live address-space activation.
- Extend the ARM64 SVC/trap runtime from the current minimal syscall-return path into full trap-frame and scheduler integration.
- Fix freestanding ARM64 aggregate `ElfImage` and `UserLoadSegment` readback so the shared segment mapper can replace the scalar entry/PT_LOAD direct-load bridge. Start with compiler regressions for struct-in-array field readback, `StructInit -> ArrayPush/IndexGet -> FieldGet`, and imported accessor field typing that must not degrade to ambiguous `ANY`.
- Replace ARM64 runtime context hook fallback with a privileged register restore path that activates the task address space and enters EL0 with `eret`.
- Stabilize ARM32 text and return ABI before tightening ARM32 acceptance beyond trace markers.
