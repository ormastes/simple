# ARM User Exec Remains — Design Note

Date: 2026-04-22

## Design

- Scheduler address-space creation now routes through `os.kernel.memory.user_address_space` instead of directly importing the x86-shaped VMM helpers.
- Segment mapping now asks the same adapter for page allocation and page mapping, preserving the existing VMM path on non-ARM64 targets.
- ARM64 fs-exec uses a direct-load arena root in early boot and stages ELF PT_LOAD bytes into that arena through the ARM runtime helper. This is intentionally a bounded acceptance bridge, not the final user-mode memory design.
- ARM64 context save/restore/switch methods call runtime ABI hooks so HAL users have a concrete path instead of Simple-level placeholders.
- ARM64 process-image construction keeps the original VFS byte array in the unchecked freestanding path and records scalar ELF header fields because aggregate `ElfImage`/segment readback is not yet reliable there. The direct-load mapper uses the scalar ELF64 program-header path to stage PT_LOAD contents, creates an ARM64 user page-table image for the PT_LOAD virtual pages, probes TTBR0_EL1 with immediate restore when the MMU is off, resolves the task context entry to the staged physical address, verifies the page-table translation for that entry, and byte-checks that the staged entry matches the file-backed ELF source.
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
- ARM64 QEMU must not show the old `synthetic address space` line for the fs-exec path.
- ARM32 QEMU must keep the existing trace-marker acceptance passing.

## Follow-up

- Activate the verified ARM64 user page table while SCTLR_EL1.M is enabled after kernel mappings and rollback/fault behavior are proven, then replace the direct physical task entry with normal ELF virtual entry once exception return is ready.
- Fix freestanding ARM64 aggregate `ElfImage` and `UserLoadSegment` readback so the shared segment mapper can replace the scalar entry/PT_LOAD direct-load bridge.
- Replace ARM64 runtime context hook fallback with a privileged register restore path that activates the task address space and enters EL0 with `eret`.
- Stabilize ARM32 text and return ABI before tightening ARM32 acceptance beyond trace markers.
