# ARM User Exec Remains — Design Note

Date: 2026-04-22

## Design

- Scheduler address-space creation now routes through `os.kernel.memory.user_address_space` instead of directly importing the x86-shaped VMM helpers.
- Segment mapping now asks the same adapter for page allocation and page mapping, preserving the existing VMM path on non-ARM64 targets.
- ARM64 fs-exec uses a direct-load arena root in early boot and stages raw SMF bytes into that arena through the ARM runtime helper. This is intentionally a bounded acceptance bridge, not the final user-mode memory design.
- ARM64 context save/restore/switch methods call runtime ABI hooks so HAL users have a concrete path instead of Simple-level placeholders.
- ARM32 keeps the existing VMM/synthetic behavior to avoid regressing the fragile trace-based lane.

## Acceptance

- ARM64 QEMU must show FAT32 SMF bytes loaded, process image built, scheduler registration completed, and `TEST PASSED`.
- ARM64 QEMU must show raw SMF staging with byte and page counts.
- ARM64 QEMU must not show the old `synthetic address space` line for the fs-exec path.
- ARM32 QEMU must keep the existing trace-marker acceptance passing.

## Follow-up

- Replace ARM64 direct-load arena with real TTBR0 page-table mapping after the ARM64 paging path can be used in the fs-exec closure without hanging QEMU.
- Fix freestanding ARM64 SMF process-image segment extraction so PT_LOAD segment mapping can replace raw-SMF staging.
- Replace ARM64 runtime context hook fallback with a privileged register restore path that activates the task address space and enters EL0 with `eret`.
- Stabilize ARM32 text and return ABI before tightening ARM32 acceptance beyond trace markers.
