# ARM User Exec Remains — Local Research

Date: 2026-04-22

## Current Verified State

- `arm64-virtio-fat32-smf` loads `/sys/apps/hello_world.smf` from the FAT32 disk in QEMU, builds a process image, registers a scheduler task, and reports `TEST PASSED`.
- ARM64 no longer reports the legacy VMM sentinel path (`legacy AS=1` / `synthetic address space`) in the fs-exec lane. It now uses a direct-load arena root and stages the raw SMF bytes into RAM for this early boot acceptance path.
- ARM64 context switch facade now calls concrete `rt_arm64_context_*` runtime hooks instead of stopping at Simple-level `pass_todo` placeholders.
- `arm32-virtio-fat32-smf` remains green on the existing trace-marker path.
- ARM32 text output and aggregate/return behavior remain unreliable; trace IDs are still the stable acceptance signal.

## Remaining Blockers

- ARM64 direct-load arena is not a real TTBR0 user page-table mapping. The ARM64 paging module has table creation primitives, but using them inside the fs-exec closure hung QEMU before completion.
- ARM64 SMF process-image building currently reports zero PT_LOAD segments in this acceptance closure, so the verified loading step is raw-SMF staging rather than ELF segment mapping.
- ARM64 context hooks are C ABI runtime helpers for the current QEMU closure; live EL0 entry for a filesystem-loaded task still needs privileged register restore and `eret` handoff.
- ARM32 still needs ABI/output stabilization before replacing numeric traces with readable user-task markers.

## Implementation Decision

The implemented slice keeps the QEMU filesystem-load acceptance green, removes the old synthetic VMM sentinel from ARM64, verifies that the loaded SMF bytes are copied into a direct-load RAM arena, and makes the ARM64 context facade link through runtime hooks. Real ARM page-table activation, PT_LOAD segment extraction in the freestanding closure, and first-user-task EL0 handoff remain explicit follow-up work.
