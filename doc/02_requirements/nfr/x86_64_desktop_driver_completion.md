<!-- codex-research -->
# NFR: x86_64 Desktop Driver Completion

## Selected Option

NFR Option 2: Safety And Truthful Capability Reporting.

## Requirements

- NFR-X64DRV-001: Driver completion must be accepted by deterministic QEMU markers with bounded timeouts.
- NFR-X64DRV-002: Driver summaries must report DMA mode, interrupt mode, polling fallback, acceleration state, and unsupported hardware-alpha features.
- NFR-X64DRV-003: No driver may claim DMA unless it used a kernel-owned DMA descriptor.
- NFR-X64DRV-004: No hidden heap-copy fallback may be reported as zero-copy or direct DMA.
- NFR-X64DRV-005: Framebuffer or VGA/BGA display paths must report `accelerated=false`.
- NFR-X64DRV-006: Polling fallback is allowed only when the driver summary says `interrupt_mode=polling`.
- NFR-X64DRV-007: Resident process fallback, false display acceleration, and hidden copy markers must fail the complete-driver acceptance lane.

