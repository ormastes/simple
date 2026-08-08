# SimpleOS Venus GPU stack requirements

Selection basis: the user explicitly selected the architecture-aligned first
slice on 2026-08-08; no alternative renderer or transport was selected.

- REQ-SVG-001: One public GPU capability/provider contract shall feed the
  existing Engine2D/DrawIR owner; no parallel renderer is permitted.
- REQ-SVG-002: The existing virtio-gpu driver shall discover PCI capabilities
  with a fixed visit bound, loop detection, reserved-BAR rejection, 64-bit
  overflow checks, and minimum-length validation.
- REQ-SVG-003: DEVICE_CFG shall be mapped separately from common config and
  shall expose a generation-stable, bounded `num_capsets` value.
- REQ-SVG-004: Shared-memory capability parsing shall retain only validated
  tuples and shall identify host-visible shmid 1 without assuming order.
- REQ-SVG-005: Capset enumeration shall retain every discovered
  `(id,max_version,max_size)` tuple up to a fixed bound and return typed
  complete/partial/rejected status.
- REQ-SVG-006: The Venus discovery receipt shall be explicitly discovery-only;
  it shall never set execution, fence, readback, or compositor availability.
- REQ-SVG-007: Every malformed, oversized, stale-generation, missing-feature,
  and missing-region path shall fail closed with a stable reason.
- REQ-SVG-008: x86_64 PCI, AArch64 PCI/MMIO, and RISC-V PCI/MMIO adapters may
  supply transport facts, but shall not define architecture-specific Venus or
  rendering APIs.
- REQ-SVG-009: Later queue work shall preserve the order context -> blob/map ->
  ring -> command -> fence -> readback and shall remain unavailable until each
  preceding receipt is valid.
