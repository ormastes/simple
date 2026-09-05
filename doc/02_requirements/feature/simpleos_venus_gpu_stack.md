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
- REQ-SVG-010: Pure-Simple transport, Venus, Vulkan API, and DrawIR seams shall
  emit versioned `NormalizedTrace`/`TraceEvent` semantic records through an
  injected test sink, without raw pointers, unstable handles, or wall-clock
  equality fields.
- REQ-SVG-011: `TraceComparator` shall compare explicit semantic projections,
  map implementation-local object handles, report the first divergence plus
  context, and reject schema/profile mismatch rather than silently normalize it.
- REQ-SVG-012: Mesa/Vulkan `ReferenceOracleAdapter` shall be test-only,
  dynamically loaded, unavailable when its exact library/symbol set is absent,
  and unable to alter provider admission, rendering, or fallback.
- REQ-SVG-013: All oracle externs shall have one canonical
  `nogc_sync_mut` owner and compiled ABI, error propagation, acquisition,
  release, double-release rejection, and missing-library tests.
- REQ-SVG-014: GPU expectation profiles shall bind the canonical UI environment
  profile, architecture/transport, required VirtIO/Venus/Vulkan features,
  allowed oracle identity, readback provenance, and no-fallback policy.
- REQ-SVG-015: GPU and Chrome/Web differential tests may share the generic
  trace schema and comparator only; their production layers, domain adapters,
  object vocabularies, and acceptance policies shall remain independent.
- REQ-SVG-016: VUDA shall not be migrated or vendored because its CUDA-like
  Vulkan owner bypasses the provider/VirtIO/Venus boundaries. It may be retained
  only as a separately labelled external compute-test reference.
