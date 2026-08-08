# SimpleOS Venus GPU stack NFRs

- NFR-SVG-001: PCI capability traversal visits at most 48 records; capset
  traversal admits at most 64 tuples.
- NFR-SVG-002: Discovery allocates no framebuffer and no unbounded buffer.
  A capset payload must fit the existing 4096-byte response buffer after its
  24-byte header.
- NFR-SVG-003: Discovery runs once per device initialization and is cached in
  the owning driver; no frame or DrawIR command rescans PCI/config space.
- NFR-SVG-004: Device-config reads retry at most three times when the config
  generation changes. Capability/capset discovery has a 250 ms target and the
  complete negotiation stays inside the existing 500 ms admission budget.
- NFR-SVG-005: Every receipt carries evidence class, device identity fields,
  source architecture, stable reason, and explicit false execution/readback
  fields until live proof exists.
- NFR-SVG-006: New source files remain below 800 lines and expose only the
  interface needed by the next layer.
- NFR-SVG-007: Focused branch evidence covers valid, short, overflow, loop,
  duplicate, stale-generation, absent-Venus, oversized-payload, fallback, and
  device-readback rejection paths. No 80% claim is allowed without measured
  coverage or an accepted branch ledger.
