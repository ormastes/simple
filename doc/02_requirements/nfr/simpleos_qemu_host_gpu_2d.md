# SimpleOS QEMU Host-GPU 2D NFR Requirements

**Selected option:** NFR B — balanced desktop target.

- NFR-001: The canonical 1280×720 ARGB rendering fixture shall have zero pixel mismatches against the CPU oracle.
- NFR-002: The canonical processing fixture shall have exact element-for-element parity with the CPU oracle.
- NFR-003: Warm batched render plus same-frame readback p95 shall be at most 16.7 ms on supported native-ISA hardware-accelerated rows.
- NFR-004: The processing fixture shall be at least 1.5× faster than the CPU oracle to become preferred; a correct but slower device backend remains `available-not-preferred`.
- NFR-005: Incremental QEMU plus host-service max RSS shall be at most 256 MiB for the canonical fixture.
- NFR-006: Capability negotiation and fallback selection shall finish within 500 ms after guest device initialization.
- NFR-007: Queue depth, payload size, command count, dimensions, and outstanding batches shall be bounded; overload shall fail or backpressure without unbounded allocation.
- NFR-008: Cross-ISA TCG rows shall verify correctness and honest provenance but shall not be required to meet native-ISA latency/speedup targets. Applicability shall come from the retained executed QEMU `-accel` argument plus matching host ISA, never ISA equality alone; same-ISA TCG remains correctness-only.
- NFR-009: Evidence shall record host OS, guest ISA, QEMU version/device arguments, selected QEMU accelerator, protocol version, selected backend, native device identity, frame/run identity, timings, max RSS, and checksums.
- NFR-010: The exact Simple 2D gate shall compare the canonical serialized
  framebuffer byte-for-byte with `mismatch_count=0`; tolerance, blur, scaling,
  color conversion, screenshots, and CPU mirrors are forbidden.
- NFR-011: The current host Metal, host Vulkan, CPU SIMD, software, event-flow,
  Draw IR, vector-font, and high-DPI contracts shall pass unchanged before any
  QEMU or board adapter can be promoted.
- NFR-012: Supported native-board rows shall use the existing 20-sample warm
  p95 and exact-parity rules. A correct row that misses the selected latency or
  speedup target remains `available-not-preferred`.
- NFR-013: Capability discovery shall be cached for one boot/session and
  invalidated on device reset, driver/firmware identity change, protocol
  version change, or backend loss; no frame may rescan the full device tree or
  spawn a discovery process.
