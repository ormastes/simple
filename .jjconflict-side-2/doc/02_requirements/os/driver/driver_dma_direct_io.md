# Driver DMA Direct I/O Requirements

Feature: FR-DRIVER-0010.

## Requirements

- REQ-001: The fs-driver layer must expose an explicit direct-I/O request path
  based on `SharedDmaBuffer`.
- REQ-002: Direct I/O must validate file offset, buffer length, and
  device-address alignment before submission.
- REQ-003: NVMe and VirtIO-BLK adapters must provide methods that submit
  SharedDmaBuffer-backed block reads and writes.
- REQ-004: Unaligned direct I/O must either return an error or report an
  explicit bounce-buffered result when bounce is enabled.
- REQ-005: Direct-I/O timeout and cleanup authority must be observable in
  Result-returning APIs and tests.
- REQ-006: A deterministic benchmark report must compare buffered-copy bytes
  with direct-DMA copy bytes for the same fixture.
