# Driver DMA Direct I/O Design

Feature: FR-DRIVER-0010.

## Data Structures

- `DirectIoRequest`: handle id, file offset, operation, shared DMA buffer, and
  timeout budget.
- `DirectIoResult`: submitted flag, byte count, backend tag, status,
  buffered-copy bytes, direct-DMA copy bytes, and cleanup requirement.
- `DirectIoBenchmarkReport`: deterministic same-fixture copy-cost comparison.

## Semantics

- `direct_io_submit` rejects invalid handles, unknown operations, zero timeout,
  and invalid or unaligned buffers.
- If `bounce_allowed` is true, an otherwise unaligned valid buffer returns a
  `bounce-buffered` result rather than silently pretending to be zero-copy.
- Aligned reads and writes synchronize the shared DMA buffer at the request
  boundary and return a `submitted` result.
- Cleanup uses `validate_shared_dma_release` so task id, BDF, allocation id,
  size, and double-free state remain enforced.

## Driver Methods

- `NvmeDriver.read_shared_dma` and `write_shared_dma` validate the descriptor,
  sync caches, and call notification-backed sector submission with
  `buf.device_addr`.
- `VirtioBlkDriver.read_shared_dma` and `write_shared_dma` allocate 17 bytes of
  driver scratch DMA for header/status and point the data descriptor at
  `buf.device_addr`.
