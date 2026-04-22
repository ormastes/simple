# Driver DMA Direct I/O NFR

Feature: FR-DRIVER-0010.

## Targets

- NFR-001: Buffered read/write APIs remain the default and require no caller
  DMA descriptor.
- NFR-002: Direct I/O is opt-in through capability probing or direct request
  construction.
- NFR-003: No hidden heap-copy fallback occurs unless the returned status says
  `bounce-buffered`.
- NFR-004: Cache synchronization remains explicit at the DMA boundary.
- NFR-005: Focused SSpec coverage must exercise aligned I/O, unaligned
  rejection/bounce, timeout, cleanup, and benchmark reporting.
