# Simple 2D Vector Fonts — NFR Requirements

Date: 2026-07-11
Selection: NFR Option B

- NFR-001: The retained repeated corpus achieves at least 90% cache hits and zero rerasterizations on an identical second pass.
- NFR-002: Warm cached p50 is at least 25% faster than the same cold workload; both p95 values are recorded.
- NFR-003: Bitmap-only p50 regresses by no more than 5% against the retained pre-change baseline with identical checksum.
- NFR-004: Cache bounds are 512 entries and 32 MiB alpha payload; counters expose entries, bytes, hits, misses, rasterizations, and evictions.
- NFR-005: Evidence records fixture/license, size, backend, viewport, cache state, p50/p95, checksum, and RSS when available.
- NFR-006: Invalid fonts/sizes fail without crash, leak, partial activation, or loss of bitmap fallback.
- NFR-007: Fixed fixture/backend output is deterministic and paired with absolute nonblank/layout witnesses.
- NFR-008: The hot path performs no filesystem access, font reload, environment polling, subprocess, or full-font scan per glyph/draw.
- NFR-009: No runtime extern is declared outside the font I/O owner; changed entrypoints add no dependency cycle.
