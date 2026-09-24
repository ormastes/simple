# NFR: Browser renderer GPU surface owner

**Status:** selected; implementation and hardware evidence pending
**Selection:** O1 compositor-owned surfaces + B/N2 runtime session

- **NFR-SURFACE-001 — residency:** Steady display performs no framebuffer
  download/readback. Capture is explicit, separately counted, and occurs only
  after the requested timing interval.
- **NFR-SURFACE-002 — interaction:** The normal frame path uses immutable scene
  snapshots, bounded offers, nonblocking polls, and at most one configured
  bounded wait on pressure. No per-frame device-wide idle, hidden sleep loop,
  or global cache drain is permitted.
- **NFR-SURFACE-003 — ownership:** Retained device bytes are reported per live
  slot plus fixed session resources. Every allocation, release, completion,
  presenter release, and device-loss recovery is counted; no resource may be
  released before its exact receipts resolve.
- **NFR-SURFACE-004 — latency evidence:** Record monotonic host p50/p95 for
  offer, poll, bounded wait, compute retirement, presenter release, and total
  frame publication separately. Optional Vulkan timestamps carry availability
  and are never presented as host timings.
- **NFR-SURFACE-005 — parity:** C Vulkan, Simple Vulkan, Chrome, and Simple web
  rows are comparable only with identical viewport, workload, warmup/sample
  count, timing scope, GPU identity, readback/capture mode, checksum semantics,
  fallback state, and non-seed provenance. Missing or mismatched evidence
  yields `skipped`, never a ratio.
- **NFR-SURFACE-006 — resolution:** The existing 8K-primary sweep remains the
  acceptance target: 800x600, 1080p, 4K, and 8K must be reported, with no hard
  upper resolution limit and no ratio degradation beyond the approved target.

## Verification

The system test plans for browser surface ownership and Vulkan async submission
ring are the authoritative evidence plans. Device-free fixtures prove control
flow only; live-device rows are required before any performance claim.
