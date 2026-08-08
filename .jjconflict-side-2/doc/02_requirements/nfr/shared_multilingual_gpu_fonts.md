<!-- codex-research -->
# Shared Multilingual GPU Fonts — NFR Requirements

Status: selected NFR A on 2026-07-11

- **NFR-001 Integrity:** All selected font/source inputs and generated manifests
  have immutable hashes, complete license metadata, deterministic regeneration,
  and fail-closed validation.
- **NFR-002 Correctness:** Pin fixtures, viewport, color space,
  premultiplication/rounding, comparator, device/driver, warmups, samples, and
  percentile method. The integer alpha reference is exact RGBA8; broader native
  AA uses fixed absolute edge/coverage limits. Equality alone is insufficient.
- **NFR-003 Distribution:** Core bundled font assets plus notices are at most
  80 MiB.
- **NFR-004 Warm performance:** After one warm run, the standard mixed-language
  fixture has at least 95% cache hits. Warm 1,024-glyph text p95 is at most 4 ms
  at 1080p and 8 ms at 4K on each promoted native backend.
- **NFR-005 GPU benefit:** Promote a route only when equal-semantics 4,096-glyph
  end-to-end p95 is at least 1.25× faster than its CPU oracle, including upload,
  queue, and synchronization but excluding explicit evidence readback.
- **NFR-006 Memory/upload:** No full atlas upload occurs on unchanged warm
  frames. 2D/3D integration adds at most 10% RSS over equivalent legacy
  fixtures; standard-fixture GPU resource high-water is at most 128 MiB.
- **NFR-007 Reliability:** Corrupt assets/programs, unsupported formats, device
  loss, and compile/submit failure fall back without corrupting active atlas/run
  identity or regressing unchanged CPU-fixture p95.
- **NFR-008 Evidence:** Report shaping, material, emission/compile, dirty upload,
  queue, device, sync, present/readback, CPU, RSS, and GPU resource stages.
  A fused submit-through-device-completion API may report queue/device as one
  explicit interval; it must not be presented as disjoint queue and device
  time. Offscreen rendering reports present as not applicable while retaining
  mandatory device-origin readback.
  Promotion requires compiled versioned entry, nonzero handles, payload hash,
  submit/draw, completed fence, device-origin nonblank absolute readback, and
  CPU-oracle comparison.
