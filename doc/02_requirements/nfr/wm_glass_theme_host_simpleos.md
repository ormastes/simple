# WM Glass Theme on Host and SimpleOS — NFR Requirements

## Selected Direction

NFR Option A: exact semantic parity with capability-declared pixel evidence.
Host and SimpleOS must resolve the same theme fingerprint and material values;
pixel evidence may differ only where the backend declares and exercises a
specific supported fallback.

## Non-Functional Requirements

- **NFR-001 — Semantic parity:** host and canonical SimpleOS evidence report
  identical theme ID, theme revision/fingerprint, and normalized material
  semantics for the tested scene.
- **NFR-002 — Pixel provenance:** retained evidence records viewport, backend,
  fallback state, framebuffer/readback method, crop coordinates, checksums,
  source revision, binary identity, and artifact paths.
- **NFR-003 — Capability declaration:** blur, shadow, gradient, font, GPU, and
  readback capability/fallback decisions are structured and fail closed when
  unknown; evidence records the first unavailable proof rung.
- **NFR-004 — Stable visual assertions:** nonblank/full-frame checks plus stable
  semantic regions prove desktop, chrome, content, active/inactive depth, and
  post-interaction change. Region policies are documented rather than silently
  widened.
- **NFR-005 — Performance:** measure warm hosted startup, representative frame
  or request latency, QEMU first themed frame, and maximum RSS on the canonical
  fixtures; regressions require a fix or concrete tracking record.
- **NFR-006 — Accessibility:** text contrast and solid reduced-transparency
  fallbacks are mechanically checked for representative active/inactive
  surfaces.
- **NFR-007 — Determinism:** fixed inputs produce the same semantic fingerprint
  and region policy result across repeated checker invocations without relying
  on wall-clock text or unrelated animated pixels.
- **NFR-008 — Verification quality:** no stubs, TODO passes, dummy assertions,
  stale generated manuals, misplaced `.spl` specs, direct environment/process
  violations, or undocumented fallback can pass the final gate.
