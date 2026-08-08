# Simple 2D RenderDoc Backend Equivalence NFRs

Selected by the user on 2026-07-10: **NFR Option B — Intensive CI Gate**.

## Quality and Correctness

- NFR-001: All exact pixel comparisons require `mismatch_count=0` and `blur_or_tolerance=false`.
- NFR-002: Detailed records serialize identically across 10 repeated runs after documented nondeterministic normalization.
- NFR-003: Every backend-specific pass proves requested/actual API provenance, frame completion, positive handle, nonblank output, and independently computed oracle values.
- NFR-004: Missing tools, unsupported hosts, absent native APIs, capture-open failures, fallback, and contradictory evidence fail closed with stable machine-readable reasons.
- NFR-005: New/changed Simple code achieves at least 80% branch coverage and contains no stubs, placeholder passes, empty helpers, boolean-wrapper assertions, or direct raw runtime shortcuts outside owners.

## Performance and Scale

- NFR-006: The focused record/diff/oracle gate completes within 15 minutes on the reference Linux host.
- NFR-007: The complete Linux intensive suite completes within 60 minutes, excluding separately scheduled native Windows/macOS checkpoints.
- NFR-008: Primitive/effect stress scenarios run 100 repeated frames per case with bounded memory and deterministic results.
- NFR-009: Every intensive run records elapsed time and max RSS; retained paths may not regress max RSS by more than 10% from the recorded baseline without a tracked explanation and user-approved target change.
- NFR-010: The default intensive matrix includes all 50 production layouts and sampled 132-site/43-widget runs; exhaustive all-site/all-widget-per-backend qualification remains an optional scheduled profile, not an ordinary presubmit.

## Maintainability and Operations

- NFR-011: One versioned schema and one canonical comparator are shared by Vulkan, DirectX, Metal, translated lanes, web fixtures, and capture replay; no platform-specific duplicate record models.
- NFR-012: Generated manuals report zero stubs and explain setup, steps, artifacts, exact equality rules, host limitations, and troubleshooting without requiring source inspection.
- NFR-013: Verification runs each acceptance criterion at most once per session and performs no more than three verify/fix cycles.
- NFR-014: The SimpleOS/board evidence path uses a bounded noalloc-compatible receipt/event format in the guest, performs no subprocess or filesystem scan in the render loop, reaches the same deterministic result across 10 QEMU boots, and keeps physical-board status fail-closed until real board identity and capture/transcript evidence are supplied.
- NFR-015: SimpleOS framebuffer comparisons are exact (`mismatch_count=0`, no percentage threshold, blur, or tolerance); guest serial receipt and host capture must share the same run/frame identity and firmware hash.
- NFR-016: QEMU SIMD qualification is target-native: host SIMD reports, target-feature declarations, scalar aliases, NOP stubs, and shared arithmetic labeled “SIMD” are insufficient. Each architecture must execute its own vector instruction path, expose positive operation counters, and remain deterministic across 10 guest boots.
