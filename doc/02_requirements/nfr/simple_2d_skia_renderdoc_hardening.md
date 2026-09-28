<!-- codex-research -->
# Simple 2D, Skia and RenderDoc nonfunctional requirements

Selected by the user on 2026-09-26: evidence option **N2**. The existing broader rendering latency budgets remain separate; this selection adds no performance or draw-count admission target.

| ID | Target | Verification |
|---|---|---|
| NFR-2D-001 | Deterministic offline schema, preflight and failure tests; unsupported features and missing evidence never count as success. | Focused unit/integration and SPipe scenarios with explicit blocked/failure states. |
| NFR-2D-002 | At least one physical Linux Vulkan device qualifies completed output for the selected scenes. Record device, driver, API, Skia revision, backend, fixture hashes and capture provenance. | Device identity and replay/readback artifacts from an admitted Linux run. |
| NFR-2D-003 | Canonical pixels for controlled primitives match exactly. Font and antialiasing cases use fixture-specific, declared tolerances and pinned assets; tolerance cannot be inferred after seeing a mismatch. | Byte comparison and fixture-level thresholds recorded before qualification. |
| NFR-2D-004 | Every comparison validates exact RGBA byte length and domain metadata before digest or tolerance checks. Ambiguous target, incomplete frame, unsupported conversion or absent GPU produce distinct, nonpassing outcomes. | Malformed metadata, missing target, compute-only and device-absence regression scenarios. |
| NFR-2D-005 | Default embedded builds do not link upstream Skia. The optional provider has deterministic setup, teardown and failure behavior. | Link/build inspection and provider lifetime tests. |

N2 qualifies one physical Linux Vulkan device. Windows and software Vulkan lanes are outside this selection. A macOS/offline test cannot satisfy NFR-2D-002; report that criterion as blocked until a genuine device run exists.
