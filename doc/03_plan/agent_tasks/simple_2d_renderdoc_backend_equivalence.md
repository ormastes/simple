# Simple 2D RenderDoc Backend Equivalence Agent Tasks

## Shared Contract

- Interfaces: `BackendRenderRecord`, `BackendRenderRecordDiff`, `BackendRenderEquivalenceResult`, `capture_backend_render_record`, `compare_backend_render_records`, `verify_backend_render_equivalence`.
- Manual steps: prepare fixture; capture records; validate provenance/completion; compare detailed state; compare absolute pixels; report mismatch/host limitation.
- Helpers: existing setup/evidence tools, `test/helpers/renderdoc_capture_helper.shs`, and `scripts/check/check-simple-2d-renderdoc-backend-equivalence.shs`.
- Any unresolved helper fails explicitly with `fail(...)`; no pass-shaped placeholder or synthetic positive evidence.

## Lanes

| Lane | Owner | Files/scope | Handoff |
|---|---|---|---|
| A — schema | lower-model sidecar advisory; primary implements | `src/lib/common/renderdoc/`, unit spec | Pure model/validation/canonical/diff/equivalence |
| B — Engine2D | primary | backend trait, capture adapter, Vulkan/DirectX/Metal/software, integration specs | Honest snapshots/provenance/readback |
| C — web/SSpec | lower-model sidecar advisory; primary implements | web facade, corpora fixtures, system specs/manuals | Modern structure-before-pixel scenarios |
| D — platform/capture | lower-model sidecar advisory; primary implements | Simple replay inspector, existing RenderDoc/platform wrappers, aggregate | Replay-open and fail-closed matrix |
| E — SimpleOS/QEMU/board/SIMD | lower-model sidecar advisory; primary implements | runtime per-op vector counters, hosted strict SIMD facade, noalloc receipt/SIMD kernels, common target/SIMD evidence, compositor/QMP adapters, board catalog, QEMU/board specs | Guest-native exact evidence, portable board contract, target-native vector execution |
| F — docs | primary | architecture/design/guides/reports/generated manuals | Operator-readable current contracts |

## Coordination

- Merge owner: primary Codex `/root`.
- Sidecars were read-only design auditors because this checkout has concurrent unrelated SimpleOS/compiler work.
- Generated-manual review owner: primary Codex, then final normal/highest-capability reviewer.
- Final reviewer: highest available normal Codex; it must independently review sidecar findings, exclusions, native-host limitations, false-green controls, manuals, and all release-blocking evidence.
- Files outside this lane remain other-session work and are excluded from commits/status claims.

## Order

1. Add failing unit/integration/system specs and generate manuals.
2. Implement common schema algorithms.
3. Implement backend snapshots/facade capture and correct readback provenance.
4. Implement SimpleOS receipt/QMP correlation and target-native SIMD lanes.
5. Implement replay inspection/aggregate and web corpus profiles.
6. Refactor docs/wiki, verify once per AC, and run highest-capability review.

## Remaining External-Evidence Handoff

- TODO 528 is closed as of 2026-07-11 on a Metal-capable macOS host:
  framebuffer readback, CPU/Metal parity, Electron/Chrome/Simple Metal browser
  backing, and macOS Metal render-log compare all pass with zero blocked gates.
- TODO 529: obtain an independently reviewed SimpleOS QEMU framebuffer oracle
  before enabling exact x86_64/AArch64/RV64 guest comparisons.
- Do not replace remaining prerequisites with a software fallback, generated
  baseline, tolerance, or synthetic positive receipt.
