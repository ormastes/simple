<!-- codex-design -->
# Selected C/N2 system evidence plan

Status: C/N2 selected on 2026-09-26. Existing focused tests cover bounded repairs; broader executable specs and physical Linux Vulkan evidence are in progress.

The physical Linux handoff is tracked in
`doc/08_tracking/todo/simple_2d_skia_renderdoc_linux_n2_2026-09-27.md`.

| Scenario | Real observation |
|---|---|
| Unsupported op after a valid rectangle | Strict mode errors before any render; preview reports incompleteness |
| Fractional coordinate / elliptical radius / ignored paint | Semantics preserved or explicit strict rejection |
| Empty, malformed and unavailable output digest | Parser and comparison reject evidence |
| Same pixels, differing draw/compute counts | Visual equivalence independent of event order |
| Missing final target / incomplete readback | Typed blocked/error status, never PASS |
| Fractional shared-IR round-trip | Producer coordinates and glyph identities survive serialization |
| Web / GUI matched scene | Same admitted scene and completed pixel domain |
| Native provider context loss / shutdown | Resources retired safely and error propagated |

Reuse existing bridge and renderdoc_diff tests before adding new mirrors. System specs belong under `test/03_system/`; generated Markdown mirrors live under `doc/06_spec/`. Primary manuals explain pinned scene, preflight, render, capture admission and pixel comparison using the agreed helper names. Exact fixture bytes and metadata, independent oracles, and explicit non-admission of unsupported environments prevent vacuous success. Run only selected checks once after final edits; do not claim source inspection as execution.

## Qualification scene policy

The initial N2 physical-device matrix is `01-solid-boxes` (controlled integer primitives, exact RGBA), `06-rectangular-clip` (source-derived parent clip, exact RGBA), `02-fractional-edges` (fractional geometry/AA), `31-latin-shaping` (font shaping), and one GUI button/input scene emitted by `widget_tree_to_draw_ir`. The full 48-case corpus is an integration inventory; each additional case needs its own declared comparator before admission. The HTML fixture hashes and viewport/DPR are pinned by the corpus manifest. Pin the font bytes, backend binaries, upstream Skia revision and physical device identity before any cross-backend result is accepted.

For the first device run, exact RGBA is required for `01-solid-boxes`. Before executing `02-fractional-edges`, `31-latin-shaping`, or the GUI case, place a fixture-specific numeric threshold and an independent oracle in the run manifest; absent thresholds make those rows **blocked**, never automatic PASS. Thresholds cannot be chosen from observed mismatches. This policy avoids treating the supplied CPU Chromium screenshots as Vulkan goldens.

`02-fractional-edges` remains blocked pending trusted execution and physical
backend evidence. The strict Web producer now has source code for the painted,
clipped `#scene`, both leaves and seven-degree transform; its focused spec has
not run through a trustworthy Simple executable. DrawIR/SDN v4 and UiIr v2
carry affine state. The six-command Web source-to-GPU v4 projection, both
case-specific capture adapters, the analytic oracle, and runner commands
`run-corpus-case02` / `verify-corpus-case02` are connected in source. Engine2D
has a candidate Vulkan polygon-coverage path. Skia private v3 drawing has an
explicit build opt-in, default off, and lacks a pinned-header build and
submitted-matrix provenance. Neither backend has case 02 device pixels here.

The GUI input producer now has a pinned 160 × 40 focus/type/caret scene with
before/after DrawIR receipts. Its physical Engine2D/Skia pixels are still
blocked. Engine2D has a strict Vulkan text path that needs fixture-specific
evidence; upstream Skia currently rejects every text command. The source
scene now pins the bundled Noto Sans Mono SHA-256 and requires the resolved
font identity, complete glyph arrays and caret bounds. Before adding GUI
input worker commands, define an independent
before/after pixel oracle and a bounded private native glyph contract. The
existing button scene remains the initial GUI physical candidate. The runner
has been split into scene, worker and receipt modules; compilation and runtime
behavior of that extraction remain unverified.

Before case 02 execution, require: (1) real-producer inventory including
canvas, scene background, rotated tile and fractional bar with stable source
indexes; (2) independent checks of CSS `T(base)·T(origin)·T(.25,.25)·R(7°)·T(-origin)`
order and surface clip; (3) DrawIR/SDN/UiIr v4 round trip and atomic rejection
of invalid matrices; (4) independent polygon/pixel coverage oracle for tile
and bar, exact interior/exterior checks, a predeclared edge tolerance and
color-domain metadata; (5) Vulkan GPU coverage without diagonal seams or CPU
fallback; (6) Skia private-v3 build and capture; (7) completed matching-device
physical receipts. The analytic oracle and tolerance are now pinned; missing
physical reference bytes and receipts keep manifest status `not-run`.

Requirement trace: bridge scenarios cover REQ-2D-001; shared-IR round-trip and UiIr consumption cover REQ-2D-002; completed final pixels and invalid-domain cases cover REQ-2D-003/004 and NFR-2D-003/004; optional provider lifetime and link checks cover REQ-2D-005/NFR-2D-005; Web/GUI scenes and physical-device receipts cover REQ-2D-006/NFR-2D-002. Offline negative cases cover NFR-2D-001.
