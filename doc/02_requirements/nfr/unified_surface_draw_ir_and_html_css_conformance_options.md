<!-- codex-research -->
# NFR Options — Unified Surface Draw IR and HTML/CSS Conformance

Status: user selection required

## NFR 1 — Strict compatibility and measured hot paths (recommended)

- Zero intentional pixel/semantic changes during pure refactor phases.
- Dual-run legacy and Draw IR paths on a pinned corpus until parity passes.
- No duplicate backend/font/image/diff/cache implementation.
- Frame allocation and command counts are bounded and reported.
- Warm representative repaint target: p95 below 16.7 ms for small retained
  GUI/TUI changes and below 100 ms for a small web subtree change on the
  declared reference machine; full-frame results reported separately.
- Max RSS and retained-cache size recorded for each surface class.
- Vulkan, CUDA, HIP/ROCm, Metal, and DirectX report actual device execution,
  accelerated/fallback command counts, upload bytes, dispatch/draw counts,
  presentation mode, readback source, checksum, p50/p95, and max RSS.
- A backend may claim a fully GPU-rendered frame only when every required
  command executes on the selected device and readback/presentation provenance
  proves that device; mixed CPU/GPU frames remain explicit.
- Unsupported HTML/CSS remains explicit and fail-closed.

Pros: strongest regression and performance control.
Cons: more evidence work before legacy deletion.
Effort: L, 8–15 additional evidence files.

## NFR 2 — Compatibility-first without fixed latency gates

- Same semantic/pixel parity and no-duplication requirements.
- Record timings and RSS, but defer hard budgets until baselines stabilize.

Pros: faster initial migration.
Cons: performance regressions can remain non-blocking too long.
Effort: M, 4–8 evidence files.

## NFR 3 — Fast cutover with fallback

- Default new Draw IR paths once smoke fixtures pass.
- Keep legacy paths as runtime fallback.

Pros: shortest route to production exposure.
Cons: retains duplicate logic indefinitely and makes regressions harder to
attribute; does not satisfy the requested no-duplication outcome.
Effort: M initially, potentially XL cleanup debt.
