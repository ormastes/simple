# Chrome layout geometry re-baseline on the fresh runner — 2026-09-14

## Context

PR #959 found the shared runner `build/cargo-r2/release/simple` was built
2026-09-12, one commit before `08770cc5025` (2026-09-14) added the extern
`rt_engine2d_blend_cov_span_u32` (registered in
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs`, declared/called
from
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl`).
On the stale binary that extern silently returned nil at the interpreter
dispatch layer — no crash, no error — so `fb_soft_box_shadow` quietly stopped
painting, and the web layout emitted all-`(0,0,0,0)` boxes on affected
catalog pages. Rounds 11-13's per-page geometry totals recorded against that
stale binary are **void for any page whose shadow path was exercised** and
are superseded by this document for `html`, `css-layout`, `css-paint`,
`forms-media`, and `animation`.

## Runner rebuild

```
sh scripts/setup/build-gpu-seed.shs --verify
```

| | before (PR #959 finding) | after |
|---|---|---|
| path | `build/cargo-r2/release/simple` | same |
| size | 39528776 bytes | 39581608 bytes |
| mtime | 2026-09-12 16:57:30 | 2026-09-14 08:34:50 |
| sha256 | `606d464fee80a9576a6d4cc7bfa388582992f2aa2e6a212143041a15d6fbce94` | `2d0669321ebbc805355013f21327f0ea4903aec01ee5652b8b35e58aefa07b9c` |
| git HEAD built from | (predates `08770cc5025`) | `794fbf5394fb7e15ebab5961d11db63599d648fd` (includes `08770cc5025`) |
| features | vulkan,metal,simple-compiler/vulkan-graphics (assumed) | vulkan,metal,simple-compiler/vulkan-graphics (confirmed by build log) |
| build-gpu-seed `--verify` | not run | `PASS — 5 capability probe(s) executed` |

Built with `CARGO_TARGET_DIR=/Users/ormastes/simple/build/cargo-r2`, warm
cache, `Finished release profile [optimized] target(s) in 1m 12s`.

## Fix confirmed

`nm` on the binary shows **zero** hits for `rt_engine2d_blend_cov_span_u32` —
this is expected and not a regression: interpreter-dispatched externs are
registered into a runtime `HashMap` via the `insert_simple!` macro
(`interpreter_extern/mod.rs`), not exported as linkable/nm-visible symbols, so
`nm` cannot prove dispatch either way. The actual proof is
`build-gpu-seed.shs --verify`'s capability-probe path, which runs real specs
under `SIMPLE_EXECUTION_MODE=interpreter` and fails on `unknown extern
function` — it reported `PASS — 5 capability probe(s) executed` against this
binary, meaning every extern it probes (including the renderer/Vulkan paths
that exercise this dispatch machinery) resolves and executes without error.

## Geometry differential — html page (confirmed non-degenerate)

```
SIMPLE_BIN=build/cargo-r2/release/simple GEOM_DIFF_PAGES=html \
  GEOM_DIFF_HEIGHT=20000 sh scripts/check/check-chrome-layout-geometry-diff.shs
```

Result: `PASS — 431 element(s) compared, 430 mismatched`. This is the direct
before/after proof requested for this task: on the stale binary the
soft-box-shadow path returned nil boxes; on the fresh binary the differ
produces a full 431-element comparison with real, non-zero, non-degenerate
`dx/dy/dw/dh` values across the whole document (root mismatches: 401,
inherited: 29, 0 elements missing on the Simple side, 1 Simple-only box at
`path:(body)`). Raw output:
`build/chrome_layout_geometry_diff/html.geometry_diff.md`.

This one page took ~9 minutes wall time under
`SIMPLE_EXECUTION_MODE=interpreter` for the Simple-side render + diff (the
interpreter's known slow path for this renderer, noted in `08770cc5025`'s own
commit message: "the interpreter benchmark harness could not complete even a
6-row x 160-px case inside 560 s"). At that per-page cost the remaining 7
catalog pages (css-layout, css-paint, forms-media, animation, overview,
evidence, tab-bar) were **not** run in this session — a full re-baseline
across all 8 pages is estimated at 60-70+ minutes serial wall time and is
deferred as follow-up work, tracked alongside this document. Do not read the
absence of the other 7 pages' numbers as "no regression there" — round
11-13's html/css-layout/css-paint/forms-media/animation totals remain void
until each page is re-measured against this (or a later) fresh binary.

**SUPERSEDED 2026-09-14 (round 14) — and the 431/430 html figure above is
itself void.** The full 8-page re-baseline was run:
`doc/10_metrics/ui/web_chrome_parity_round14_2026-09-14.md`. It also found that
the fresh binary was not the only reason the numbers were bad. The renderer arms
its OWN wall-clock budget (`WEB_RENDER_BUDGET_MS`, 10 s), which
`SIMPLE_TIMEOUT_SECONDS=0` does not disable; on `html.html` it truncated the
style pass at node 46 of 883, so the Simple side was again all-zero and "430 of
431 mismatched" was a measurement of the deadline, not of CSS. With the budget
lifted the same page reports **329**. See
`doc/08_tracking/bug/web_render_budget_truncates_geometry_differ_layout_2026-09-14.md`.
Two harness fixes landed with it: the budget is now pinned by the differ script,
and the differ fails closed on a degraded render.

## Guard added

`scripts/check/check-runner-binary-extern-freshness.shs` (advisory, push
tier) — flags a deployed runner binary older than the declaring source of an
`extern fn rt_*` under `src/lib/**`, unless the symbol is already in
`scripts/check/unbacked_extern_baseline.txt`. Run against the fresh binary:
`PASS — 3323 extern(s) checked, 0 newer than
/Users/ormastes/simple/build/cargo-r2/release/simple`. `--selftest`:
`SELFTEST PASS — 2 fixture(s) checked`. Wired into
`config/check/must_check_gates.sdn` (`push-runner-binary-extern-freshness`)
and `scripts/check/check-push-must-pass.shs`;
`check-guard-wiring.shs` reports `0 NEW unwired`.
