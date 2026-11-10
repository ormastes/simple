# layout_paint.spl `_paint_box` is latent dead code built against the wrong BeLayoutBox shape

- **Date:** 2026-08-15
- **Status:** FIXED (2026-11-11, lane ne13) — `_paint_box` deleted with a
  backing contract-pin spec by 36d99cf738d9 (2026-08-17); re-verified green on
  the release/1.0.0 seed. See addendum.
- **Component:** `src/lib/gc_async_mut/gpu/browser_engine/layout_paint.spl`
- **Severity:** low (dead code), but a semantic landmine

## Finding

`layout_paint.spl` imports `BeLayoutBox` from
`std.gc_async_mut.gpu.browser_engine.layout_box`, but its `_paint_box`
function is written against a different, nonexistent shape of that class:

- It reads `box.node` as a field. `BeLayoutBox` has **no `node` field** —
  it carries only `node_id: i64` (plus `tag_name`, `style`, ...).
- It reads `content_x` / `content_y` / `content_width` / `content_height`
  as **fields**. On `BeLayoutBox` these exist only as **methods**
  (`content_x()`, `content_width()`, ...), computed from padding/border.

So `_paint_box` cannot execute: any call would fail with a semantic
error at the first `box.node` access. It has never run.

## Why it sits green

No module imports `layout_paint` (`grep -rn "browser_engine.layout_paint"`
finds only the test spec added for coverage closure). The functions that
don't touch the broken field reads are exercisable and tested
(`layout_paint_coverage_closure_spec.spl`), but `_paint_box` itself is
unreachable, uncompiled-in-practice code.

## Suggested fix

Either delete `_paint_box` (and any helpers only it uses), or port it to
the real `BeLayoutBox` contract: resolve the DOM node via `node_id`
where needed, and call `content_x()` etc. as methods. Deletion is the
ponytail choice unless a paint pipeline is about to consume it.

## Addendum 2026-11-11 (lane ne13) — FIXED by 36d99cf738d9, re-verified

Deletion (the ponytail choice this doc recommended) landed in `36d99cf738d9`
(2026-08-17, "fix(browser_engine): delete _paint_box dead code; close 2 stale
bugs with evidence"): `_paint_box` and its now-dead imports were removed; the
live paint walk is `_browser_paint_boxes` in `browser_renderer.spl`. A
tombstone comment at the top of `layout_paint.spl` cites this doc.

Backing test (written ahead of the deletion, now the pin):
`test/01_unit/browser_engine/layout_paint_contract_pin_spec.spl`.
**Verification actually run** (seed-smoke, fresh seed 46fe8f6b6def,
`--mode=interpreter --no-cache`): **6 declared, 6 executed, 6 passed,
0 failed** — including "carries node_id, not a node object field" and
"content geometry is exposed as methods computed from box model", the exact
wrong-shape reads this doc flagged. No module imports `layout_paint` for
`_paint_box` (grep of the file shows only the tombstone).
