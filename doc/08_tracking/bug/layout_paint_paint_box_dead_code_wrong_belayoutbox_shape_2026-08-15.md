## RESOLVED 2026-08-17

`_paint_box` deleted from `src/lib/gc_async_mut/gpu/browser_engine/layout_paint.spl`
(with its now-unused imports). Confirmed dead: zero importers; the live paint walk is
`_browser_paint_boxes` in `browser_renderer.spl:207`.

Specs (mirror-synced, `diff -q` identical):
- repro/contract pin: `test/01_unit/browser_engine/layout_paint_contract_pin_spec.spl`
  and `test/unit/browser_engine/layout_paint_contract_pin_spec.spl`
- generalization/surviving surface: same file, `describe "layout_paint surviving surface (generalization)"`
- pre-existing coverage: `test/01_unit/browser_engine/layout_paint_coverage_closure_spec.spl`

Evidence:
```
SPEC FILE VERDICT: .../layout_paint_contract_pin_spec.spl declared>=6 executed=6 passed=6 failed=0 dropped=0
Results: 6 total, 6 passed, 0 failed
SPEC FILE VERDICT: .../layout_paint_coverage_closure_spec.spl declared>=4 executed=4 passed=4 failed=0 dropped=0
```
The pin spec asserts the REAL contract the dead code violated: `node_id` (no `node`
field), and `content_x()/content_y()/content_width()/content_height()` as METHODS.

# layout_paint.spl `_paint_box` is latent dead code built against the wrong BeLayoutBox shape

- **Date:** 2026-08-15
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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
