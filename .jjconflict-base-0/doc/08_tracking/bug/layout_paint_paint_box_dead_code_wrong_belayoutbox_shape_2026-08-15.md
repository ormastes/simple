# layout_paint.spl `_paint_box` is latent dead code built against the wrong BeLayoutBox shape

- **Date:** 2026-08-15
- **Status:** OPEN
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
