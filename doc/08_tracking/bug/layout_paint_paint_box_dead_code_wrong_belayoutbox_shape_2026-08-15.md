# layout_paint.spl `_paint_box` is latent dead code built against the wrong BeLayoutBox shape

- **Date:** 2026-08-15
- **Status:** RESOLVED 2026-08-16 (deleted) — `_paint_box` was removed from
  `layout_paint.spl` along with the imports only it used (BeLayoutBox, BeDomNode,
  dom_accessors, render_scene). Rationale: it had never run (semantic error at
  the first `box.node` access), nothing imported the module except the coverage
  spec, and porting it would require a `node_id -> BeDomNode` resolution no
  pipeline provides — deletion is the mandated non-over-engineering choice.
  `_apply_opacity` is kept and remains fully covered by
  `test/01_unit/browser_engine/layout_paint_coverage_closure_spec.spl`.
  Previously: OPEN — re-triaged 2026-08-15 during the layout_core port
  (see `layout_core_incompatible_with_committed_belayoutbox_2026-08-15.md`,
  now RESOLVED): `_paint_box` is NOT trivially fixable by that port, because
  it needs a `node_id -> BeDomNode` resolution (or style data carried on the
  box) that no current pipeline provides. Left as-is; deletion remains the
  ponytail choice.
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
