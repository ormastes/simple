# Bug: `src/lib/blink/paint/paint_tree_walker.spl` and `src/lib/blink/layout/block_flow.spl` do not exist — spec targets an unimplemented module

Date: 2026-07-20

## Symptom

`test/01_unit/lib_standalone/blink/.spipe_matchers_image_paint_spec.spl`:
```
error: semantic: Cannot resolve module: std.blink.layout.block_flow

error: test-runner: no examples executed

=========================================
Test Summary
=========================================
Files: 1
Passed: 0
Failed: 1
Duration: 196ms

FAIL test/01_unit/lib_standalone/blink/.spipe_matchers_image_paint_spec.spl
```

Command:
```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib_standalone/blink/.spipe_matchers_image_paint_spec.spl --no-session-daemon
```

## Root cause: not a stale import — the target module tree does not exist

The spec's header declares:
```
# @cover src/lib/blink/paint/paint_tree_walker.spl 85%
```
and imports:
```
use std.blink.layout.block_flow.{
    LayoutContext, LayoutBox, BoxGeometry,
    box_geometry_new, layout_box_new, layout_context_new
}
use std.blink.paint.paint_tree_walker.{
    StyledBox, ImageEntry, PaintContext,
    paint_tree_new_with_images, collect_display_list, finalize_paint
}
use std.common.render_scene.paint_types.{PaintOp, DisplayList}
```

Checked against the actual repo tree:
- `src/lib/blink/` exists but contains only `css_parser/` and `dom/`
  subdirectories — **no `paint/` or `layout/` subdirectory at all**.
- `src/lib/blink/paint/paint_tree_walker.spl` does not exist anywhere in the
  repo (`find ... -iname '*paint_tree*'` returns nothing).
- `src/lib/blink/layout/block_flow.spl` does not exist either.
- None of the symbols `BoxGeometry`, `box_geometry_new`, `layout_box_new`,
  `StyledBox`, `ImageEntry`, `PaintContext`, `paint_tree_new_with_images`,
  `collect_display_list`, `finalize_paint` are defined anywhere in `src/`.
- `std.common.render_scene.paint_types.{PaintOp, DisplayList}` DOES resolve
  fine (`src/lib/common/render_scene/paint_types.spl` exists) — only the
  `std.blink.layout.*` and `std.blink.paint.*` halves are missing, so this
  compiler error surfaces on the first missing import only (`block_flow`);
  the second missing import (`paint_tree_walker`) is never reached.

This is the "Phase B2 image-paint path" feature per the spec's own docstring
— test scaffolding was written ahead of the production implementation, and
the production module (`paint_tree_walker.spl` + its `LayoutContext`/
`BoxGeometry` layout-box dependency) was never landed (or was removed without
removing the spec). No test-only edit can fix this: implementing the fix
requires writing the actual `blink/layout/block_flow.spl` and
`blink/paint/paint_tree_walker.spl` production modules, which is out of scope
for a test-shard fix.

## Affected

- `test/01_unit/lib_standalone/blink/.spipe_matchers_image_paint_spec.spl` (whole file, 0 examples executed)
