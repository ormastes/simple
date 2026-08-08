# Render-lane specs import modules that were never implemented (2026-08-08)

**Status:** partially fixed — 2 of 27 specs unblocked, 25 remain legitimately RED
**Area:** `src/lib/{cc,blink,content}` (Chromium-mirror render lane)

## Summary

26 spec files under `test/01_unit/lib/{cc,blink,content}` were written spec-first
against a Chromium-mirror module layout (`std.cc.*`, `std.blink.*`) whose modules
were never implemented. 24 distinct modules are absent from `src/lib/`.

The same specs are duplicated across three test trees — `test/01_unit/lib/`,
`test/01_unit/lib_standalone/` (`.spipe_matchers_*`), and `test/unit/lib/` — so
**76 spec files** in total are affected by the same 24 missing modules.

## These specs are NOT vacuous-green

This was audited specifically because an unresolved `use` is only a *warning* in
this repo (see `reference_unresolved_use_is_only_a_warning...`), which can make a
spec pass while importing nothing. **That is not what happens here.** The
single-file runner fails closed on module resolution:

```
error: semantic: Cannot resolve module: std.cc.entity.layer
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed        (rc=1)
```

`doc/08_tracking/test/test_result.md` independently records both specs as 🔴 with
a 100% failure rate. So the red is honest — these specs were *not* fabricating
confidence, they were correctly reporting an unimplemented feature.

## Fixed in this change

Three modules implemented against the API the specs already pinned down:

| Module | Spec | Result |
|---|---|---|
| `src/lib/blink/entity/paint_chunk.spl` | `blink/paint_chunk_spec.spl` | 6 total, 6 passed |
| `src/lib/cc/entity/layer.spl` | (dependency of the two below) | — |
| `src/lib/cc/entity/layer_tree_host.spl` | `cc/layer_tree_host_spec.spl` | 8 total, 8 passed |

Plus `SkRect.make_xywh` added to `src/lib/skia/entity/geometry.spl` — the
`layer_tree_host` spec calls it as a static constructor; only the free function
`sk_rect_make_xywh` existed.

Landing `src/lib/cc/entity/layer.spl` also removed one of the three missing
imports from `cc/picture_layer_impl_spec.spl`.

### Note: `blink.entity.paint_chunk` is NOT the existing `PaintChunk`

`PaintChunk`-named types already exist in
`src/lib/common/ui/render_opt/paint_chunk_rasterizer.spl` (`PaintChunkRects`,
`ChunkRasterBuffer`). Those are a *rasterizer* concern — pixel buffers and rect
lists. The Blink `PaintChunk` is a display-item grouping keyed by
`PropertyTreeState`. Repointing the spec at `render_opt` was considered and
rejected: the concepts do not correspond.

## Sabotage verification

| Spec | baseline | sabotaged | restored |
|---|---|---|---|
| `blink/paint_chunk_spec.spl` (`size()` off-by-one) | 6/6 pass | 5/6 pass, 1 fail | 6/6 pass |
| `cc/layer_tree_host_spec.spl` (`next_id` not advanced) | 8/8 pass | 7/8 pass, 1 fail | 8/8 pass |

Restores were verified byte-for-byte against pre-sabotage `git hash-object`
snapshots, not just by re-running.

### Non-discriminating scenario found

`cc/layer_tree_host_spec.spl` → *"changing pending after commit does not mutate
active"* does **not** discriminate. Replacing `commit()`'s
`me.active_tree = me.pending_tree.clone_tree()` with a bare
`me.active_tree = me.pending_tree` still yields 8/8 pass, because class
assignment already copies by value in this engine. The scenario therefore proves
nothing about commit isolation. It should be rewritten to assert isolation
through a mutation the copy cannot mask, or dropped.

## Remaining gap — 24 modules, 25 specs still RED

These are left RED deliberately, per `.claude/rules/testing.md`: *"A correct spec
that fails is a legitimate artifact ... leave it RED, file a bug record."* They
are not stubbed, skipped, or deleted.

| Spec (under `test/01_unit/lib/`) | Missing module(s) |
|---|---|
| `blink/block_flow_spec.spl` | `std.blink.layout.block_flow` |
| `blink/computed_style_spec.spl` | `std.blink.entity.computed_style` |
| `blink/document_spec.spl` | `std.blink.dom.document` |
| `blink/flex_spec.spl` | `std.blink.layout.flex` |
| `blink/form_paint_spec.spl` | `std.blink.dom.form_state` `std.blink.layout.block_flow` `std.blink.paint.paint_tree_walker` |
| `blink/hit_test_spec.spl` | `std.blink.layout.block_flow` `std.blink.input.event` `std.blink.input.hit_test` |
| `blink/html_tokenizer_spec.spl` | `std.blink.html_parser` |
| `blink/html_tree_builder_spec.spl` | `std.blink.html_parser` `std.blink.html_parser.tree_builder` |
| `blink/image_paint_spec.spl` | `std.blink.layout.block_flow` `std.blink.paint.paint_tree_walker` |
| `blink/inline_flow_spec.spl` | `std.blink.layout` |
| `blink/input_event_spec.spl` | `std.blink.input.event` |
| `blink/navigation_controller_spec.spl` | `std.blink.navigation.controller` `std.blink.url.url_parser` |
| `blink/navigation_fetch_spec.spl` | `std.blink.network.fetch` `std.blink.navigation.controller` |
| `blink/paint_artifact_spec.spl` | `std.blink.entity.paint_artifact` |
| `blink/paint_controller_spec.spl` | `std.blink.feature.paint.paint_controller` `std.blink.entity.paint_artifact` |
| `blink/paint_tree_walker_spec.spl` | `std.blink.layout.block_flow` `std.blink.entity.computed_style` `std.blink.paint.paint_tree_walker` |
| `blink/scroll_manager_spec.spl` | `std.blink.scroll.manager` |
| `blink/style_cascade_spec.spl` | `std.blink.entity.computed_style` `std.blink.style.cascade` |
| `blink/url/url_parser_spec.spl` | `std.blink.url.url_parser` |
| `cc/layer_base_spec.spl` | `std.cc.entity.layer_base` |
| `cc/picture_layer_impl_spec.spl` | `std.cc.feature.raster_source` `std.cc.feature.picture_layer_impl` |
| `cc/tile_manager_spec.spl` | `std.cc.entity.tile` `std.cc.feature.raster_buffer_provider` `std.cc.feature.tile_manager` |
| `cc/tile_spec.spl` | `std.cc.entity.tile` |
| `content/web_contents_spec.spl` | `std.blink.entity.paint_artifact` |
| `content/.spipe_matchers_web_contents_spec.spl` | `std.blink.entity.paint_artifact` |

Each has mirrored copies under `test/01_unit/lib_standalone/` and `test/unit/lib/`.

**Unblock condition per row:** implement the listed module(s) against the API the
spec already pins, then confirm the spec's `Results:` line reports a non-zero
executed count. The two rows fixed above are the worked example — each took one
small value-object module.

**Highest-leverage next targets** (each unblocks the most specs per module):
`std.blink.layout.block_flow` (4 specs), `std.blink.entity.paint_artifact`
(4 specs), `std.blink.entity.computed_style` (3), `std.blink.paint.paint_tree_walker`
(3), `std.cc.entity.tile` (2).

## Modules that DO exist (not part of this gap)

`std.blink.css_parser.{parser,selector,tokenizer}`, `std.blink.dom.{node,interaction_state}`,
`std.cc.entity.property_tree`, all of `std.viz.*`, `std.content.entity.web_contents`,
`std.content.feature.render_widget_host_view`. Their specs resolve and run.
