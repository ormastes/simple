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

## Triage of the 24 missing modules (2026-08-09, doc-only pass)

Derived by reading every red spec at `origin/main` = `22a847bfd3043fb9be2a270fe21a147b19c2777a`.
No specs were run for this section — example counts are `it "` counts read from
source, not executed results. "Unblocks" = number of red specs under
`test/01_unit/lib/` that stop having an unresolved import once the module lands
(mirrored copies under `lib_standalone/` and `test/unit/` triple each number).

| # | Module | Unblocks | Examples gated | Demanded surface (verbatim from the `use` blocks) | Depends on |
|---|---|---|---|---|---|
| 1 | `blink.layout.block_flow` | 5 | 7 (+31 downstream) | `BoxGeometry` `LayoutBox` `LayoutContext`; `box_geometry_zero/new` `layout_box_new` `layout_context_new`; methods `add_box` `get_box` `set_root` `compute_layout` `total_height_for` | none missing |
| 2 | `blink.entity.paint_artifact` | 4 | 5 (+12 downstream) | `PaintArtifact` (`empty()` `item_count()` `chunk_count()`), `PaintChunk` (`create(begin_index,end_index,properties)`), `PaintChunkProperties` (`root()`, fields `transform_id/clip_id/effect_id`) | none missing |
| 3 | `blink.entity.computed_style` | 3 | 6 (+17 downstream) | `ComputedStyle` `Display` `Position` `Overflow` `Visibility` `TextAlign` `Length`; `computed_style_default`; methods `is_visible` `is_block_level` `is_positioned` `total_margin_horizontal` | none missing |
| 4 | `blink.paint.paint_tree_walker` | 3 | 6 (+11 downstream) | `StyledBox` `ImageEntry` `FormFieldPaintEntry` `PaintContext`; `paint_tree_new` `paint_tree_new_with_images` `paint_tree_new_with_forms` `paint_tree` `collect_display_list` `finalize_paint`; methods `paint_box` `find_style` | 1, 3; `common.render_scene.paint_types` (exists) |
| 5 | `cc.entity.tile` — **IN PROGRESS** | 2 | 7 (+6) | tile_spec: `Tile` `TileId` `TilePriority` `TileDrawState` `tile_id_new` `tile_new`; tile_manager_spec: `Tile.new` `TileKey.new` `TilePriority` | `skia.backend.cpu.raster_prims.Bitmap` (exists, has `zeros`) |
| 6 | `blink.url.url_parser` | 2 | 8 (+8) | `ParsedUrl` `parse_url` `percent_decode` `percent_encode` `query_string_parse` | none missing |
| 7 | `blink.navigation.controller` | 2 | 8 (+6) | `NavigationEntry` `NavigationController` `navigation_entry_new` `navigation_controller_new`; methods `navigate` `goto` `go_back` `go_forward` `can_go_back/forward` `history_count` `current_entry` `set_current_title` | 6 |
| 8 | `blink.html_parser` | 2 | 8 (+7) | `HtmlTokenKind` `HtmlAttribute` `HtmlToken` `tokenize_html` | none missing |
| 9 | `blink.input.event` | 2 | 8 (+7) | `InputEvent` `EventType` `ModifierFlags` `Point` `TouchPoint`; `mouse_event` `key_event` `char_event` `touch_event` `wheel_event` `touch_point`; methods `is_mouse/is_touch/is_keyboard` `has_modifier` `mark_handled` | none missing |
| 10 | `blink.style.cascade` | 1 | 11 | `parse_length_value` `parse_color_value` `parse_f64_value` `apply_declaration` `resolve_style` `resolve_style_with_state` | 3; css_parser + dom.node + interaction_state (all exist) |
| 11 | `blink.layout` (module root, inline flow) | 1 | 11 | `InlineItemKind` `InlineItem` `InlineBox` `LineBox` `InlineLayoutResult`; `inline_text` `inline_element` `layout_inline_flow` `wrap_text_run` `estimate_text_width` | none missing |
| 12 | `blink.layout.flex` | 1 | 8 | `FlexDirection` `JustifyContent` `AlignItems` `FlexItem` `FlexContainer`; `flex_item_new` `flex_container_row/column` `layout_flex` | none missing |
| 13 | `blink.scroll.manager` | 1 | 8 | `OverflowBehavior` `ScrollableArea` `ScrollManager`; `scrollable_area_new` `scroll_manager_new`; methods `register` `scroll_by` `scroll_element` `find_area` `can_scroll_y` `max_scroll_x/y` | none missing |
| 14 | `cc.entity.layer_base` — **IN PROGRESS** | 1 | 8 | `Layer` `LayerId` `LayerType` `layer_new` `layer_id_new`; methods `add_child` `remove_child` `child_count` `set_bounds` `set_opacity` `is_root` | none missing |
| 15 | `blink.dom.document` | 1 | 7 | `Document` `ReadyState` `document_new`; methods `create_element` `set_title` `set_ready_state` `is_loading` `is_complete` | none missing |
| 16 | `blink.html_parser.tree_builder` | 1 | 7 | `build_html_tree` | 8; `blink.dom.node` (exists) |
| 17 | `blink.feature.paint.paint_controller` | 1 | 7 | `PaintController` (`new`, `record_item`, `update_properties`, `commit`, `chunk_count`, `item_count`, indexed `get`) | 2 |
| 18 | `blink.input.hit_test` | 1 | 7 | `HitTestResult` `hit_test_empty` `point_in_rect` `hit_test` `hit_test_event` `hit_test_ancestors` | 1, 9 |
| 19 | `blink.dom.form_state` | 1 | 8 | `FormState` `FormFieldEntry`; `form_state_empty/with_field/set_value/get_value/get_placeholder` | none missing |
| 20 | `cc.feature.tile_manager` | 1 | 6 | `TileManager` (`new`, `add_tile`, `schedule_tasks`, `invalidate_tile`, `pending_count`, `ready_count`) | 5, 21 |
| 21 | `cc.feature.raster_buffer_provider` | 1 | (with 20) | `RasterBufferProvider.new` | 5 |
| 22 | `blink.network.fetch` | 1 | 6 | `FetchResponse` `fetch_text` (`is_ok`) | 7 |
| 23 | `cc.feature.raster_source` | 1 | 1 | `RasterSource.from_picture(SkPicture)` | `skia.entity.picture` (exists) |
| 24 | `cc.feature.picture_layer_impl` | 1 | (with 23) | `PictureLayerImpl.from_layer(Layer, RasterSource)`, field `.base` | 23; `cc.entity.layer` (landed) |

External dependencies were verified present at BASE, not assumed:
`skia/entity/geometry.spl` (`SkRect` `SkIRect` `SkPoint`), `skia/entity/picture.spl`,
`skia/capability.spl`, `skia/entity/matrix.spl`, `skia/backend/cpu/raster_prims.spl`
(`Bitmap.zeros`), `common/render_scene/paint_types.spl` (`PaintOp` `DisplayList`
`DisplayItem`), `common/color/types.spl` (`Color`). **No missing module is blocked
on anything outside this table.**

### Ranked next steps (top 5)

1. **`blink.layout.block_flow`** — highest fan-out of any module here: 5 red specs,
   and modules 4/18 cannot start without it. Pure value objects + a layout pass.
2. **`blink.entity.paint_artifact`** — 4 specs including both `content/` rows; the
   demanded surface is three field-only value types with static constructors, the
   same shape as the already-landed `blink.entity.paint_chunk`. Cheapest per spec.
3. **`blink.entity.computed_style`** — 3 specs, and it is the gate on modules 4 and
   10 (the whole style→paint chain). Enum-heavy, no behaviour beyond predicates.
4. **`cc.entity.tile` + `cc.entity.layer_base`** — already claimed by a running
   agent (see caveat below); listed here so the next session does **not** duplicate.
5. **`blink.url.url_parser`** — self-contained (no missing deps at all), 8 examples
   directly, and unblocks module 7 which in turn unblocks module 22, i.e. a
   3-module chain rooted in one dependency-free module.

### Production-consumer reality check

Only **one** production import of this lane exists at BASE:
`src/lib/viz/feature/aggregator_compose.spl:8` → `std.cc.entity.property_tree`
(which already exists). Verified by `git grep "use std\.\(blink\|cc\)\." -- src`
excluding `src/lib/{blink,cc}` — one hit. So **none of the 24 missing modules has a
live production consumer today**; the `cc.*` rows (5, 14, 20, 21, 23, 24) are the
ones on the same tier as that consumer, and the `blink.*` rows sit a tier above it.
Rank accordingly if consumer-proximity matters more than spec count.

### Cross-spec API conflicts a implementer must reconcile

- **`cc.entity.tile` is demanded with two different constructor conventions.**
  `tile_spec.spl` imports `TileId` + free functions `tile_id_new`/`tile_new`;
  `tile_manager_spec.spl` imports `TileKey` and calls `Tile.new(...)`/`TileKey.new(...)`.
  One module must export **both** shapes, or one spec must be corrected. Landing
  only one convention leaves the other spec red with a *different* error.
- **`cc.entity.layer_base.Layer` is a different type from the landed
  `cc.entity.layer.Layer`.** layer_base's has `LayerId`/`LayerType`, children
  (`add_child`/`child_count`), and `set_opacity`; the landed one is flat
  (`id`/`parent_id`/`kind`/`*_id`). Two same-named types in sibling `cc.entity.*`
  modules — decide whether that is intended before implementing.
- `blink.layout` (module root, used by `inline_flow_spec`) and
  `blink.layout.block_flow` are separate modules in the same namespace.

### Weak / low-discrimination specs spotted (beyond the layer_tree_host one)

Flagged because a red spec that would pass vacuously the moment a stub exists is
worse than no spec:

- **`cc/picture_layer_impl_spec.spl` — 1 example, 1 assertion, `expect(impl.base.id).to_equal(7)`.**
  Asserts only that `from_layer` stored the layer it was handed. Any stub that
  assigns `base` passes; `RasterSource` is constructed and then never observed.
  Two whole modules (23, 24) are gated on an oracle that tests one field copy.
- **`content/web_contents_spec.spl` — only 1 of its 7 examples touches the missing
  module**, and that one asserts `wc.last_paint.is_some() == true` after
  `update_paint(PaintArtifact.empty())` — true for any non-nil value. The other 6
  examples exercise already-existing `WebContents`; the file is red purely on the
  import. Landing module 2 turns 7 examples green while only 1 of them is actually
  about `PaintArtifact`.
- **`blink/paint_artifact_spec.spl` (5 examples)** is entirely constructor
  field-echo (`create` stores begin/end indices; `root()` has all ids 0). Acceptable
  for a value object, but it proves no behaviour — do not treat it as coverage of
  paint-chunk semantics.

`picture_layer_impl_spec` in particular should be strengthened *before* modules 23/24
are implemented, otherwise both land with a tautological oracle.

### Characterisation confidence

All 24 modules were characterised from their specs' import blocks and call sites;
none was left uncharacterised. Two residual uncertainties, stated rather than
guessed: (a) the exact **field** sets of the demanded types are not recoverable
where a spec only calls methods (e.g. `LayoutContext`), so the surface column lists
what is *named*, not a complete signature; (b) modules 5 and 14 are being
implemented by another session concurrently — the rows above describe what the
specs demand at BASE, not that session's in-flight design.

## Modules that DO exist (not part of this gap)

`std.blink.css_parser.{parser,selector,tokenizer}`, `std.blink.dom.{node,interaction_state}`,
`std.cc.entity.property_tree`, all of `std.viz.*`, `std.content.entity.web_contents`,
`std.content.feature.render_widget_host_view`. Their specs resolve and run.
