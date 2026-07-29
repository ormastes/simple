# WM Native Regression Gate Blockers — 2026-07-29

## Self-hosted source closure

The WM system and GUI shortcut specs initially stopped because the
repository-wide source closure reached:

```text
src/lib/skia/feature/shaper/ot_layout_shaper.spl
Unexpected Dedent
```

The conditional at that location and the unparenthesized multiline GPOS
variation-store condition have now been normalized to the older Phase-3
grammar. The focused `ot_layout_gpos_data.spl` source-entry closure builds and
links successfully with the existing Phase-3 compiler. The capped full WM
closure has not been retried, and no bootstrap was run.

## Freestanding aggregate regression

The targeted native parity fixture
`trait_optional_struct_return` now covers concrete-to-trait dispatch,
aggregate-by-value, module-global aggregates, aggregate `Option`/`Result`,
arrays in returned structs, and nested aggregate returns.

Its LLVM native build fails with:

```text
semantic: variable fld_base_sym not found
```

The second backend made no progress and was stopped once. Per the repository
runaway guard, neither command is retried in this session.

## Host runtime availability

The host initially had no system `libglfw.so`. A retained local GLFW runtime
under `build/wm_harden/glfw_root` later enabled the focused Xvfb probe, which
proved non-black presentation plus native key, text, pointer, clipboard, and
generation-safe teardown. That boundary is green; it is not full WM scene
evidence.

## Full hosted native entry

The checked hosted entry
`examples/06_io/ui/wm_full_stack_demo.spl` passes the one-file semantic check.
Its first entry-closure native build emitted no progress or diagnostic for
roughly 2.5 minutes:

```text
bin/simple native-build --entry examples/06_io/ui/wm_full_stack_demo.spl \
  --entry-closure -o /tmp/simple_wm_full_stack_demo
```

It was terminated once with exit 143. The command is not retried in this
session; the native build therefore remains unproven rather than inferred
from the semantic check.

## Pure-Simple Phase 3 entry build

At user direction, the seed-driven build was stopped and the existing
aggregate-fix Phase 3 compiler was used directly:

```text
build/aggfix/stage3/simple native-build ... \
  --cache-dir build/native_probe/phase3_cache \
  --entry examples/06_io/ui/wm_full_stack_demo.spl
```

After normalizing the multiline expressions rejected by that older parser,
the focused GPOS source-entry build and the full WM closure now complete. The
cold full closure built 512 modules; the final incremental pass compiled 3 and
reused 509 cached modules. No full bootstrap or Phase 2 retry was run.

The existing `SIMPLE_LINK_OBJECTS` final-link hook supplies the GLFW and
miniaudio provider objects. The resulting executable defines its active
`rt_glfw_*` and `rt_audio_*` symbols and no longer depends on an ineffective
preload for compiler-generated extern slots.

Two live native faults in theme parsing were the documented erased-result
`.to_i32()` misdispatch into `Px.to_i32()`. Typed `i64` intermediates with
`as i32` now carry those conversions. The third and final capped live attempt
passed host/audio initialization and theme loading, then faulted here before a
capturable frame:

```text
ProfileResolver.orientation_changed()
  <- UISession.dispatch()
  <- spl_main()
```

The profile receiver was changed to the established native-safe receiver form,
and resize dispatch now stores the event dimensions before profile
recomputation. The focused Phase-3 native probe reproduced the exact
`ProfileResolver.orientation_changed()` segfault before the change and passes
afterward with a 40x60 Portrait viewport.

The next full linked host run passed that route and reached the canonical GUI
renderer:

```text
common.ui.widget_draw_ir._emit_widget()
  <- widget_tree_to_draw_ir_with_theme()
  <- UISession.submit_widget_draw_ir()
  <- gui_session_content_frame()
```

Disassembly proved the `_emit_widget()` fault was the known aggregate
`Option<T>` payload defect: `find_rect() -> WidgetRect?` returned a raw
`WidgetRect`, `rt_is_some` accepted it, and `rt_enum_payload` produced tagged
nil. The renderer now uses scalar `find_rect_index()` lookups and direct array
reads for main and scroll paths, and no longer returns an optional scroll batch.

Targeted no-mangle pure-Simple archives now provide both
`rt_file_hash_sha256` and `fs_copy_cstr`. With both linked, the exact demo-tree
native probe passes and verifies root, button, scrollbar, embedded Simple 2D,
and embedded Simple Web Draw-IR commands. No bootstrap, C hash shim, or skipped
font validation was used.

The first full run with those providers correctly rejected scene revision
zero. The demo now submits `render_revision + 1`, preserving the producer's
fail-closed revision rule. Its next native fault was a corrupted nested
`HostCompositor.content_target()` receiver in the GUI router. The operational
router now performs the small scalar hit-test inline, and the focused native
pointer-capture probe exits cleanly.

The next backtrace appeared to enter `WidgetStore.set_prop()` from `spl_main`,
even though the demo has no source call to that method. Disassembly resolved
the mismatch: every chained `tree.find_widget(...).set_prop(...)` returned an
aggregate `WidgetNode?`, then compiled the call as:

```text
UITree.find_widget()
  -> WidgetStore.set_prop()  # wrong receiver/method
```

The demo now constructs `WidgetNode(id: ...)` directly for its five stable
controls. The exact demo-tree native probe passes property mutation/readback
and Draw-IR generation, while rebuilt `spl_main` references only
`WidgetNode.set_prop()`.

A direct no-timeout run mapped a real 640x600 X11 window. Two native ABI
defects were then isolated at the GLFW boundary:

```text
Simple text header -> const char*       # title appeared as RTS\x01
packed uint32_t pixels -> int64_t words # 8-byte stride over 4-byte allocation
```

`SimpleGlfw.create_window()` now uses the existing `spl_str_ptr()` bridge. The
raw presenter now accepts four-byte alignment and copies `uint32_t` pixels. Its
live C probe deliberately presents a four-byte-aligned/non-eight-byte-aligned
buffer and passes:

```text
glfw_live_probe=pass packed_argb32=1 frames=2
native_input=key,text,pointer,button
capture: 96x64 colors=2 mean=0.366013 min=8224 max=53456
sha256=ee82698fd31521729756cd3f7dcf6fe3a4c3dcc73290deb87aa431871463addb
```

The rebuilt full demo is now discoverable by the exact
`Simple Full Stack WM Demo` title. Its first 640x600 capture remains entirely
black (`colors=1`, `mean=0`, SHA-256
`0b56d6bd870958ec99fb98026aa09e576e046046c5815efe02d39c9f8d393cc1`),
and a bounded live run next faults in `rt_to_string()` before the post-input
capture. The next target is compositor pixel population/native string
conversion, not the independently green GLFW raw copier. This checkpoint does
not claim a non-black full-WM frame, semantic input mutation, or clean
outer-window close evidence.

The next bounded native probe found two pre-paint uses of the generic tagged
formatter:

```text
SharedMdiRenderWindow.id interpolation -> rt_to_string()
external frame -> unused Simple Web revision -> theme manifest -> rt_to_string()
```

Operational numeric window-ID projections now reuse
`rt_raw_i64_to_string()`, which already exists in both native runtimes. The
external-content branch now skips the unused Simple Web revision entirely.
The third focused probe reached the compositor buffer and matched exact pixel
`0xff112233`; return 6 was a probe error because its input split colors by row
while it sampled by column. The pattern is corrected to split by column, but
the probe was not rerun after the repository's three-cycle cap.

One rebuilt full-demo live attempt still mapped the exact titled X11 window
and then faulted before the two-second capture. Therefore the remaining
blocker is in the richer GUI/demo route. This checkpoint proves neither the
final corrected probe assertion nor a live non-black GUI frame, semantic input
mutation, or clean close.

The first-frame probe was then upgraded from a synthetic PixelSurface to the
exact demo widget tree, `UISession`, canonical GUI frame producer, compositor
admission, and raw pixel readback. Its three bounded Phase-3 cycles exposed the
same generic numeric-format defect at progressively later owners:

```text
common.ui.builder.with_height()
nogc_sync_mut.ui.session._ui_draw_ir_session_nonce()
nogc_sync_mut.ui.session.UISession.dispatch()
common.ui.event.process_event()  # remaining, viewport tokens at lines 66-67
```

`common.ui.native_scalar_text` now owns the existing native raw-i64 formatter.
Builder dimensions, RenderSurface scalar properties, UISession identities and
selected event receipts, and WM numeric identities route through it. This
removes the demo/compositor/MDI raw-runtime declarations rather than spreading
another workaround.

The third probe build completed with 3 compiled and 377 cached modules, then
exited 139. GDB identifies the remaining first formatter call as:

```text
rt_to_string
  <- common.ui.event.process_event
  <- common.ui.state.update_state
  <- UISession.dispatch
```

Per the three-cycle guard, `event.spl:66-67` is recorded for the next bounded
turn and was not fixed/rebuilt here. The full GLFW demo was not retried behind
this red focused gate.

The next bounded turn routed the Resize token dimensions through the existing
native scalar-text owner. The exact GUI probe then advanced through two theme
owners:

```text
theme_package._source_manifest_sha256()  # path.len()
theme_package._split_top_level_commas()  # text-only current/ch interpolation
```

The path length now uses `ui_native_i64_text()`. The sibling CSS argument and
shadow splitters now use direct `text + text` concatenation instead of invoking
the generic formatter for each character.

All three incremental Phase-3 builds linked successfully. The final receipt was
3 compiled and 377 cached modules, followed by exit 139. Its remaining first
call is:

```text
rt_to_string
  <- common.ui.theme_render_snapshot.normalized_theme_material_text
  <- common.ui.theme_render_snapshot.theme_material_sha256
  <- nogc_sync_mut.ui.theme_package.load_theme_package
  <- UISession.submit_widget_draw_ir
```

`normalized_theme_material_text()` still serializes many `u32`, `i32`, boolean,
and shadow-index fields through interpolation. It is the exact next owner; no
layout-aggregate fix or live GLFW retry is justified before this focused gate
passes.
