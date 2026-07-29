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

A direct no-timeout run remains alive and maps a real 640x600 X11 window. The
native title is corrupt (`RTS\x01`), explaining why name-based capture polling
reported no window. Capturing by the mapped X11 ID succeeds, but both the
initial image and the image after native pointer plus Ctrl+A injection are
entirely black:

```text
colors=1 mean=0 min=0 max=0 changed_pixels=0
sha256=0b56d6bd870958ec99fb98026aa09e576e046046c5815efe02d39c9f8d393cc1
```

The next bounded target is the raw compositor pixel-buffer/presentation
boundary, plus the independent native title-text ABI. This checkpoint does not
claim a non-black full-WM frame, semantic input mutation, or clean outer-window
close evidence.
