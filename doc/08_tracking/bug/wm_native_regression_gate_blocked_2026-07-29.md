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

The next bounded turn replaced those generic interpolations with direct text
concatenation, the existing native scalar-text owner, and explicit lowercase
booleans. The exact GUI producer probe then completed theme loading without a
fault. Split frame diagnostics show:

```text
frame.width == 100
frame.height == 60
frame.pixels.len() != 6000  # exit 33
```

The first two builds compiled 3/377 and 2/378 changed/cached modules. A third
build compiled 3 and reused 377. Reading pixels directly from the concrete
`Engine2D` owner produced the same exit `33`, so that ineffective experiment
was reverted. The remaining gate is the native aggregate/trait pixel-return
boundary in the Draw IR renderer. Per the three-cycle cap, no further repair,
live GLFW rebuild, or presentation claim was attempted in this turn.

That pixel-boundary conclusion was subsequently disproven. The demo widget
tree emits an image command for `wm-demo://image`, but the focused probe passed
an empty resolved-image list. Draw IR therefore reported a skipped command and
the GUI adapter deliberately emitted an empty fail-closed frame. With the same
2x2 image supplied by the production demo, the focused cached Phase-3 build
compiled 2 modules, reused 378, and exits `0`. It proves a 100x60/6000-pixel
GUI frame, nonzero checksum, external-frame admission, and exact raw compositor
pixel `0xff0e0e10`. The earlier direct-read experiment was inconclusive because
the combined fallback/skip guard discarded its pixels; it remains reverted.

The next fresh full-demo build reached a different generic formatter call:

```text
rt_to_string
  <- ui.web.html_css.responsive_css
  <- ui.web.html_css.generate_package_authoritative_css
  <- HostTaskbarRuntime._default_pinned
```

`responsive_css()` now uses direct concatenation and the existing native scalar
owner for breakpoint values. The rebuilt binary compiled 3 modules and reused
511. On Xvfb `:77`, the exact titled GLFW window captured at 640x600 with 138
colors and SHA-256
`43ef5a5e3047c2064b5419c3ae9ec837995dd36a8de3a229ad72b6c0214c45c8`
(`/tmp/wm_full_stack_demo_v4.png`). This is the first current non-black
full-demo capture. It visibly shows WM chrome, client content, and taskbar, but
the widget layout is collapsed/overlapping. Sending native `windowclose`
removes the X11 window while the demo loop remains alive, so clean event-driven
shutdown is still unproven and the process was stopped with Ctrl-C.

The next bounded layout probe made that visual failure executable. For the
exact demo tree at 480x480, the initial oracle asserted `demo-button.y=90` and
`demo-status.y=374`. Both IDs survive `compute_layout()`, but the Phase-3
binary exits `23` because the returned button Y is corrupt. Three cycles
distinguished the boundary:

```text
cycle 1: direct returned WidgetRect geometry -> grouped exit 21
cycle 2: post-return scalar snapshot -> grouped exit 21
cycle 3: split identity/geometry diagnostics -> exit 23 (button Y)
```

The attempted post-return snapshot and renderer accessors were removed because
they cannot repair geometry already corrupted by the aggregate-array return.
The retained regression now fails before the previously green frame checks.
The next repair must write scalar geometry during layout traversal, before
recursive or top-level `WidgetRect[]` returns.

The parallel close audit confirmed that runtime GLFW already enqueues close
callbacks and exposes `rt_glfw_should_close()`, while the demo consumed only
queued events. It now also checks `SimpleGlfw.should_close(host_window)` after
polling. The cached full build compiled 2 modules and reused 512. Xvfb `:77`
runs without a window manager, so `xdotool windowclose` directly removes the
surface without setting the GLFW close flag; the unchanged process remains
alive. This is invalid close-request certification rather than proof that the
fallback is wrong. A real WM_DELETE_WINDOW host smoke remains required.

The next bounded experiment moved scalar geometry capture into
`_compute_layout()` immediately after its scalar `sx/sy/sw/sh` calculation and
before recursion. Parallel small-model review confirmed that this traversal is
preorder and aligns with the surviving returned ID order. Results:

```text
cycle 1: i32 raw scalar store, 4 compiled / 376 cached -> exit 23
cycle 2: diagnostic build, 2 compiled / 378 cached -> stored button Y = 1
cycle 3: i64 raw scalar store, 3 compiled / 377 cached -> exit 23
```

The production experiment was reverted because it did not improve the gate.
This disproves the narrower theory that only aggregate-array return transport
corrupts geometry. The next investigation must isolate scalar argument
evaluation at the VBox-to-recursive-call boundary before attempting another
renderer or live-window change.

That isolation found the root container is a bordered Panel. Its inner origin
is `(1,1)`, so the correct button/status Y oracle is `91/375`; the regression
was corrected. The observed native button Y of `1` therefore identifies the
failure more precisely: VBox places every child at the unchanged inner origin
because `cur_y` does not survive the call-bearing child loop.

A fresh existing pure-Simple Stage-2 binary reproduced exit `23`. Converting
only the VBox measurement and placement loops from `for` to indexed `while`
also reproduced exit `23`, consistent with the known cross-block scalar spill
family rather than a `for`-specific lowering bug; that workaround was reverted.
A scoped compiler refresh was then attempted with the existing Stage-2 binary,
the persistent cache, and `SIMPLE_NO_STUB_FALLBACK=1`—not a bootstrap. It
failed before producing an executable:

```text
GlobalFlags.mem_infra_requested: cannot infer field type
SdnValue.empty: unknown enum variant or method
ANY.is_empty: cannot infer field type
```

Per the three-cycle cap, no raw coordinate stack or live GLFW rebuild was
attempted in this turn. The next convergent lane is one of those three
compiler-entry lowering failures, after which the source-fixed scalar-spill
compiler can rerun the unchanged WM oracle.

Those three failures were source defects and are now repaired:

```text
GlobalFlags: declare and parse --mem-infra / --mem-infra-strict
SdnBackend: emit direct scalar SdnValue.Null
coverage threshold: compare typed text with ""
```

The first cached rebuild cleared the GlobalFlags and coverage errors, then
showed that Stage-2 cannot resolve even the valid `SdnValue.null()` static enum
helper; the direct `SdnValue.Null` variant cleared it. Two subsequent
cache-preserving builds compiled the full compiler closure and reached link.
Both then failed because this Stage-2 native-build driver selects the
intentionally minimal `core-c-bootstrap` runtime lane even when the bundle
option is omitted. The closure needs hosted/compiler primitives including
`rt_index_of`, `rt_cranelift_*`, `rt_file_stat`, and coverage/process helpers.
No stub fallback was allowed.

The WM remains blocked on producing a source-current pure-Simple compiler
artifact, but the blocker has moved from HIR/MIR source compilation to the
runtime-provider/link contract. No layout-specific workaround was added.

The runtime-provider audit then found the supported smaller route:

```text
admitted Stage-2
  native-build
  positional src/app/cli/bootstrap_main.spl
  core-c-bootstrap
  --runtime-path <stage2-runtime-authority>
```

That route lets the native builder project the required runtime symbols and
attach `libsimple_compiler_backfill.a`; direct `libsimple_native_all.a`
injection is intentionally unsupported. The focused build was run with its own
cache and no stub fallback. After 10m42s at ~100% CPU it still had zero object
files. A separate identical canonical build already running in the shared
workspace was 7h45m old at ~99% CPU. This is the known pre-object runaway
signature, not useful compilation progress, so the scoped process was stopped
with exit `130` and its cache retained.

The next WM turn should not repeat that unchanged compiler command. The
shortest remaining route is a native-safe layout cursor owner that does not
depend on cross-block local scalar reloads, or an independently refreshed
compiler artifact after the pre-object closure defect is fixed.

A bounded raw cursor owner was then tested directly in `layout_vbox`. It used
one i64 recursion-stack record per VBox depth, advanced the parent record
before recursion, and packed child Y/height together to avoid aggregate
returns and multi-call scalar transport. The exact stale-Phase-3 results were:

```text
cycle 1: 8 compiled / 372 cached -> exit 23
cycle 2: 3 compiled / 377 cached -> exit 28
cycle 3: 2 compiled / 378 cached -> exit 28
```

Exit `28` means the root raw slot itself did not contain final status Y `375`.
The third probe also ruled out every expected row origin
`1/25/61/91/123/195/285`; corruption occurs before the raw cursor can become
authoritative, not only at recursive argument or `WidgetRect[]` return
boundaries. The stack and diagnostic hooks were reverted. The retained oracle
does keep one independent correction: a bordered 480-wide Panel has a
478-wide client row, so `demo-button.w` must be `478`, not `480`.

## 2026-07-30 source repair checkpoint

A separate source audit found a pre-runtime native regression:
`14ed678bc8` replaced the typed, native-safe theme material serializer accepted
in `892e467f74` with generic interpolation. The scoped repair restores the
wire-compatible typed serializer and also projects exact semantic colors from
the installed Aetheric package CSS into `ThemePackage`. Discriminating unit
assertions and highest-capability source review accept this repair.

This does not clear the native gate. The released runtime remains stale and an
external source-matched incremental build is unresolved, so no fresh host
capture or runtime PASS is claimed. CPU/SIMD/Vulkan glass, Web ordered-shadow
fidelity, and x86/ARM QEMU evidence remain separate follow-ups.

The CPU/SIMD/Vulkan source follow-up is now accepted: those concrete targets
request bounded CPU-composited glass while keeping opaque fail-closed command
pixels; Metal alone requests device glass and Engine2D alone records execution.
This still does not clear the native gate because no current source-matched
runtime or capture has verified the path.
