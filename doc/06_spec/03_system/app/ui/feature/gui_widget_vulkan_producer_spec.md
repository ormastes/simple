# GUI widget input and visible evidence

Executable source: `test/03_system/app/ui/feature/gui_widget_vulkan_producer_spec.spl`

Trace: REQ-2D-006, NFR-2D-002

Run from the repository root with a verified pure-Simple self-hosted runtime:
`<runtime> test test/03_system/app/ui/feature/gui_widget_vulkan_producer_spec.spl --mode=interpreter`.
The available macOS binaries in this checkout are bootstrap seeds or fail
before this scenario compiles while parsing unrelated
`src/lib/nogc_sync_mut/io/process_ops.spl`.

## Scenario: visible text input interaction

1. Build the pinned `qualification-text-input` widget at 160 × 40 with a
   visible `Type` placeholder. Require GUI source and component IDs in the
   actual GPU-targeted `widget_tree_to_draw_ir` output.
2. Click `(10, 10)` through `widget_dispatch_click`, require focus on that
   input, then deliver `A`, `B`, `left`, and `C` through
   `widget_dispatch_key`. Require committed visible text `ACB` and caret
   character index 2.
3. Require the bundled Noto Sans Mono byte digest and resolved font identity
   to match the fixture pin, with positive advances and complete glyph arrays
   for both text commands. Require the
   after-state caret to be a 2-pixel rectangle inside the field at the
   producer's declared y position. Require distinct DrawIR hashes and save
   both SDN documents with `build/test-artifacts/simple_2d/gui_text_input.sdn`.
4. The receipt records source input identity, resolved font identity/family and
   bundled font SHA-256,
   caret rectangle, and explicit blocked physical
   Engine2D and upstream Skia Vulkan statuses. It does not claim device
   pixels, font parity, or live-window event delivery.

## Scenario: pointer event changes a button

1. Build a real GUI button, lower its DrawIR to accepted `UiIr`, and render
   its resting DrawIR through CPU Engine2D.
2. Deliver a pointer press and click at `(10, 10)` through the widget hit
   dispatcher. Require the button ID and its `ui_action_pending` state.
3. Lower the pressed state to `UiIr`, render it, and require a changed DrawIR
   fill and at least one changed CPU pixel. Match the exact button-fill color
   in the CPU and GPU-targeted DrawIR for both states. Release the button and
   require the original fill in both producers.
4. Serialize the actual GPU-targeted DrawIR for both widget states, require
   distinct SHA-256 digests, and retain both SDN inputs beside the resting and
   pressed CPU PPM frames. Write
   `build/test-artifacts/simple_2d/gui_widget_input.sdn` with those input
   digests, widget state, CPU/GPU button-fill colors, CPU pixel-change count,
   and explicit blocked
   statuses for the two Vulkan backends and physical-device qualification.

The CPU pixel observation is a local GUI producer witness. It is not a Vulkan
comparison or an admitted physical Linux capture.

## Scenario: rectangle-only GUI preflight

Build an unlabeled button so its full-surface fill is the only GPU-targeted
DrawIR command. Require upstream Skia's strict rectangle preflight to admit
both resting and pressed states, require their fill colors to differ, and
require release to restore the resting color. This proves that real widget
input can reach the current rectangle-only provider contract. The labeled
button, glyph rendering, and completed GPU pixels remain separate open gates.
