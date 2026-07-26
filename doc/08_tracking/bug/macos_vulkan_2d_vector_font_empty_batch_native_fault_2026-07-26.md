# macOS Vulkan 2D vector-font empty-batch native fault

Status: open, live evidence blocked

## Scope

The manifest-attested macOS Vulkan 2D binary built successfully at pushed
revision `24345dfc8c83` (207/207 modules, zero compile failures). The live
wrapper re-admitted the trusted manifest after the report-order fix, launched
the exact binary, and then failed closed because the process exited before
publishing its ready or runtime receipt.

## Reproduced evidence

- Live result: `launched-process-missing`.
- Exact process stderr: `runtime error: field access on nil receiver`.
- A direct run of the same trusted binary also printed the nil-receiver error
  before producing a receipt. The retained diagnostic does not bind a signal
  exit code.
- A minimal native Vulkan diagnostic reached backend creation, font loading,
  selected Bungee identity, two `draw_text` calls, and renderer installation;
  those calls recorded zero rasterizations.
- `Engine2D.font_execution_attempts()` and
  `Engine2D.font_execution_target()` are declared with `fn` while reading
  `self`; changing them to receiver methods (`me`) removes that nil-receiver
  trap.
- One native diagnostic recorded `engine.font_owner.active.len() == 1` and
  then trapped while accessing the element receiver. In a separate run,
  `engine.fonts()` returned a renderer with the selected TTF identity.
- Routing the selected Vulkan backend as the concrete default font execution
  target entered canonical vector staging, but emitted:

  ```text
  [font-batch] degenerate source=text content=6 quads=0 atlas_pixels=1048576 \
  identity=sha256=c4f5361ce120af3e6b9156d0bf379fa19cda2ea0cd18ac01fd99596c6bf66e3f;axes=static \
  generation=1
  ```

  The retained output did not reach the post-cold-draw marker.

## Interpretation

The diagnostic selected backend name `vulkan`, but it does not independently
prove MoltenVK/provider health, backend font dispatch, or device readback. The
receipt occurs after `fonts.stage_text_configured()` and before batch
consumption, so it proves that an empty staged quad list is observed
pre-dispatch despite a non-empty atlas-pixel array. The precise producer fault remains to
be isolated. The path is not fail-closed, preventing valid cold/warm cache,
Vulkan font execution, device-readback, 300-DPI capture, and event evidence.

The isolated changes used to diagnose the receiver and target routing are not
accepted implementation evidence because the final native probe still faults
and does not reach the post-cold-draw marker. They must not be merged as a
completed fix.

## Required acceptance gate

1. A focused native producer probe must use an exact non-empty Bungee string
   at 24 pt / 300 DPI and prove computed font size 100 px, `valid=true`,
   positive quad count, consistent atlas dimensions/pixel count, in-bounds
   nontransparent quad coverage, and matching renderer identity/generation.
2. An empty or inconsistent `FontRenderBatch` must return a named failure
   propagated to the caller, without dereferencing a nil aggregate, with
   evidence that no backend batch method was entered.
3. `Engine2D.draw_text` must retain the selected renderer and record ordered
   Vulkan execution attempts plus target, prove Vulkan success with no CPU
   fallback, and avoid a native receiver fault while retrieving the selected
   renderer.
4. Cold draw must increment rasterizations; warm draw must keep
   rasterizations stable and increment warm hits.
5. Vulkan device readback after text must prove source `device_readback`, a
   positive backend handle, exact framebuffer pixel count, and a text-only
   region-of-interest pre/post delta.
6. Only after those focused native checks pass may the immutable trusted
   harness be rebuilt and the full live capture/event gate retried.

No additional bootstrap is justified until an accepted source fix requires a
new immutable trusted binary.
