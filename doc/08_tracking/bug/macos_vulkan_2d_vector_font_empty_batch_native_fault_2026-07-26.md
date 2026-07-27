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

### 2026-07-27 bounded no-bootstrap diagnostics

Three focused current-source native-build cycles were run without bootstrapping:

- Cycle 1 compiled 185 modules with zero compile failures in approximately
  9.9 seconds, but the diagnostic process produced empty standard output.
- Cycle 2 compiled 184 modules in 10.2 seconds. Its entry and receipt sentinels
  succeeded and it selected the exact Bungee face at a computed 100 px size.
  However, the layout, raster, local, inbound, staged, stage-return, and alpha
  scalar checkpoints all serialized as empty values.
- In the same cycle, `post_engine_fonts` and `post_install_retrieve` serialized
  as the nil sentinel `2305843009213693951` (`0x1fffffffffffffff`).
- The third and final bounded cycle started from
  `bb9a9b60edcc572e86555e8c929bfabc20b74a62`. Its scalar-only diagnostic
  explicitly initialized every checkpoint and exposed individual `i64`
  getters directly from the live `Engine2D` font owner. The no-bootstrap
  native build compiled 184 modules with zero failures and linked a 654 KB
  binary with SHA-256
  `8460a54790068788b5c4997b59ad0d04ed73e863f5d281a48f7d34a7f3f1164a`.
  The run exited 132 with `runtime error: field access on nil receiver` before
  producing any checkpoint output.
- All third-cycle diagnostic source and probe edits were reverted after that
  failure. The three-cycle cap is exhausted: no retry, bootstrap, renderer
  change, or Vulkan live gate is permitted in this session.

These facts are summarized here because the diagnostic directory
`/private/tmp/simple-font-zero-quads-evidence-448d2a5` is ephemeral. It is not
a retained, manifest-bound evidence artifact and must not be cited as live
acceptance provenance.

The third-cycle binary is an ephemeral diagnostic product. Its hash identifies
the exact failed executable, but it has no trusted manifest binding and is not
Vulkan live evidence.

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

The 2026-07-27 diagnostics also do not prove where the zero-quad state is
introduced. The leading seam remains the transfer from locally produced quads
through `FontRenderBatch.quads` into `_stage_batch`, but a layout or raster
producer failure is still a viable alternative. Empty scalar serialization and
nil-sentinel renderer retrieval make the diagnostic transport itself
untrustworthy. No renderer fix, live PASS, or bootstrap resulted from these
cycles.

The third cycle confirms that adding more scalar fields/getters on the current
owner path is not a trustworthy next diagnostic step: the process still
reaches a native nil-receiver fault before an observable checkpoint. It does
not localize layout, rasterization, quad construction, or staging. In a fresh
session, first localize and fix the aggregate/owner nil-receiver channel using
the existing tracked aggregate-return bug evidence. Only then retry the
focused font producer checkpoint.

## Required acceptance gate

1. In a fresh session, localize and fix the aggregate/owner nil-receiver
   channel using the tracked native aggregate-return evidence; do not add
   another scalar checkpoint on the same untrusted owner path.
2. Establish at least one typed scalar checkpoint through the repaired channel
   that cannot serialize a present value as empty or confuse it with the nil
   sentinel. Use it to distinguish layout/raster production from the
   `local quads -> FontRenderBatch.quads -> _stage_batch` transfer seam.
3. A focused native producer probe must use an exact non-empty Bungee string
   at 24 pt / 300 DPI and prove computed font size 100 px, `valid=true`,
   positive quad count, consistent atlas dimensions/pixel count, in-bounds
   nontransparent quad coverage, and matching renderer identity/generation.
4. An empty or inconsistent `FontRenderBatch` must return a named failure
   propagated to the caller, without dereferencing a nil aggregate, with
   evidence that no backend batch method was entered.
5. `Engine2D.draw_text` must retain the selected renderer and record ordered
   Vulkan execution attempts plus target, prove Vulkan success with no CPU
   fallback, and avoid a native receiver fault while retrieving the selected
   renderer.
6. Cold draw must increment rasterizations; warm draw must keep
   rasterizations stable and increment warm hits.
7. Vulkan device readback after text must prove source `device_readback`, a
   positive backend handle, exact framebuffer pixel count, and a text-only
   region-of-interest pre/post delta.
8. Only after those focused native checks pass may the immutable trusted
   harness be rebuilt and the full live capture/event gate retried.

Bootstrap is permitted only if it is essential after the focused producer
passes and a new immutable trusted binary is required.
