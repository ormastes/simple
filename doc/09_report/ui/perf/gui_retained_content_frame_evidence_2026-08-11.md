# GUI retained content-frame evidence — 2026-08-11

Status: IMPLEMENTED; focused damage-classifier spec PASS; GUI integration is
pending Stage-4 self-hosted execution.

The production `gui_session_content_frame` path now retains one exact rendered
GUI content revision. A hit keyed by window id, dimensions, and authoritative
content revision returns the retained pixels/checksum while preserving current
scene revision, parent, and offsets. It skips widget DrawIR submission,
Engine2D construction, clear, raster, readback, shutdown, and checksum scan.

The cache retains up to eight ordinary visible GUI windows without
alternating-window thrash, but admission is additionally bounded by an exact
33,177,600-pixel global budget (one 7680x4320 ARGB surface). LRU eviction
retires the cached pixel payload and composition; resizing immediately
retires the stale-size entry. An entry larger than the budget is returned
for the current frame but is not retained. This prevents the nominal
eight-entry cap from retaining more than 1 GiB of 8K pixel payloads.
For a revision change on the same window and dimensions, the cache retains the
prior canonical `DrawIrComposition` and validated CPU pixels. A LOCAL decision
seeds a fresh CPU Engine2D target from those pixels, then invokes the shared
DrawIR damage executor with the exact canonical plan. This proves the GUI
consumer uses the same clipping/fallback semantics as the DrawIR and WM
consumers; it does **not** claim a persistent target or an 8K improvement,
because the seed copy and final readback are still full-frame. A dimension or
window change takes FULL. Cache clear owns only retained payloads, not a live
Engine2D target.

The damage classifier now fails closed for multi-batch compositions. Its patch
carrier deliberately reconstructs one batch, so flattening a multi-batch scene
could silently lose embedding/clip/layer semantics while passing a
flattened-command comparison. Such scenes receive FULL with
`multi-batch-patch-replay-unsupported` until batch-preserving patch replay is
implemented.

Verification:

- `bin/simple check src/lib/gc_async_mut/ui/gui_content_renderer.spl`: PASS
  under the available Rust seed; diagnostic only, not Stage-4 evidence.
- `test/01_unit/lib/common/ui/render_opt/composition_damage_spec.spl`: 6/6
  PASS under that same seed, including the multi-batch fail-closed regression.
- `test/01_unit/lib/gc_async_mut/ui/gui_content_renderer_spec.spl`: PASS,
  2 examples / 0 failures (54.398 seconds). It proves a fresh FULL frame,
  exact revision NONE reuse, and a changed revision whose identical canonical
  command stream produces a verified empty patch/NONE replay.
- `gui_content_renderer_dynamic_damage_spec.spl` now checks the LOCAL replay
  counter and pixel equality against an independently full-rasterized GUI
  surface. It cannot execute on the available seed: the seed parser rejects
  the already-present GUI module with `Unexpected token: expected pattern,
  found Use` before any example runs. Resume with the admitted Stage-4 CLI;
  this is a compiler-authority blocker, not a pass.

This proves static cache ownership and conservative plan classification. Exact
NONE reuse removes settled producer/raster work. The current WM content-frame
boundary still requests a complete pixel array after a non-cache render.
However, the software target remains transient. The current WM content-frame
boundary still requests a complete pixel array after every non-cache render;
the GUI lane must retain a live target before local replay can remove the seed
copy/readback from the hot path.

The dedicated 8K timing benchmark is
`test/perf/graphics_2d/bench_damage_checksum_8k.spl`. It could not produce a
timing row: the deployed self-hosted binary again lacks
`rt_struct_receiver_valid`, and interpreter fallback exceeded both the 60s
default guard and one bounded 240s retry during the 8K run. Therefore dynamic
8K/80 remains unproven; this is not a performance pass. Physical GPU behavior
is also unproven. GUI continues to emit canonical `DrawIrComposition`; no
nominal GuiIR exists.

The cache-budget structural gate passes 2/2. The optimizer reports 62
opportunities, predominantly bounds-check elimination and loop-invariant
motion; these are compiler opportunities rather than applied or measured
speedups. The multi-window behavioral spec now pins the exact retained pixel
count, but its large dependency runner has not been re-admitted, so the new
memory policy is not yet an RSS measurement or 8K/80 proof.
