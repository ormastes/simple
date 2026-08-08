# Web Draw IR Route Key SDN Overhead

## Status

Synthetic serializer cost measured; end-to-end route evidence remains open.
Production remains on the exact canonical SDN key.

## Evidence

`web_draw_ir_route_key_cost_spec.spl` directly serializes synthetic Draw IR,
using three samples after three warmups for 64, 256, and 1024 rectangle
commands. It asserts stable encoded sizes and positive timings. This isolates
serializer cost but does not execute the production route. On the incremental
Rust development interpreter, median canonical SDN serialization was:

| Commands | SDN bytes | Initial median | Review median | Final median |
|---:|---:|---:|---:|---:|
| 64 | 30,571 | 345,428 us | 305,251 us | 317,359 us |
| 256 | 121,514 | 1,312,451 us | 1,207,284 us | 1,269,513 us |
| 1024 | 485,835 | 5,307,734 us | 4,820,833 us | 4,937,136 us |

These development measurements size the suspected cost; they are not admitted
completion evidence. The pure-Simple wrapper receipt remains host-blocked.

## Actual Boundary

The traced producer is `SimpleWebRenderSession.render` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_render_session.spl`; it
retains the canonical `SimpleWebLayoutDrawIrResult` produced by
`simple_web_html_layout_renderer`. Its `composition_checksum()` calls
`draw_ir_to_sdn(result.composition)` before hashing. The traced consumer is
`Engine2dCompositorBackend.render_draw_ir_composition_resources_revision` in
`src/os/compositor/compositor_engine2d.spl`; it already admits a producer and
composition revision tuple, but still verifies a cache hit with exact
composition equality. The benchmark does not enter these producer/consumer
functions; it measures only their shared serializer cost. No GPU runtime or
compiler backend is changed by this lane.

The repeatable receipt entrypoint is
`sh scripts/check/check-web-draw-ir-route-key-sdn-overhead.shs`. It runs the
existing benchmark with an admitted pure-Simple interpreter, rejects the Rust
bootstrap seed, validates the printed medians and encoded sizes, and writes
`build/web-draw-ir-route-key-sdn-overhead/evidence.env`. It admits only
canonical release/stage3 deployment paths, rejects seed-identifying binaries,
and requires exactly one benchmark receipt. A missing or forbidden binary exits
125 and records `status=unavailable`; it never bootstraps.

## Rejected Attempt

A full structural dual fingerprint preserved every serialized Draw IR field.
The first portable byte encoder timed out after 180 seconds on a two-command
unit. A reduced code-point encoder also timed out after 180 seconds. A runtime
`text_hash` variant was rejected because that symbol is not available through
the current Simple surface. Production source was restored after the
three-cycle cap.

## Required Fix

Add an opaque producer-owned revision to `SimpleWebLayoutDrawIrResult`, sourced
from `SimpleWebRenderSession`'s retained composition revision. It must cover
document/style revisions, viewport width and height, resolved font and registry
generation, render configuration, asset root, render-budget state, and ordered
composition semantics. Use a session-owned route cache or key the process-local
cache by exact session identity plus composition revision; a session-local
revision alone is not globally unique. Never cache degraded or partial output. Standalone,
animated, scrolled, overlay, or image-backed callers must retain exact SDN
keying or disable reuse until they have an owner-scoped revision. Do not replace
exact identity with a probabilistic composition fingerprint.

Acceptance evidence:

- identical revision avoids SDN serialization on repeated frames;
- any HTML, viewport, font/style revision, backend, or transfer-mode change
  misses the cache;
- output parity and device provenance remain unchanged;
- paired same-host/runtime before/after runs show lower 64/256/1024 command
  median lookup time;
- CUDA live route calibration/reuse still passes; Metal repeats on the prepared
  macOS host under TODO 588.
