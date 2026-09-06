# Six engine2d showcase fixture painters were never implemented; their specs assert an unpainted surface

Date: 2026-09-06
Status: OPEN
Area: lib / gc_async_mut / gpu / browser_engine

## Symptom

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl`
reports 14 passed / 7 failed. Six of the seven are exact-pixel fixture scenarios:

| scenario | reported assertion |
|---|---|
| renders dashboard command list fixture with exact chart and list colors | `expected 4278915616 to equal 4279286145` (`0xFF0B1220` vs `0xFF10B981`) |
| renders form sidebar validation fixture with exact navigation and validation colors | `expected 4278849306 to equal 4287323382` (`0xFF0A0F1A` vs `0xFF8B5CF6`) |
| renders settings inspector tree fixture with exact tree and inspector colors | `expected 4278915104 to equal 4293870660` (`0xFF0B1020` vs `0xFFEF4444`) |
| renders media gallery command fixture with exact image grid and taskbar colors | `expected 4279179050 to equal 4293870660` (`0xFF0F172A` vs `0xFFEF4444`) |
| renders report table command fixture with exact table and command colors | `expected 4294507260 to equal 4286331629` (`0xFFF8FAFC` vs `0xFF7C3AED`) |
| renders split pane status list fixture with exact status colors | `expected 4294967295 to equal 4282090230` (`0xFFFFFFFF` vs `0xFF3B82F6`) |

In every row the ACTUAL value is exactly the fixture's own `background-color`
(white for the split-pane fixture, which declares none). The reported line is
only the last assertion of each scenario; **every** color assertion in these six
scenarios is wrong, not just the reported one.

## Mechanism

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl:1140-1141`
dispatches exactly one showcase fixture marker to a dedicated painter:

```
    if html.contains("simple-web-engine2d-toolbar-modal-grid"):
        return _toolbar_modal_grid_pixels(width, height)
```

`_toolbar_modal_grid_pixels` is defined at
`simple_web_engine2d_renderer.spl:1071`. It is the ONLY fixture painter in the
tree — `grep -rn` over `src/` and `test/` for the other six marker classes
(`simple-web-engine2d-dashboard-command-list`, `-form-sidebar-validation`,
`-settings-inspector-tree`, `-media-gallery-command`, `-report-table-command`,
`-split-pane-status-list`) finds hits only in spec files, never in `src/`.

Lacking a marker branch, those six documents fall through the dispatch: they
contain no `<p>/<h1>/<span>/...` tag, no `display:contents`, no `wm-app-*`
class, and no class/id style block, so `_first_block_color` is 0 and
`heuristic_recognized` is true via `bg != white`, reaching
`simple_web_engine2d_renderer.spl:1172` — `_solid_fill_pixels(width, height, bg)`.
The result is a uniform background fill.

## Evidence

Direct probe of the rendered surface at the exact asserted indices
(`SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple run`):

```
dashboard len=6144
  idx=0    -> 4278915616   (0xFF0B1220, spec expects 0xFF111827)
  idx=196  -> 4278915616   (spec expects 0xFF22C55E)
  idx=1752 -> 4278915616   (spec expects 0xFF22C55E)
  idx=1786 -> 4278915616   (spec expects 0xFFCBD5E1)
  idx=5636 -> 4278915616   (spec expects 0xFF10B981)
splitpane len=6144
  idx=0,771,2115,3459,12,1786,4090 -> 4294967295 (white)
  idx=2938 -> 4278190080 (black)
toolbar len=6144
  idx=0    -> 4280562759   (0xFF243447, matches spec)
  idx=196  -> 4280468830
  idx=1748 -> 4293870660
  idx=2550 -> 4291548641
  idx=5574 -> 4287323382
```

The toolbar fixture — the one with a painter — produces the distinct colors its
scenario asserts. The other six produce a single flat color at every index.

## Classification

This is NOT stale expected colors and NOT a backend defect. The six scenarios
describe fixture painters that were never written; the expectations are a
specification of unimplemented behavior. Pre-existing: reproduced identically at
the untouched commit `e0432cd7be29668138a4c47bf270cb5243ead8e4`.

## Fix location (outside the reporting lane's ownership)

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl` —
either add the six painters alongside `_toolbar_modal_grid_pixels` (:1071), or
route the six markers to the real layout renderer and rewrite the fixtures'
expectations from that engine's output under review. Do not adjust the spec's
expected colors to match `_solid_fill_pixels`; that would be oracle-gaming.

## Separate, unrelated seventh failure

`preserves backend_name for generic layout dispatch while keeping pixels stable`
failed with `expected software to equal opencl`. That is host-dependent, not a
defect: `simple_web_engine2d_resolved_backend_name`
(`simple_web_engine2d_renderer.spl:1234-1252`) probes the requested backend via
`Engine2D.probe_backend` and falls back to `"software"` when it does not
initialize, which is its documented contract. `backend_probe.spl:214` is a
strict probe and reports the failure faithfully. On this host `opencl`, `metal`,
`cuda` and `opengl` do not initialize while `vulkan`, `software` and `cpu` do.
Fixed in the spec by asserting the resolver contract (`opencl` or the documented
`software` fallback) instead of a backend the host may not provide.
