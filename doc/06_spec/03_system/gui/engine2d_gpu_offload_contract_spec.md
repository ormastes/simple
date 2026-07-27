# Engine2d Gpu Offload Contract Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Gpu Offload Contract Specification

## Scenarios

### GPU offload wiring contract (showcase + WM compositor)

#### keeps CPU as the showcase default lane and honors --backend/env selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(SHOWCASE_SRC)
# default is software when no flag/env is set
expect(src).to_contain("return \"software\"")
# selection hooks: CLI flag first, then env
expect(src).to_contain("--backend=")
expect(src).to_contain("SIMPLE_GUI_BACKEND")
```

</details>

#### renders the showcase through ONE persistent session reused across frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(SHOWCASE_SRC)
# persistent session created once via the fast (GPU-only for metal) path
expect(src).to_contain("Engine2D.create_with_backend_fast(w, h, showcase_backend_key())")
# redraw loop paints into the existing engine, no per-frame create
expect(src).to_contain("build_frame_state_into(engine, fw, fh, state)")
# explicit shutdown on exit paths
expect(src).to_contain("engine.shutdown()")
```

</details>

#### surfaces honest frame provenance in the showcase frame log

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(SHOWCASE_SRC)
expect(src).to_contain("read_pixels_with_source()")
# brace-free needle: the print template itself contains interpolation
# braces which a literal here would re-interpolate
expect(src).to_contain("showcase_frame_backend=")
```

</details>

#### wires the WM compositor raster lane through Engine2dCompositorBackend by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(COMPOSITOR_BACKEND_SRC)
# trait conformance so HostCompositor can compose through Engine2D ops
expect(src).to_contain("impl CompositorBackend for Engine2dCompositorBackend:")
# backend-by-name factory with ONE persistent session + explicit shutdown
expect(src).to_contain("static fn create_named(width: i32, height: i32, backend_name: text) -> Engine2dCompositorBackend:")
expect(src).to_contain("Engine2D.create_with_backend_fast(width, height, backend_name)")
expect(src).to_contain("me shutdown():")
# CPU default when no env is set
expect(src).to_contain("return \"software\"")
# honest provenance accessor
expect(src).to_contain("fn frame_provenance() -> text:")
```

</details>

#### asserts device_readback provenance and CPU-vs-Metal parity in the evidence harness

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(EVIDENCE_SRC)
# (a) metal lane must be device_readback — cpu_mirror fails the gate
expect(src).to_contain("if metal_rb.source != \"device_readback\":")
# (b) bit-exact pixel compare of independently produced CPU/Metal frames
expect(src).to_contain("compare_exact(\"primitives\", cpu_prim, metal_prim)")
expect(src).to_contain("compare_exact(\"wm_composite\", cpu_rb, metal_rb)")
```

</details>

#### keeps the Metal circle-outline kernel on the canonical d<0 midpoint tie-break

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(METAL_MSL_SRC)
# kernel_draw_circle replays the CPU midpoint loop; the tie-break must
# stay `d < 0` (D2-canonical, matches backend_software/backend_emu) —
# `d <= 0` diverges by 16 ring pixels at midpoint-tie radii (r=4, r=14)
expect(src).to_contain("midpoint-tie radii")
```

</details>

#### gates the one-call draw_image upload on its own runtime capability flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(METAL_BACKEND_SRC)
# upload extern (rt_write_u32s_to_raw) is newer than the download
# extern; sharing the readback flag hard-errors mid-frame on runtimes
# that export only the download side
expect(src).to_contain("SIMPLE_ONE_CALL_UPLOAD")
```

</details>

#### offers a deployed-binary bulk upload via the spl_gpu_transfer cdylib, off by default, loud on missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(METAL_BACKEND_SRC)
# opt-in mode name — the deployed binary lacks rt_write_u32s_to_raw, so
# the cdylib route (16 px per FFI call) is the only bulk upload it can run
expect(src).to_contain("SIMPLE_BULK_UPLOAD")
expect(src).to_contain("== \"cdylib\"")
# bulk staging goes through the sanctioned SFFI sibling-cdylib bridge
expect(src).to_contain("spl_wffi_call_i64")
expect(src).to_contain("spl_gpu_stage_write8")
# loud error, never a silent per-pixel fallback, when the mode is
# requested but the cdylib cannot be loaded
expect(src).to_contain("could not be loaded")
# the per-pixel loop remains the default (no env set) path
expect(src).to_contain("metal_host_write_i32(host, i * 4, v)")
```

</details>

### Hosted WM engine2d raster-lane adoption (task #28-A)

#### routes the default hosted WM frame through SharedWmScene Draw IR and Engine2D

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = file_read(HOSTED_ENTRY_SRC)
val core = file_read(HOST_CORE_SRC)
expect(entry).to_contain("Engine2dCompositorBackend.create_from_env(WINDOW_WIDTH, WINDOW_HEIGHT)")
expect(entry).to_contain("comp.render_frame_engine2d(raster)")
expect(entry).to_contain("if not comp.render_frame_engine2d(raster):")
expect(entry).to_contain("draw-ir-rejected retry=compatibility")
expect(entry).to_contain("comp.render_frame()")
expect(core).to_contain("shared_wm_scene_draw_ir_composition_with_content(")
expect(core).to_contain("executor.render_draw_ir_composition(composition, images)")
expect(core).to_contain("host_wm_chrome_force_direct()")
expect(core).to_contain("shared_wm_content_frame_image_uri(frame)")
```

</details>

#### reuses one Engine2D session, recreates it on resize, and shuts it down

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(HOSTED_ENTRY_SRC)
expect(src).to_contain("var raster = raster_in")
expect(src).to_contain("raster = Engine2dCompositorBackend.create_from_env(physical.width, physical.height)")
expect(src).to_contain("raster.shutdown()")
expect(src).to_contain("hosted_winit_present_pure_simple_pixels(presenter, comp.pure_simple_pixel_buffer()")
```

</details>

#### fails closed when live or motion pixels cannot reach the host framebuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = file_read(HOSTED_ENTRY_SRC)
val guard = "if not hosted_winit_present_pure_simple_pixels(presenter, comp.pure_simple_pixel_buffer(), comp.width, comp.height):\n                print "
expect(src).to_contain(guard + "\"ERROR: hosted WM live pure-Simple frame presentation failed\"")
expect(src).to_contain(guard + "\"ERROR: hosted WM motion pure-Simple frame presentation failed\"")
```

</details>

#### renders the default color frame through the canonical hosted Draw IR route

- host wm force direct chrome
- var comp = HostCompositor new headless
- comp apply bridge request
   - Expected: pixels.len() equals `240 * 180`
   - Expected: pixels[0] equals `wm_chrome_theme().command_lane`
   - Expected: raster.last_composition_id equals `"wm-composite"`
   - Expected: raster.last_scene_key is not blank
   - Expected: raster.last_web_content_image_count is greater than `0`
   - Expected: readback completed at `240x180`, stride `960`, format `argb8888`
   - Expected: a later direct pixel mutation invalidates the correlated receipt
- raster shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
host_wm_force_direct_chrome(false)
val raster = Engine2dCompositorBackend.create_named(240, 180, "software")
var comp = HostCompositor.new_headless(Size(width: 240u64, height: 180u64))
comp.apply_bridge_request(1, 1, COMP_CREATE_WINDOW.to_i64(), 0, "Docs", 20, 48, 160, 100, "<p>canonical hosted text</p>", 1, "font-route-test")
expect(comp.render_frame_engine2d(raster)).to_be(true)
val pixels = comp.pure_simple_pixel_buffer()
expect(pixels.len()).to_equal(240 * 180)
expect(pixels[0]).to_equal(wm_chrome_theme().command_lane)
expect(pixels[90 * 240 + 30] == wm_chrome_theme().command_lane).to_be(false)
expect(raster.last_composition_id).to_equal("wm-composite")
expect(raster.last_scene_key == "").to_be(false)
expect(raster.last_web_content_image_count).to_be_greater_than(0)
expect(raster.last_readback_completed).to_be(true)
expect(raster.last_readback_width).to_equal(240)
expect(raster.last_readback_height).to_equal(180)
expect(raster.last_readback_stride).to_equal(960)
expect(raster.last_readback_format).to_equal("argb8888")
expect(raster.frame_provenance()).to_contain("composition_id=wm-composite;scene_key=")
expect(raster.frame_provenance()).to_contain(";web_content_image_count=1")
expect(raster.frame_provenance()).to_contain(";completed=true;width=240;height=180;stride=960;format=argb8888")
raster.fill_rect(0, 0, 1, 1, 0xFFFFFFFFu32)
expect(raster.last_readback_completed).to_be(false)
expect(raster.last_readback_width).to_equal(0)
expect(raster.last_readback_height).to_equal(0)
expect(raster.last_readback_stride).to_equal(0)
expect(raster.last_readback_format).to_equal("")
expect(raster.last_readback_checksum).to_equal(0)
expect(raster.last_composition_id).to_equal("")
expect(raster.last_scene_key).to_equal("")
expect(raster.last_web_content_image_count).to_equal(0)
raster.shutdown()
```

</details>

#### produces a software-provenance frame through the same Engine2dCompositorBackend seam hosted_entry adopts

- host wm force direct chrome
- var comp = HostCompositor new
- comp render frame
   - Expected: pixels.len() equals `64 * 48`
   - Expected: pixels[0] equals `wm_chrome_theme().taskbar`
   - Expected: pixels[64 * 24 + 32] equals `pixels[0]`
- comp backend shutdown
- host wm force direct chrome


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pin the direct compatibility path to preserve its existing backend
# provenance contract independently from the canonical hosted route.
host_wm_force_direct_chrome(true)
val backend = Engine2dCompositorBackend.create_named(64, 48, "software")
var comp = HostCompositor.new(backend, Size(width: 64u64, height: 48u64))
comp.render_frame()
val pixels = comp.backend.get_pixel_buffer()
expect(pixels.len()).to_equal(64 * 48)
# Content pin (not just length): at 48px tall the 56px taskbar clips
# across the full target, so both a corner and the centre must carry
# the same non-zero taskbar color after render_frame. This
# proves get_pixel_buffer() returns the Engine2D session's rendered
# framebuffer — a zeroed/garbage readback (or a get_pixel_buffer that
# returns an all-zero allocation of the right length) fails here, where
# a bare length==w*h check would silently pass. Value is the composited
# opaque slate (alpha=0xFF -> >= 0xFF000000).
expect(pixels[0]).to_equal(wm_chrome_theme().taskbar)
expect(pixels[64 * 24 + 32]).to_equal(pixels[0])
val prov = comp.backend.frame_provenance()
expect(prov).to_contain("backend=software")
expect(prov).to_contain("source=")
comp.backend.shutdown()
host_wm_force_direct_chrome(false)
```

</details>

#### reports device_readback provenance when the metal raster backend is available

- host wm force direct chrome
- var comp = HostCompositor new
- comp render frame
- print "SKIP: metal raster backend unavailable on this host
- comp backend shutdown
- host wm force direct chrome


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# frame_provenance() reports cpu_mirror until a frame has actually been
# drawn+presented (gpu_frame_complete gate) — render_frame() first so a
# genuinely-unavailable Metal device (reported via backend_name, not a
# premature cpu_mirror read) is what triggers the skip below.
host_wm_force_direct_chrome(true)
val backend = Engine2dCompositorBackend.create_named(64, 48, "metal")
var comp = HostCompositor.new(backend, Size(width: 64u64, height: 48u64))
comp.render_frame()
val prov = comp.backend.frame_provenance()
if not prov.contains("backend=metal"):
    print "SKIP: metal raster backend unavailable on this host ({prov})"
else:
    expect(prov).to_contain("source=device_readback")
comp.backend.shutdown()
host_wm_force_direct_chrome(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/engine2d_gpu_offload_contract_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GPU offload wiring contract (showcase + WM compositor)
- Hosted WM engine2d raster-lane adoption (task #28-A)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
