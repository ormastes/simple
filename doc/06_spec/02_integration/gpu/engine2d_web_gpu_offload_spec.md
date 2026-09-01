# Engine2d Web Gpu Offload Specification

> Tests covering Engine2D web renderer GPU offload.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2d Web Gpu Offload Specification

## Scenarios

### Engine2D web renderer GPU offload

#### probes the WebGPU adapter honestly and disclosures the offload lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probes the WebGPU adapter honestly and disclosures the offload lane
- Probe adapter availability (no assumption either way)
- Probe result is self-consistent on every host
   - Expected: probe.status equals `Failed`
   - Expected: probe.adapter_count equals `0`
- Strict-init check agrees with the probe
   - Expected: strict.reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("probes the WebGPU adapter honestly and disclosures the offload lane")
step("Probe adapter availability (no assumption either way)")
val avail = webgpu_available()
val probe = webgpu_probe_adapter()
if avail:
    print("[webgpu-offload] adapter lane AVAILABLE: status=" + probe.status +
        " adapters=" + probe.adapter_count.to_text() +
        " selected=" + probe.selected_adapter)
else:
    print("[webgpu-offload] SKIPPED: no WebGPU runtime on this host; " +
        "CPU-mirror assertions below still run hard")

step("Probe result is self-consistent on every host")
# status vocabulary is closed
val status_ok = (probe.status == "Ok" or probe.status == "Failed" or probe.status == "Fallback")
expect(status_ok).to_be(true)
if not avail:
    # No runtime => the probe must say Failed with zero adapters, never Ok.
    expect(probe.status).to_equal("Failed")
    expect(probe.adapter_count).to_equal(0)
    expect(probe.fell_through_to_cpu).to_be(false)
if probe.status == "Ok":
    expect(probe.adapter_count > 0).to_be(true)
    expect(probe.fell_through_to_cpu).to_be(false)
if probe.status == "Fallback":
    expect(probe.fell_through_to_cpu).to_be(true)

step("Strict-init check agrees with the probe")
val strict = webgpu_strict_init_check()
if probe.status == "Ok":
    expect(strict.reason).to_equal("")
else:
    expect(strict.reason == "").to_be(false)
```

</details>

#### creates a WebGPU surface session with honest init and probe reporting

- creates a WebGPU surface session with honest init and probe reporting
- Create + init a WebGpuBackend surface
- init() and probe() carry the same availability signal
- CPU mirror is allocated unconditionally (hard assert)
   - Expected: px.len() equals `16 * 16`
- Readback provenance is cpu_mirror always (no device readback SFFI exists)
   - Expected: rb.source equals `cpu_mirror`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates a WebGPU surface session with honest init and probe reporting")
step("Create + init a WebGpuBackend surface")
var backend = WebGpuBackend.create()
val gpu_ok = backend.init(16, 16)

step("init() and probe() carry the same availability signal")
val pr = backend.probe()
if gpu_ok:
    print("[webgpu-offload] surface live: " + pr.device_name)
else:
    print("[webgpu-offload] SKIPPED: no live WebGPU surface (" + pr.fallback_reason + ")")
    # Honest reporting: a CPU-mirror-only backend must not claim a device.
    expect(backend.initialized).to_be(false)

step("CPU mirror is allocated unconditionally (hard assert)")
val px = backend.read_pixels()
expect(px.len()).to_equal(16 * 16)

step("Readback provenance is cpu_mirror always (no device readback SFFI exists)")
val rb = backend.read_pixels_with_source()
expect(rb.source).to_equal("cpu_mirror")
backend.shutdown()
```

</details>

#### draw submission readback matches the SoftwareBackend oracle (hard)

- draw submission readback matches the SoftwareBackend oracle (hard)
- Submit clear + filled-rect draws to the WebGPU backend
- Render the same ops on the SoftwareBackend CPU oracle
- Center is red, corner is black, channel-for-channel vs oracle
   - Expected: color_r(px[ci]) equals `255`
   - Expected: color_g(px[ci]) equals `0`
   - Expected: color_b(px[ci]) equals `0`
   - Expected: color_r(px[0]) equals `0`
   - Expected: px[ci] equals `oracle[ci]`
   - Expected: px[0] equals `oracle[0]`
- Full-frame mismatch count is zero
   - Expected: pixel_mismatches(px, oracle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("draw submission readback matches the SoftwareBackend oracle (hard)")
step("Submit clear + filled-rect draws to the WebGPU backend")
var backend = WebGpuBackend.create()
backend.init(16, 16)
backend.clear(rgb(0, 0, 0))
backend.draw_rect_filled(4, 4, 8, 8, rgb(255, 0, 0))
backend.present()
val px = backend.read_pixels()

step("Render the same ops on the SoftwareBackend CPU oracle")
var sw = SoftwareBackend.create()
sw.init(16, 16)
sw.clear(rgb(0, 0, 0))
sw.draw_rect_filled(4, 4, 8, 8, rgb(255, 0, 0))
val oracle = sw.read_pixels()

step("Center is red, corner is black, channel-for-channel vs oracle")
val ci = (8 * 16 + 8) as i64
expect(color_r(px[ci])).to_equal(255)
expect(color_g(px[ci])).to_equal(0)
expect(color_b(px[ci])).to_equal(0)
expect(color_r(px[0])).to_equal(0)
expect(px[ci]).to_equal(oracle[ci])
expect(px[0]).to_equal(oracle[0])

step("Full-frame mismatch count is zero")
expect(pixel_mismatches(px, oracle)).to_equal(0)
backend.shutdown()
```

</details>

#### clip and mask apply to offloaded ops (offload-desync regression guard)

- clip and mask apply to offloaded ops (offload-desync regression guard)
- Draw a clipped filled rect on the WebGPU backend
- Same ops on the SoftwareBackend oracle
- Inside-clip pixel painted, outside-clip pixel untouched, oracle-equal
   - Expected: color_g(px[inside]) equals `255`
   - Expected: color_g(px[outside]) equals `0`
   - Expected: pixel_mismatches(px, oracle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("clip and mask apply to offloaded ops (offload-desync regression guard)")
step("Draw a clipped filled rect on the WebGPU backend")
var backend = WebGpuBackend.create()
backend.init(16, 16)
backend.clear(rgb(0, 0, 0))
backend.set_clip(0, 0, 8, 8)
backend.draw_rect_filled(0, 0, 16, 16, rgb(0, 255, 0))
backend.clear_clip()
val px = backend.read_pixels()

step("Same ops on the SoftwareBackend oracle")
var sw = SoftwareBackend.create()
sw.init(16, 16)
sw.clear(rgb(0, 0, 0))
sw.set_clip(0, 0, 8, 8)
sw.draw_rect_filled(0, 0, 16, 16, rgb(0, 255, 0))
sw.clear_clip()
val oracle = sw.read_pixels()

step("Inside-clip pixel painted, outside-clip pixel untouched, oracle-equal")
val inside = (4 * 16 + 4) as i64
val outside = (12 * 16 + 12) as i64
expect(color_g(px[inside])).to_equal(255)
expect(color_g(px[outside])).to_equal(0)
expect(pixel_mismatches(px, oracle)).to_equal(0)
backend.shutdown()
```

</details>

#### web HTML scene offloaded through the WebGPU backend matches the CPU oracle

- web HTML scene offloaded through the WebGPU backend matches the CPU oracle
- Produce the web draw command scene from HTML
- Submit the scene's fill commands to the WebGPU backend
- Composite the same scene on the SoftwareBackend oracle
- Pixel-for-pixel parity with the CPU oracle (hard)
   - Expected: px.len() equals `48 * 32`
   - Expected: pixel_mismatches(px, oracle) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("web HTML scene offloaded through the WebGPU backend matches the CPU oracle")
step("Produce the web draw command scene from HTML")
val scene = simple_web_render_html_to_scene(HTML, 48, 32)
expect(scene.commands.len() > 0).to_be(true)

step("Submit the scene's fill commands to the WebGPU backend")
var backend = WebGpuBackend.create()
backend.init(48, 32)
backend.clear(0xFFFFFFFFu32)
var i = 0
while i < scene.commands.len():
    if scene.commands[i].kind == "fill_rect":
        backend.draw_rect_filled(0, 0, 48, 32, scene.commands[i].color | 0xFF000000u32)
    i = i + 1
backend.present()
val px = backend.read_pixels()

step("Composite the same scene on the SoftwareBackend oracle")
var sw = SoftwareBackend.create()
sw.init(48, 32)
sw.clear(0xFFFFFFFFu32)
var j = 0
while j < scene.commands.len():
    if scene.commands[j].kind == "fill_rect":
        sw.draw_rect_filled(0, 0, 48, 32, scene.commands[j].color | 0xFF000000u32)
    j = j + 1
val oracle = sw.read_pixels()

step("Pixel-for-pixel parity with the CPU oracle (hard)")
expect(px.len()).to_equal(48 * 32)
expect(pixel_mismatches(px, oracle)).to_equal(0)
backend.shutdown()
```

</details>

#### WebRenderSession lifecycle: create, frames, refcount teardown

- WebRenderSession lifecycle: create, frames, refcount teardown
- Create a managed-shared web render session
   - Expected: ws.create_surface() equals `42`
- Frame begin/end accounting
   - Expected: ws.frame_count equals `2`
   - Expected: ws.begin_count equals `2`
   - Expected: ws.end_count equals `2`
- Retain then release to zero tears the session down
   - Expected: ws.retain_session() equals `2`
   - Expected: ws.create_surface() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("WebRenderSession lifecycle: create, frames, refcount teardown")
step("Create a managed-shared web render session")
var ws = WebRenderSession.create(surface_id: 42, session_id: 7,
    session_mode: WebRenderSessionMode.ManagedShared)
expect(ws.is_valid()).to_be(true)
expect(ws.create_surface()).to_equal(42)

step("Frame begin/end accounting")
ws.begin_frame()
expect(ws.is_active).to_be(true)
ws.end_frame()
ws.begin_frame()
ws.end_frame()
expect(ws.frame_count).to_equal(2)
expect(ws.begin_count).to_equal(2)
expect(ws.end_count).to_equal(2)
expect(ws.is_active).to_be(false)

step("Retain then release to zero tears the session down")
expect(ws.retain_session()).to_equal(2)
ws.release_session()
ws.release_session()
expect(ws.is_valid()).to_be(false)
expect(ws.create_surface()).to_equal(0)
```

</details>

#### PerfExclusive is rejected for web surfaces and WM children

- PerfExclusive is rejected for web surfaces and WM children
- WebRenderSession refuses PerfExclusive
   - Expected: ws.create_surface() equals `0`
   - Expected: ws.retain_session() equals `-1`
- WM policy refuses perf_exclusive children, accepts managed_shared


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PerfExclusive is rejected for web surfaces and WM children")
step("WebRenderSession refuses PerfExclusive")
var ws = WebRenderSession.create(surface_id: 1, session_id: 1,
    session_mode: WebRenderSessionMode.PerfExclusive)
expect(ws.is_valid()).to_be(false)
expect(ws.create_surface()).to_equal(0)
expect(ws.retain_session()).to_equal(-1)

step("WM policy refuses perf_exclusive children, accepts managed_shared")
var wm = WmBackendSession.create(session_id: 9)
val rejected = wm.retain_for_child("perf_exclusive")
expect(rejected.starts_with("error:")).to_be(true)
val accepted = wm.retain_for_child("managed_shared")
expect(accepted.starts_with("retained")).to_be(true)
```

</details>

#### WM session composes surfaces and a RenderSurfaceSession tracks the pipeline

- WM session composes surfaces and a RenderSurfaceSession tracks the pipeline
- Adopt two surfaces into the WM session and present a batch
   - Expected: wm.surface_count equals `2`
   - Expected: wm.dirty_count equals `1`
- RenderSurfaceSession accumulates stage timings + readback toggle
   - Expected: rs.frame_count equals `1`
   - Expected: rs.total_pipeline_us() equals `175`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("WM session composes surfaces and a RenderSurfaceSession tracks the pipeline")
step("Adopt two surfaces into the WM session and present a batch")
var wm = WmBackendSession.create(session_id: 3)
wm.add_surface(101, 48, 32)
wm.add_surface(102, 16, 16)
wm.propagate_dirty(101, 0, 0, 48, 32)
val presented = wm.compose_and_present()
expect(presented.starts_with("present batch=1")).to_be(true)
expect(wm.surface_count).to_equal(2)
expect(wm.dirty_count).to_equal(1)

step("RenderSurfaceSession accumulates stage timings + readback toggle")
var rs = RenderSurfaceSession.create(101, 3, "managed_shared", 48, 32)
val fid = rs.begin_frame()
rs.record_paint(120)
rs.record_upload(40)
rs.record_present(15)
val line = rs.end_frame(fid)
expect(rs.frame_count).to_equal(1)
expect(rs.total_pipeline_us()).to_equal(175)
expect(line.contains("total_us=175")).to_be(true)
rs.enable_readback(true)
expect(rs.readback_enabled).to_be(true)
wm.cleanup()
```

</details>

#### WebGpuProofBackend session flow submits and presents with honest mode

- WebGpuProofBackend session flow submits and presents with honest mode
- Create the proof backend and disclose its mode
- Uninitialized session refuses submit/present
   - Expected: proof.create_device() equals `error: adapter not initialized`
   - Expected: proof.submit_commands(3) equals `error: not initialized`
   - Expected: proof.present() equals `error: not initialized`
- Init adapter then submit + present through the session
   - Expected: proof.init_adapter() equals `ok`
   - Expected: proof.create_device() equals `ok`
   - Expected: proof.submit_count equals `1`
   - Expected: proof.present_count equals `1`
   - Expected: proof.cleanup() equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("WebGpuProofBackend session flow submits and presents with honest mode")
step("Create the proof backend and disclose its mode")
var proof = WebGpuProofBackend.create()
val mode_ok = (proof.mode == "real" or proof.mode == "stub" or proof.mode == "unavailable")
expect(mode_ok).to_be(true)
if proof.mode == "unavailable":
    print("[webgpu-offload] SKIPPED: proof backend unavailable (" +
        proof.adapter_info.error_message + "); logic assertions still run")
    step("Uninitialized session refuses submit/present")
    expect(proof.create_device()).to_equal("error: adapter not initialized")
    expect(proof.submit_commands(3)).to_equal("error: not initialized")
    expect(proof.present()).to_equal("error: not initialized")
    expect(proof.is_real_mode()).to_be(false)
    return

print("[webgpu-offload] proof backend mode=" + proof.mode +
    " adapter=" + proof.adapter_info.summary())
step("Init adapter then submit + present through the session")
expect(proof.init_adapter()).to_equal("ok")
expect(proof.create_device()).to_equal("ok")
val surf = proof.create_surface(48, 32)
expect(surf.starts_with("ok")).to_be(true)
val sub = proof.submit_commands(3)
expect(sub.starts_with("error")).to_be(false)
val pres = proof.present()
expect(pres.starts_with("error")).to_be(false)
expect(proof.submit_count).to_equal(1)
expect(proof.present_count).to_equal(1)
expect(proof.cleanup()).to_equal("ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/02_integration/gpu/engine2d_web_gpu_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2D web renderer GPU offload.
- Engine2D web renderer GPU offload

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `01f2b819eb11c1916abac19ef0027e0bf9c61e3ccf1fa5556315313ee655ed3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01f2b819eb11c1916abac19ef0027e0bf9c61e3ccf1fa5556315313ee655ed3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01f2b819eb11c1916abac19ef0027e0bf9c61e3ccf1fa5556315313ee655ed3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/gpu/engine2d_web_gpu_offload_spec.spl
mirror: doc/06_spec/02_integration/gpu/engine2d_web_gpu_offload_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/gpu/engine2d_web_gpu_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/gpu/engine2d_web_gpu_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/gpu/engine2d_web_gpu_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 24 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/gpu/engine2d_web_gpu_offload_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probes the WebGPU adapter honestly and disclosures the offload lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu/engine2d_web_gpu_offload_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a WebGPU surface session with honest init and probe reporting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu/engine2d_web_gpu_offload_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'draw submission readback matches the SoftwareBackend oracle (hard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
