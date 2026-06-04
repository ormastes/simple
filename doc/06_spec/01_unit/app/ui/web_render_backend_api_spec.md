# Web Render Backend Api Specification

> <details>

<!-- sdn-diagram:id=web_render_backend_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_render_backend_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_render_backend_api_spec -> common
web_render_backend_api_spec -> app
web_render_backend_api_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_render_backend_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Render Backend Api Specification

## Scenarios

### web render backends use the shared common API

#### keeps headless as an explicit no-display render target

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_HEADLESS, "Headless", "<main>headless</main>", "", "", 80, 24)
val artifact = web_render_to_artifact(req)

expect(artifact.target).to_equal(WEB_RENDER_TARGET_HEADLESS)
expect(artifact.capability_summary).to_equal("headless")
expect(web_render_capability_summary(WEB_RENDER_TARGET_HEADLESS)).to_equal("headless")
expect(web_render_capabilities_for_target(WEB_RENDER_TARGET_HEADLESS).len()).to_equal(0)
```

</details>

#### keeps render_html as body-only HTML for web electron and tauri

1. Err
   - Expected: e equals ``

2. Ok
   - Expected: electron_html equals `web_html`
   - Expected: electron_render_ipc_json(state, 1280, 720) equals `web_render_to_artifact(electron_req).ipc_json`

3. Err
   - Expected: e equals ``

4. Ok
   - Expected: tauri_html equals `web_html`


<details>
<summary>Executable SPipe</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val web = WebBackend.new(4010)
val web_html = web.render_html(state)
expect(web_html).to_contain("widget-panel")
expect(web_html).to_contain("widget-button")
expect(web.input_envelope_json("main", UIEvent.KeyPress(key: "enter"))).to_contain("\"target\":\"simple_web\"")
expect(web.snapshot_envelope_json("main", 3u64, "{\"mode\":\"NORMAL\"}")).to_contain("\"type\":\"snapshot\"")
expect(web.patch_envelope_json("main", 3u64, 4u64, "[]", "")).to_contain("\"type\":\"patch\"")

val tui_web = TuiWebBackend.new()
expect(tui_web.render_html(state)).to_equal(web_html)
expect(tui_web.input_envelope_json("main", UIEvent.KeyPress(key: "enter"))).to_contain("\"target\":\"tui_web\"")
expect(tui_web.snapshot_envelope_json("main", 3u64, "{\"mode\":\"NORMAL\"}")).to_contain("\"type\":\"snapshot\"")
expect(tui_web.patch_envelope_json("main", 3u64, 4u64, "[]", "")).to_contain("\"target\":\"tui_web\"")

val electron_result = ElectronBackend.new(4011)
match electron_result:
    Err(e):
        expect(e).to_equal("")
    Ok(electron):
        val electron_html = electron.render_html(state)
        expect(electron_html).to_equal(web_html)
        val electron_req = WebRenderRequest.html(WEB_RENDER_TARGET_ELECTRON, "", web_html, "", "", 1280, 720)
        expect(electron_render_ipc_json(state, 1280, 720)).to_equal(web_render_to_artifact(electron_req).ipc_json)
        expect(ipc_writer_message(electron_render_ipc_json(state, 1280, 720))).to_contain("\"target\":\"electron\"")
        expect(electron.input_envelope_json("main", UIEvent.KeyPress(key: "enter"))).to_contain("\"target\":\"electron\"")
        expect(electron.input_envelope_json("main", UIEvent.Resize(width: 640, height: 480))).to_contain("\"event_type\":\"resize\"")
        expect(electron.input_envelope_json("main", UIEvent.InputChange(target_id: "name", value: "Ada"))).to_contain("\"event_type\":\"input\"")
        expect(electron.input_envelope_json("main", UIEvent.MouseEvent(x: 10.0, y: 20.0, button: "left", kind: "down"))).to_contain("\"event_type\":\"mouse_down\"")
        expect(electron.snapshot_envelope_json("main", 3u64, "{\"mode\":\"NORMAL\"}")).to_contain("\"revision\":3")
        expect(electron.patch_envelope_json("main", 3u64, 4u64, "[]", "")).to_contain("\"to_sequence\":4")

val tauri_result = TauriBackend.new(4012)
match tauri_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tauri):
        val tauri_html = tauri.render_html(state)
        expect(tauri_html).to_equal(web_html)
        expect(tauri_render_ipc_json(state, 1280, 720)).to_contain("\"target\":\"tauri\"")
        expect(tauri_render_ipc_json(state, 1280, 720)).to_contain("\"surface_id\":\"\"")
        expect(ipc_writer_message(tauri_render_ipc_json(state, 1280, 720))).to_contain("\"target\":\"tauri\"")
        expect(tauri.input_envelope_json("main", UIEvent.InputChange(target_id: "name", value: "Ada"))).to_contain("\"target\":\"tauri\"")
        expect(tauri.snapshot_envelope_json("main", 3u64, "{\"mode\":\"NORMAL\"}")).to_contain("\"surface_id\":\"main\"")
        expect(tauri.patch_envelope_json("main", 3u64, 4u64, "[]", "")).to_contain("\"patches\":[]")
```

</details>

#### records pure simple browser output as a shared web render artifact

1. Err
   - Expected: e equals ``

2. Ok

3. backend render frame
   - Expected: backend.web_render_target equals `pure_simple`
   - Expected: backend.last_artifact_pixels equals `64 * 48`
   - Expected: backend.last_artifact_engine2d_status equals `WEB_RENDER_ENGINE2D_STATUS_RENDERED`
   - Expected: backend.last_artifact_engine2d_backend equals `software`


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val backend_result = BrowserBackend.create(64, 48, "software")
match backend_result:
    Err(e):
        expect(e).to_equal("")
    Ok(backend):
        val body_html = backend.render_html(state)
        expect(body_html).to_contain("widget-panel")
        expect(body_html).to_contain("widget-button")

        backend.render_frame(state.tree, state)
        expect(backend.web_render_target).to_equal("pure_simple")
        expect(backend.last_artifact_capabilities).to_contain("touch")
        expect(backend.last_artifact_html).to_contain("<div id=\"app\">")
        expect(backend.last_artifact_html).to_contain("widget-button")
        expect(backend.last_artifact_pixels).to_equal(64 * 48)
        expect(backend.last_artifact_engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_RENDERED)
        expect(backend.last_artifact_engine2d_backend).to_equal("software")
        expect(backend.last_artifact_engine2d_reason).to_contain("Engine2D")
        val ppm = backend.snapshot_ppm_text()
        expect(ppm).to_start_with("P3\n64 48\n255\n")
        expect(ppm).to_contain("255\n")
```

</details>

#### records shared render request provenance across GUI web and headless targets

1. web render request provenance evidence

2. web render request provenance evidence

3. web render request provenance evidence

4. web render request provenance evidence

5. web render request provenance evidence

6. web render request provenance evidence
   - Expected: matrix.len() equals `6`
   - Expected: row.surface_id equals `main`
   - Expected: row.request_has_body is true
   - Expected: row.semantic_attached is true
   - Expected: row.artifact_target_matches is true
   - Expected: row.artifact_dimensions_match is true
   - Expected: row.artifact_has_html is true
   - Expected: row.ready is true
   - Expected: row.reason equals `pass`
   - Expected: matrix[0].target equals `WEB_RENDER_TARGET_SIMPLE_WEB`
   - Expected: matrix[2].artifact_has_ipc_or_pixels is true
   - Expected: matrix[3].artifact_has_ipc_or_pixels is true
   - Expected: matrix[4].target equals `WEB_RENDER_TARGET_HEADLESS`
   - Expected: matrix[5].target equals `WEB_RENDER_TARGET_PURE_SIMPLE`
   - Expected: matrix[5].engine2d_status equals `WEB_RENDER_ENGINE2D_STATUS_RENDERED`
   - Expected: matrix[5].engine2d_backend equals `software`


<details>
<summary>Executable SPipe</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val body = WebBackend.new(4015).render_html(state)
val css = generate_css(state.tree.theme_name())
val semantic_json = WebBackend.new(4016).semantic_snapshot_json(state)
val web_req = web_render_adapter_request(WEB_RENDER_TARGET_SIMPLE_WEB, "main", "", body, css, "", 1280, 720)
val tui_req = web_render_adapter_request(WEB_RENDER_TARGET_TUI_WEB, "main", "", body, "", "", 120, 40)
val electron_req = web_render_adapter_request(WEB_RENDER_TARGET_ELECTRON, "main", "", body, css, "", 1280, 720)
val tauri_req = web_render_adapter_request(WEB_RENDER_TARGET_TAURI, "main", "", body, css, "", 1280, 720)
val headless_req = web_render_adapter_request(WEB_RENDER_TARGET_HEADLESS, "main", "", body, "", "", 80, 24)
val pure_req = web_render_adapter_request(WEB_RENDER_TARGET_PURE_SIMPLE, "main", "", body, css, "", 64, 48).with_pixel_output()
val pure_artifact = web_render_engine2d_rendered_artifact(web_render_pixel_artifact(pure_req, [1u32, 2u32, 3u32, 4u32]), "software")
val matrix = [
    web_render_request_provenance_evidence(web_req, web_render_to_artifact(web_req), semantic_json),
    web_render_request_provenance_evidence(tui_req, web_render_to_artifact(tui_req), semantic_json),
    web_render_request_provenance_evidence(electron_req, web_render_to_artifact(electron_req), semantic_json),
    web_render_request_provenance_evidence(tauri_req, web_render_to_artifact(tauri_req), semantic_json),
    web_render_request_provenance_evidence(headless_req, web_render_to_artifact(headless_req), semantic_json),
    web_render_request_provenance_evidence(pure_req, pure_artifact, semantic_json)
]

expect(matrix.len()).to_equal(6)
for row in matrix:
    expect(row.surface_id).to_equal("main")
    expect(row.request_has_body).to_equal(true)
    expect(row.semantic_attached).to_equal(true)
    expect(row.artifact_target_matches).to_equal(true)
    expect(row.artifact_dimensions_match).to_equal(true)
    expect(row.artifact_has_html).to_equal(true)
    expect(row.ready).to_equal(true)
    expect(row.reason).to_equal("pass")
expect(matrix[0].target).to_equal(WEB_RENDER_TARGET_SIMPLE_WEB)
expect(matrix[2].artifact_has_ipc_or_pixels).to_equal(true)
expect(matrix[3].artifact_has_ipc_or_pixels).to_equal(true)
expect(matrix[4].target).to_equal(WEB_RENDER_TARGET_HEADLESS)
expect(matrix[5].target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
expect(matrix[5].engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_RENDERED)
expect(matrix[5].engine2d_backend).to_equal("software")
expect(matrix[5].summary()).to_contain("engine2d_status=engine2d_rendered")
```

</details>

#### matches Electron and Tauri live snapshot transports to the shared helper output

1. Err
   - Expected: e equals ``

2. Ok
   - Expected: electron.snapshot_envelope_json("main", 5u64, "{\"mode\":\"NORMAL\"}") equals `web_render_snapshot_transport_json("electron", "main", 5u64, "{"mode":"NORMAL... (full value in folded executable source)`
   - Expected: electron.patch_envelope_json("main", 5u64, 6u64, "[]", "{\"mode\":\"INSERT\"}") equals `web_render_patch_transport_json("electron", "main", 5u64, 6u64, "[]", "{"mode... (full value in folded executable source)`

3. Err
   - Expected: e equals ``

4. Ok
   - Expected: tauri.snapshot_envelope_json("main", 5u64, "{\"mode\":\"NORMAL\"}") equals `web_render_snapshot_transport_json("tauri", "main", 5u64, "{"mode":"NORMAL"}")`
   - Expected: tauri.patch_envelope_json("main", 5u64, 6u64, "[]", "{\"mode\":\"INSERT\"}") equals `web_render_patch_transport_json("tauri", "main", 5u64, 6u64, "[]", "{"mode":"... (full value in folded executable source)`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val electron_result = ElectronBackend.new(4013)
match electron_result:
    Err(e):
        expect(e).to_equal("")
    Ok(electron):
        expect(electron.snapshot_envelope_json("main", 5u64, "{\"mode\":\"NORMAL\"}")).to_equal(web_render_snapshot_transport_json("electron", "main", 5u64, "{\"mode\":\"NORMAL\"}"))
        expect(electron.patch_envelope_json("main", 5u64, 6u64, "[]", "{\"mode\":\"INSERT\"}")).to_equal(web_render_patch_transport_json("electron", "main", 5u64, 6u64, "[]", "{\"mode\":\"INSERT\"}"))

val tauri_result = TauriBackend.new(4014)
match tauri_result:
    Err(e):
        expect(e).to_equal("")
    Ok(tauri):
        expect(tauri.snapshot_envelope_json("main", 5u64, "{\"mode\":\"NORMAL\"}")).to_equal(web_render_snapshot_transport_json("tauri", "main", 5u64, "{\"mode\":\"NORMAL\"}"))
        expect(tauri.patch_envelope_json("main", 5u64, 6u64, "[]", "{\"mode\":\"INSERT\"}")).to_equal(web_render_patch_transport_json("tauri", "main", 5u64, 6u64, "[]", "{\"mode\":\"INSERT\"}"))
```

</details>

#### matches Electron and Tauri transport bundles to the common API

<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = sample_state()
val cmd = WebRenderHostWindowCommand(action: "new_browser_window", window_id: "win-transport", surface_id: "main", app_id: "/sys/apps/browser", title: "Browser", url: "https://example.test", x: 0, y: 0, width: 640, height: 480)
val body = WebBackend.new(4015).render_html(state)
val electron_req = WebRenderRequest.html(WEB_RENDER_TARGET_ELECTRON, "", body, "", "", 1280, 720)
val tauri_req = WebRenderRequest.html(WEB_RENDER_TARGET_TAURI, "", body, "", "", 1280, 720)
val browser_req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "", body, "", "", 1280, 720)
val tui_web_req = WebRenderRequest.html(WEB_RENDER_TARGET_TUI_WEB, "", body, "", "", 120, 40)
val electron_bundle = web_render_transport_bundle(electron_req, "main", UIEvent.KeyPress(key: "enter"), 8u64, 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}", cmd)
val tauri_bundle = web_render_transport_bundle(tauri_req, "main", UIEvent.InputChange(target_id: "name", value: "Ada"), 8u64, 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}", cmd)
val browser_bundle = web_render_transport_bundle(browser_req, "main", UIEvent.MouseEvent(x: 10.0, y: 20.0, button: "left", kind: "down"), 8u64, 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}", cmd)
val tui_web_bundle = web_render_transport_bundle(tui_web_req, "main", UIEvent.KeyPress(key: "enter"), 8u64, 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}", cmd)

val electron = ElectronBackend.new(4016).unwrap()
expect(electron_render_ipc_json(state, 1280, 720)).to_contain("\"target\":\"electron\"")
expect(electron.input_envelope_json("main", UIEvent.KeyPress(key: "enter"))).to_equal(electron_bundle.input_json)
expect(electron.input_envelope_json("main", UIEvent.Resize(width: 640, height: 480))).to_contain("\"target\":\"electron\"")
expect(electron.input_envelope_json("main", UIEvent.Resize(width: 640, height: 480))).to_contain("\"event_type\":\"resize\"")
expect(electron.input_envelope_json("main", UIEvent.InputChange(target_id: "name", value: "Ada"))).to_contain("\"event_type\":\"input\"")
expect(electron.input_envelope_json("main", UIEvent.MouseEvent(x: 10.0, y: 20.0, button: "left", kind: "down"))).to_contain("\"event_type\":\"mouse_down\"")
expect(electron.snapshot_envelope_json("main", 8u64, "{\"mode\":\"NORMAL\"}")).to_equal(electron_bundle.snapshot_json)
expect(electron.patch_envelope_json("main", 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}")).to_equal(electron_bundle.patch_json)
expect(electron.host_window_command_json(cmd)).to_equal(electron_bundle.host_window_json)

val tauri = TauriBackend.new(4017).unwrap()
expect(tauri_render_ipc_json(state, 1280, 720)).to_contain("\"target\":\"tauri\"")
expect(tauri.input_envelope_json("main", UIEvent.InputChange(target_id: "name", value: "Ada"))).to_equal(tauri_bundle.input_json)
expect(tauri.snapshot_envelope_json("main", 8u64, "{\"mode\":\"NORMAL\"}")).to_equal(tauri_bundle.snapshot_json)
expect(tauri.patch_envelope_json("main", 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}")).to_equal(tauri_bundle.patch_json)
expect(tauri.host_window_command_json(cmd)).to_equal(tauri_bundle.host_window_json)

val browser = BrowserBackend.create(1280, 720, "software").unwrap()
expect(browser.input_envelope_json("main", UIEvent.MouseEvent(x: 10.0, y: 20.0, button: "left", kind: "down"))).to_equal(browser_bundle.input_json)
expect(browser.snapshot_envelope_json("main", 8u64, "{\"mode\":\"NORMAL\"}")).to_equal(browser_bundle.snapshot_json)
expect(browser.patch_envelope_json("main", 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}")).to_equal(browser_bundle.patch_json)
expect(browser.host_window_command_json(cmd)).to_equal(browser_bundle.host_window_json)

val tui_web = TuiWebBackend.new()
expect(tui_web.input_envelope_json("main", UIEvent.KeyPress(key: "enter"))).to_equal(tui_web_bundle.input_json)
expect(tui_web.snapshot_envelope_json("main", 8u64, "{\"mode\":\"NORMAL\"}")).to_equal(tui_web_bundle.snapshot_json)
expect(tui_web.patch_envelope_json("main", 8u64, 9u64, "[]", "{\"mode\":\"NORMAL\"}")).to_equal(tui_web_bundle.patch_json)
```

</details>

#### classifies static shells and dynamic islands for binary cache planning

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val static_req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Static", "<main><section>stable</section></main>", ".stable{contain:layout paint style}", "", 320, 200)
val static_profile = web_render_optimization_profile(static_req)
expect(static_profile.cache_schema).to_equal("simple-web-cache-v1")
expect(static_profile.cacheable_static_shell).to_equal(true)
expect(static_profile.dynamic_region_count).to_equal(0)
expect(static_profile.render_plan).to_equal("binary_static_shell")
expect(static_profile.cache_key).to_contain("viewport=320x200")
expect(web_render_cache_key(static_req)).to_equal(static_profile.cache_key)

val dynamic_req = WebRenderRequest.html(WEB_RENDER_TARGET_PURE_SIMPLE, "Dynamic", "<main><section data-simple-dynamic='pane'>live</section></main>", "", "new WebSocket('/ui')", 320, 200)
val dynamic_profile = web_render_optimization_profile(dynamic_req)
expect(web_render_dynamic_region_count(dynamic_req)).to_equal(2)
expect(dynamic_profile.cacheable_static_shell).to_equal(false)
expect(dynamic_profile.render_plan).to_equal("static_shell_with_dynamic_islands")
```

</details>

#### can reuse prebuilt full HTML when producing Electron IPC JSON

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = WebRenderRequest.html(WEB_RENDER_TARGET_ELECTRON, "IPC", "<button>Run</button>", "button{color:red}", "", 640, 480)
val full_html = "<html><head><title>cached</title></head><body><div id=\"app\"><button>Run</button></div></body></html>"
val ipc = web_render_ipc_json_with_html(req, full_html)
expect(ipc).to_contain("\"target\":\"electron\"")
expect(ipc).to_contain("cached")
expect(web_render_ipc_json(req)).to_contain("\"target\":\"electron\"")
```

</details>

#### builds URL render requests through the common request envelope

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = web_render_url_request(WEB_RENDER_TARGET_PURE_SIMPLE, "about:blank", 320, 200).with_pixel_output()
expect(req.target).to_equal(WEB_RENDER_TARGET_PURE_SIMPLE)
expect(req.title).to_equal("Simple Web")
expect(req.body_html).to_contain("about:blank")
expect(req.viewport_w).to_equal(320)
expect(req.viewport_h).to_equal(200)
expect(req.wants_pixels).to_equal(true)

val pixel_req = web_render_url_to_request(WEB_RENDER_TARGET_PURE_SIMPLE, "about:blank", 320, 200)
expect(pixel_req.body_html).to_equal(req.body_html)
expect(pixel_req.wants_pixels).to_equal(true)
expect(web_render_pixel_default_page_html("about:blank")).to_contain("<div id=\"app\"><main class='simple-web-default'>")
```

</details>

#### records Engine2D provenance on shared web render artifacts

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val req = web_render_url_request(WEB_RENDER_TARGET_PURE_SIMPLE, "about:blank", 32, 16)
val base = web_render_to_artifact(req)
expect(base.engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_NOT_REQUESTED)
expect(base.engine2d_reason).to_equal("pixel output not requested")

val pixel = web_render_pixel_artifact(req, [1u32, 2u32, 3u32])
expect(pixel.engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_COMPATIBILITY)
expect(pixel.engine2d_backend).to_equal("unknown")
expect(pixel.engine2d_reason).to_contain("did not report Engine2D")

val rendered = web_render_engine2d_rendered_artifact(pixel, "software")
expect(rendered.engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_RENDERED)
expect(rendered.engine2d_backend).to_equal("software")
expect(rendered.pixels.len()).to_equal(3)

val unavailable = web_render_engine2d_unavailable_artifact(base, "opencl", "opencl ICD unavailable")
expect(unavailable.engine2d_status).to_equal(WEB_RENDER_ENGINE2D_STATUS_UNAVAILABLE)
expect(unavailable.engine2d_backend).to_equal("opencl")
expect(unavailable.engine2d_reason).to_equal("opencl ICD unavailable")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/web_render_backend_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- web render backends use the shared common API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
