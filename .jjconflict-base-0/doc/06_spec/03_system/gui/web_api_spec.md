# Web Api Specification

> <details>

<!-- sdn-diagram:id=web_api_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_api_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_api_spec -> app
web_api_spec -> nogc_sync_mut
web_api_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_api_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Api Specification

## Scenarios

### generate_html_page

<details>
<summary>Advanced: produces a full HTML page from demo.ui.sdn</summary>

#### produces a full HTML page from demo.ui.sdn _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = web_api_html("examples/06_io/ui/demo.ui.sdn", 3000)
# Must start with DOCTYPE
expect(html).to_start_with("<!DOCTYPE html>")
# Must contain essential HTML structure
expect(html).to_contain("<html")
expect(html).to_contain("<head>")
expect(html).to_contain("<body>")
expect(html).to_contain("</html>")
# Must contain style and script tags
expect(html).to_contain("<style>")
expect(html).to_contain("<script>")
# Must contain the app title
expect(html).to_contain("Simple UI Demo")
# Must contain widget content from the demo
expect(html).to_contain("widget-panel")
expect(html).to_contain("widget-statusbar")
```

</details>


</details>

<details>
<summary>Advanced: produces a full HTML page from minimal.ui.sdn</summary>

#### produces a full HTML page from minimal.ui.sdn _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = web_api_html("examples/06_io/ui/minimal.ui.sdn", 8080)
expect(html).to_start_with("<!DOCTYPE html>")
expect(html).to_contain("<title>Minimal</title>")
expect(html).to_contain("widget-panel")
expect(html).to_contain("Hello from Simple UI!")
```

</details>


</details>

### generate_css

<details>
<summary>Advanced: dark theme contains dark background color</summary>

#### dark theme contains dark background color _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_css("dark")
expect(css.len()).to_be_greater_than(0)
# Dark theme uses #1e1e2e background
expect(css).to_contain("#1e1e2e")
# Dark theme text color
expect(css).to_contain("#cdd6f4")
# Must contain widget classes
expect(css).to_contain(".widget-panel")
expect(css).to_contain(".widget-statusbar")
```

</details>


</details>

<details>
<summary>Advanced: light theme contains light background color</summary>

#### light theme contains light background color _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_css("light")
expect(css.len()).to_be_greater_than(0)
# Light theme uses #ffffff background
expect(css).to_contain("#ffffff")
# Light theme text color
expect(css).to_contain("#333333")
```

</details>


</details>

<details>
<summary>Advanced: dark and light themes produce different output</summary>

#### dark and light themes produce different output _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dark_css = generate_css("dark")
val light_css = generate_css("light")
expect(dark_css != light_css).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: glass obsidian theme serializes real CSS color values</summary>

#### glass obsidian theme serializes real CSS color values _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val css = generate_css("glass_obsidian_dark")
expect(css).to_contain("--ui-bg: #060612")
expect(css).to_contain("--ui-text: #E3E0F3")
expect(css).to_contain("--glass-accent: #C6C6C8")
expect(css.contains("Object { class")).to_equal(false)
expect(css.contains("+ WM_TRAFFIC")).to_equal(false)
```

</details>


</details>

### generate_js

<details>
<summary>Advanced: produces WebSocket connection code</summary>

#### produces WebSocket connection code _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val js = generate_js(3000)
expect(js.len()).to_be_greater_than(0)
expect(js).to_contain("WebSocket")
expect(js).to_contain("connect")
expect(js).to_contain("3000")
expect(js).to_contain("keydown")
```

</details>


</details>

<details>
<summary>Advanced: uses correct port in WebSocket URL</summary>

#### uses correct port in WebSocket URL _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val js = generate_js(9999)
expect(js).to_contain("9999")
```

</details>


</details>

### generate_wm_js

<details>
<summary>Advanced: boots immediately when the document is already loaded</summary>

#### boots immediately when the document is already loaded _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val js = generate_wm_js(3333)
expect(js).to_contain("document.readyState === 'complete'")
expect(js).to_contain("bootWMAfterLoad();")
expect(js).to_contain("new SimpleWindowManager()")
```

</details>


</details>

<details>
<summary>Advanced: retries stalled or errored websocket connections</summary>

#### retries stalled or errored websocket connections _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val js = generate_wm_js(3333)
expect(js).to_contain("let reconnectTimer = null")
expect(js).to_contain("let connectDeadline = null")
expect(js).to_contain("ws.readyState === 0")
expect(js).to_contain("WM WebSocket still connecting after startup grace period")
expect(js).to_contain("ws.onerror")
expect(js).to_contain("scheduleReconnect()")
```

</details>


</details>

### generate_wm_html_page

<details>
<summary>Advanced: produces the SimpleOS WM shell scaffold</summary>

#### produces the SimpleOS WM shell scaffold _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_wm_html_page("glass_obsidian_dark", "SimpleOS Web WM", 3333)
expect(html).to_start_with("<!DOCTYPE html>")
expect(html).to_contain("<title>SimpleOS Web WM</title>")
expect(html).to_contain("<div id=\"wm-desktop\"></div>")
expect(html).to_contain("<div id=\"wm-taskbar\"></div>")
expect(html).to_contain("WM WebSocket connected")
expect(html).to_contain("scheduleReconnect()")
```

</details>


</details>

<details>
<summary>Advanced: sets root WM token attributes on live pages</summary>

#### sets root WM token attributes on live pages _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = generate_wm_html_page("glass_obsidian_dark", "SimpleOS Web WM", 3333)
expect(html).to_contain("data-wm-theme=\"glass_obsidian_dark\"")
expect(html).to_contain("data-wm-icon-mask=\"circle\"")
expect(html).to_contain("data-wm-accent=\"blue\"")
expect(html).to_contain("data-wm-corner-radius=\"round\"")
```

</details>


</details>

### web WM runtime assets

<details>
<summary>Advanced: serves retained renderer as a browser module</summary>

#### serves retained renderer as a browser module _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = rt_file_read_text("src/app/ui.web/server.spl")
expect(server).to_contain("\"/retained_renderer.js\"")
expect(server).to_contain("src/app/ui.web/retained_renderer.js")
expect(server).to_contain("Content-Type: application/javascript")
```

</details>


</details>

<details>
<summary>Advanced: boot script can call the WM message handler</summary>

#### boot script can call the WM message handler _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = rt_file_read_text("src/app/ui.web/wm.js")
expect(wm).to_contain("handleMessage(frame)")
expect(wm).to_contain("this.receiveFrame(frame)")
```

</details>


</details>

<details>
<summary>Advanced: MDI drag and resize update real browser windows immediately</summary>

#### MDI drag and resize update real browser windows immediately _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wm = rt_file_read_text("src/app/ui.web/wm.js")
expect(wm).to_contain("ds.winEl.style.left")
expect(wm).to_contain("ds.winEl.style.top")
expect(wm).to_contain("rs.winEl.style.width")
expect(wm).to_contain("rs.winEl.style.height")
```

</details>


</details>

<details>
<summary>Advanced: retained renderer applies root props and icons</summary>

#### retained renderer applies root props and icons _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = rt_file_read_text("src/app/ui.web/retained_renderer.js")
expect(renderer).to_contain("key === 'class'")
expect(renderer).to_contain("key === 'style'")
expect(renderer).to_contain("props.width ?? props.w")
expect(renderer).to_contain("surface.icon || surface.app_icon || props.icon || props.app_icon || props.image")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/web_api_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- generate_html_page
- generate_css
- generate_js
- generate_wm_js
- generate_wm_html_page
- web WM runtime assets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 16 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
