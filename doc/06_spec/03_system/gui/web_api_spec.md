# Web Api Specification

> Tests covering generate_html_page, generate_css, generate_js, generate_wm_js, generate_wm_html_page, web WM runtime assets.

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces a full HTML page from demo.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces a full HTML page from demo.ui.sdn")
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

- produces a full HTML page from minimal.ui.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces a full HTML page from minimal.ui.sdn")
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

- dark theme contains dark background color


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dark theme contains dark background color")
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

- light theme contains light background color


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("light theme contains light background color")
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

- dark and light themes produce different output
   - Expected: dark_css != light_css is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dark and light themes produce different output")
val dark_css = generate_css("dark")
val light_css = generate_css("light")
expect(dark_css != light_css).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: glass obsidian theme serializes real CSS color values</summary>

#### glass obsidian theme serializes real CSS color values _(slow)_

- glass obsidian theme serializes real CSS color values
   - Expected: css does not contain `Object { class`
   - Expected: css does not contain `+ WM_TRAFFIC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("glass obsidian theme serializes real CSS color values")
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

- produces WebSocket connection code


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces WebSocket connection code")
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

- uses correct port in WebSocket URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses correct port in WebSocket URL")
val js = generate_js(9999)
expect(js).to_contain("9999")
```

</details>


</details>

### generate_wm_js

<details>
<summary>Advanced: boots immediately when the document is already loaded</summary>

#### boots immediately when the document is already loaded _(slow)_

- boots immediately when the document is already loaded


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots immediately when the document is already loaded")
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

- retries stalled or errored websocket connections


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retries stalled or errored websocket connections")
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

- produces the SimpleOS WM shell scaffold


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces the SimpleOS WM shell scaffold")
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

- sets root WM token attributes on live pages


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets root WM token attributes on live pages")
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

- serves retained renderer as a browser module


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serves retained renderer as a browser module")
val server = file_read_text("src/app/ui.web/server.spl")
expect(server).to_contain("\"/retained_renderer.js\"")
expect(server).to_contain("src/app/ui.web/retained_renderer.js")
expect(server).to_contain("Content-Type: application/javascript")
```

</details>


</details>

<details>
<summary>Advanced: boot script can call the WM message handler</summary>

#### boot script can call the WM message handler _(slow)_

- boot script can call the WM message handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot script can call the WM message handler")
val wm = file_read_text("src/app/ui.web/wm.js")
expect(wm).to_contain("handleMessage(frame)")
expect(wm).to_contain("this.receiveFrame(frame)")
```

</details>


</details>

<details>
<summary>Advanced: MDI drag and resize update real browser windows immediately</summary>

#### MDI drag and resize update real browser windows immediately _(slow)_

- MDI drag and resize update real browser windows immediately


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("MDI drag and resize update real browser windows immediately")
val wm = file_read_text("src/app/ui.web/wm.js")
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

- retained renderer applies root props and icons


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retained renderer applies root props and icons")
val renderer = file_read_text("src/app/ui.web/retained_renderer.js")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering generate_html_page, generate_css, generate_js, generate_wm_js, generate_wm_html_page, web WM runtime assets.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc8691512bdad4abddfc55c27a656b70ece9c3b614f9f6885c3dcf55b67c1d26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc8691512bdad4abddfc55c27a656b70ece9c3b614f9f6885c3dcf55b67c1d26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc8691512bdad4abddfc55c27a656b70ece9c3b614f9f6885c3dcf55b67c1d26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/web_api_spec.spl
mirror: doc/06_spec/03_system/gui/web_api_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/web_api_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/web_api_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/web_api_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a full HTML page from demo.ui.sdn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_api_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a full HTML page from minimal.ui.sdn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/web_api_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dark theme contains dark background color' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
