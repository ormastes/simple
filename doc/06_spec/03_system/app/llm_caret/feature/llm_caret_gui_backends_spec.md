# Llm Caret Gui Backends Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Caret Gui Backends Specification

## Scenarios

### LLM Caret Electron and pure-Simple Metal GUI backends

#### REQ-002 and REQ-006 submit test to the dummy provider

- Prepare the native Caret GUI state
- Submit the visible prompt through the dummy provider
- Check the rendered conversation state
  - Expected: submitted prompt equals `test`
  - Expected: assistant response equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = caret_native_state()
for key in [84, 69, 83, 84]:
    state = caret_native_key(state, key).state
val submitted = caret_native_key(state, 13)
expect(submitted.submit_prompt).to_equal("test")
val response = dispatch_send("dummy", submitted.submit_prompt, "", "", "", "", "", "", 0, 0, "[]")
val final_state = caret_native_apply_response(submitted.state, submitted.submit_prompt, response.content)
expect(final_state.assistant).to_equal("hello")
```

</details>

#### Launch the browser GUI and complete a visible dummy-provider turn

- Launch the provenance-qualified cached Caret browser GUI from an unrelated
  temporary working directory.
- Send `test` through its live loopback HTTP surface and require `hello`.
- Capture the visible browser window as `browser.png`.
- Require `case=browser-live status=PASS` and a zero exit status.

#### Launch Electron with the live Caret page

- Launch the cached Caret artifact with `--electron` from an unrelated
  temporary working directory, proving the wrapper's repository-root contract.
- Require the reported Electron child process to remain alive and its DevTools
  endpoint to identify the exact Caret loopback URL (a blank shell cannot pass).
- Submit `test` through the live Electron DOM and require the visible user and
  assistant nodes to contain `test` and `hello` in the retained DevTools proof.
- Capture the visible Electron window as `electron.png`.
- Require `case=electron-live status=PASS` and a zero exit status.

#### Launch the Metal companion and present device pixels

- Verify the separate `caret_metal` binary and source-bound provenance, then
  reach it through the public `bin/caret --metal-gui` wrapper route.
- Launch it with `SIMPLE_GUI=1`, focus the real Winit process, type `test`, and
  deliver Enter through macOS accessibility input.
- Require the production event log to record the `test`/`hello` submission.
- Require `backend=metal source=device_readback` while its Winit window lives.
- Capture the visible Metal window as `metal.png` and require a zero exit
  status.

#### Fail closed when live GUI prerequisites are absent

- Verify the cached core Caret artifact/runtime provenance.
- Require `nc`, macOS screen capture, Electron, and the provenance-qualified
  Metal companion.
- Any missing artifact, process, response, backend marker, or non-empty capture
  makes the scenario fail; no headless substitute is accepted.

#### REQ-004 lowers semantic Caret HTML through Draw IR

- Prepare semantic Caret HTML
- Lower the GUI surface through Draw IR
- Check the retained Draw IR evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = caret_gui_native_html("", "test", "hello", "metal", "connected")
expect(html).to_contain("You: test")
expect(html).to_contain("Assistant: hello")
val composition = simple_web_layout_render_html_draw_ir(html, 480, 320)
expect(composition.scene_key).to_equal("simple-web-html-layout")
expect(composition.batches.len()).to_be_greater_than(0)
expect(composition.batches[0].source.source_kind).to_equal("html_ast")
expect(composition.batches[0].commands.len()).to_be_greater_than(0)
```

</details>

#### REQ-005 exposes explicit Metal and accessibility semantics

- Prepare the Metal GUI semantic surface
- Inspect backend and accessibility attributes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = caret_gui_native_html("test", "", "", "metal", "connected")
expect(html).to_contain("aria-label=\"LLM Caret native chat\"")
expect(html).to_contain("data-backend=\"metal\"")
expect(html).to_contain("Message LLM Caret: test")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_gui_backends_spec.spl` |
| Updated | 2026-09-04 |
| Generator | `simple spipe-docgen` (Simple) |

**Live-launch boundary:** The four live scenarios now execute the production
launch checker, but remain red until the core and Metal artifacts, Electron,
and actual captures exist. Source-level HTML/Draw-IR scenarios cannot satisfy
those live scenarios. Captures are retained under
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_gui_live/`.

## Overview

Tests covering:
- LLM Caret Electron and pure-Simple Metal GUI backends

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
