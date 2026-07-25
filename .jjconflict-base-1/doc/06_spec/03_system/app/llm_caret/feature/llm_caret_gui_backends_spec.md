# Llm Caret Gui Backends Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Caret Gui Backends Specification

## Scenarios

### LLM Caret Electron and pure-Simple Metal GUI backends

#### REQ-002 and REQ-006 submit test to the dummy provider

- var state = caret native state
- state = caret native key
   - Expected: submitted.submit_prompt equals `test`
   - Expected: final_state.assistant equals `hello`


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

#### REQ-004 lowers semantic Caret HTML through Draw IR

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
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

**Screenshots:**
`doc/06_spec/image/03_system/app/llm_caret/feature/llm_caret_gui_backends/electron_test_hello.png`
records the live Electron `test` → `hello` interaction.

## Overview

Tests covering:
- LLM Caret Electron and pure-Simple Metal GUI backends

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
