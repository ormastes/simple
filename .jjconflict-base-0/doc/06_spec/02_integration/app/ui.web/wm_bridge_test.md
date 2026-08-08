# Wm Bridge Test Specification

> <details>

<!-- sdn-diagram:id=wm_bridge_test.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_bridge_test.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_bridge_test -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_bridge_test.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Bridge Test Specification

## Scenarios

### wm_bridge window command contracts

#### creates host surfaces as SimpleWeb bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(WM_BRIDGE_PATH)
expect(source).to_contain("\"create\":")
expect(source).to_contain("bind_window_surface_with_kind(eff_id, eff_id, 0u64, \"host.window\", eff_title, UI_SURFACE_KIND_SIMPLE_WEB)")
expect(source).to_contain("self.session.set_active_surface(eff_id)")
```

</details>

#### resolves window_id_hint through the surface registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(WM_BRIDGE_PATH)
expect(source).to_contain("val hinted = _extract_text_field(payload_json, \"window_id_hint\")")
expect(source).to_contain("val by_window = session.window_surfaces.for_window(hinted)")
expect(source).to_contain("by_window.surface_id")
```

</details>

#### applies move resize and title updates back into the surface tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(WM_BRIDGE_PATH)
expect(source).to_contain("set_surface_widget_prop(surface_id, root_id, \"x\", ")
expect(source).to_contain("set_surface_widget_prop(surface_id, root_id, \"y\", ")
expect(source).to_contain("set_surface_widget_prop(surface_id, root_id, \"width\", ")
expect(source).to_contain("set_surface_widget_prop(surface_id, root_id, \"height\", ")
expect(source).to_contain("set_surface_widget_prop(surface_id, root_id, \"title\", title)")
expect(source).to_contain("update_window_surface_title(surface_id, title)")
```

</details>

### wm_bridge input contracts

#### writes text_input payloads through to the target widget value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(WM_BRIDGE_PATH)
expect(source).to_contain("if kind == \"text_input\":")
expect(source).to_contain("self.session.set_active_surface(surface_id)")
expect(source).to_contain("self.session.set_surface_widget_value(surface_id, widget_id, value)")
```

</details>

#### browser bridge forwards canonical widget pointer and text input events

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(WM_JS_PATH)
expect(source).to_contain("document.addEventListener('pointerdown'")
expect(source).to_contain("document.addEventListener('pointerup'")
expect(source).to_contain("document.addEventListener('pointermove'")
expect(source).to_contain("document.addEventListener('input'")
expect(source).to_contain("const widget = e.target.closest('[data-canonical-id]')")
expect(source).to_contain("const hash = cid.indexOf('#')")
expect(source).to_contain("kind: 'pointer_down'")
expect(source).to_contain("kind: 'pointer_up'")
expect(source).to_contain("kind: 'pointer_move'")
expect(source).to_contain("kind: 'text_input'")
expect(source).to_contain("text: e.target.value ?? e.data ?? ''")
```

</details>

#### browser bridge routes MDI titlebar drag into focus and move commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(WM_JS_PATH)
expect(source).to_contain("_onTitlebarMousedown(e, winEl)")
expect(source).to_contain("if (e.target.closest('.wm-traffic-lights')) return;")
expect(source).to_contain("this._sendWindowCmd('focus'")
expect(source).to_contain("this.dragState = {")
expect(source).to_contain("_onMousemove(e)")
expect(source).to_contain("_onMouseup(e)")
expect(source).to_contain("this._sendWindowCmd('move'")
expect(source).to_contain("window_id_hint: ds.surfaceId")
expect(source).to_contain("x: Math.round(newX)")
expect(source).to_contain("y: Math.round(newY)")
```

</details>

#### browser bridge routes titlebar buttons and title command input

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read_source(WM_JS_PATH)
expect(source).to_contain("const btn = e.target.closest('.wm-traffic-lights button')")
expect(source).to_contain("this._markTrafficCommandFeedback(btn, action)")
expect(source).to_contain("if      (action === 'close')    this._sendWindowCmd('close', commandPayload)")
expect(source).to_contain("else if (action === 'minimize') this._sendWindowCmd('minimize', commandPayload)")
expect(source).to_contain("else if (action === 'maximize') this._sendWindowCmd('maximize', commandPayload)")
expect(source).to_contain("_makeTitleCommandInput(payload = {})")
expect(source).to_contain("input.className = 'wm-title-input wm-command-bar'")
expect(source).to_contain("input.addEventListener('input', () => this._showTitleCommandSuggestions(input, true))")
expect(source).to_contain("this._sendWindowCmd('title_command'")
expect(source).to_contain("window_id_hint: win?.dataset.surfaceId || win?.dataset.canonicalId || ''")
```

</details>

### wm_bridge native host feedback contracts

#### routes native feedback through sync taskbar helpers and client actions through queued helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bridge_source = _read_source(WM_BRIDGE_PATH)
expect(bridge_source).to_contain("val native_feedback = _extract_text_field(payload_json, \"source\") == HOST_NATIVE_EVENT_SOURCE")
expect(bridge_source).to_contain("host_taskbar_runtime_sync_focus(self.session, surface_id)")
expect(bridge_source).to_contain("host_taskbar_runtime_focus(self.session, surface_id)")
expect(bridge_source).to_contain("host_taskbar_runtime_sync_minimize(self.session, surface_id)")
expect(bridge_source).to_contain("host_taskbar_runtime_minimize(self.session, surface_id)")
expect(bridge_source).to_contain("host_taskbar_runtime_sync_close(self.session, surface_id)")
expect(bridge_source).to_contain("host_taskbar_runtime_close(self.session, surface_id)")
```

</details>

#### keeps taskbar runtime focus minimize title and geometry sync behavior aligned

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val taskbar_source = _read_taskbar_runtime_source()
expect(taskbar_source).to_contain("fn host_taskbar_runtime_sync_focus(session: UISession, surface_id: text) -> Result<Unit, text>:")
expect(taskbar_source).to_contain("session.set_active_surface(surface_id)")
expect(taskbar_source).to_contain("fn host_taskbar_runtime_sync_minimize(session: UISession, surface_id: text) -> Result<Unit, text>:")
expect(taskbar_source).to_contain("rt.minimized_surface_ids = rt.minimized_surface_ids.push(surface_id)")
expect(taskbar_source).to_contain("fn host_taskbar_runtime_sync_move(session: UISession, surface_id: text, x: i32, y: i32) -> Result<Unit, text>:")
expect(taskbar_source).to_contain("fn host_taskbar_runtime_sync_resize(session: UISession, surface_id: text, width: i32, height: i32) -> Result<Unit, text>:")
expect(taskbar_source).to_contain("fn host_taskbar_runtime_sync_set_title(session: UISession, surface_id: text, title: text) -> Result<Unit, text>:")
expect(taskbar_source).to_contain("session.update_window_surface_title(surface_id, title)")
```

</details>

#### uses the native_event host adapter marker in feedback payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter_source = _read_source(HOST_ADAPTER_CONTRACT_PATH)
expect(adapter_source).to_contain("val HOST_NATIVE_EVENT_SOURCE: text = \"native_event\"")
expect(adapter_source).to_contain("val base = ")
expect(adapter_source).to_contain("window_id_hint")
expect(adapter_source).to_contain("HOST_NATIVE_EVENT_SOURCE")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/ui.web/wm_bridge_test.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wm_bridge window command contracts
- wm_bridge input contracts
- wm_bridge native host feedback contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
