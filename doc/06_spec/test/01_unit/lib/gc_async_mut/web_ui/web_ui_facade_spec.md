# Web Ui Facade Specification

> 1. var payload = Payload empty

<!-- sdn-diagram:id=web_ui_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_ui_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_ui_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_ui_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Ui Facade Specification

## Scenarios

### gc_async_mut web_ui facade

#### re-exports pure web_ui data and registry helpers

1. var payload = Payload empty
2. payload set
3. payload set
4. payload set
   - Expected: payload.len() equals `2`
   - Expected: payload.keys().len() equals `2`
   - Expected: app_state_name equals `running`
5. var commands = CommandRegistry create
   - Expected: commands.command_count() equals `0`
   - Expected: commands.has_command("missing") is false
   - Expected: commands.js_invoke_shim() contains `__web_ui_invoke`
   - Expected: NATIVE_WEB_UI_INVOKE equals `-800`
6. var bus = EventBus create
   - Expected: bus.listener_count() equals `0`
7. var input = InputBridge create
   - Expected: input.mouse_x equals `0`
   - Expected: input.mouse_down is false
   - Expected: event_name equals `close-requested`
8. var allowed payload = Payload empty
9. allowed payload set
   - Expected: fs.is_path_allowed("/tmp/web-ui.txt") is true
   - Expected: fs.is_path_allowed("/etc/passwd") is false
   - Expected: plugins.plugin_count() equals `0`
   - Expected: config.title equals `WebUI App`
   - Expected: config.width equals `800`
   - Expected: config.target_fps equals `60`
   - Expected: pack_rgba(1, 2, 3, 4) equals `16909060`
   - Expected: attr.name equals `id`
   - Expected: attr.value equals `root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var payload = Payload.empty()
payload.set("name", "simple")
payload.set("mode", "async")
payload.set("mode", "gc")
expect(payload.len()).to_equal(2)
expect(payload.keys().len()).to_equal(2)
match payload.get("mode"):
    Some(value): expect(value).to_equal("gc")
    nil: expect("").to_equal("gc")

match CommandResult.Ok(value: "done"):
    CommandResult.Ok(value): expect(value).to_equal("done")
    CommandResult.Err(message): expect(message).to_equal("")
var app_state_name = "unexpected"
match AppState.Running:
    AppState.Running: app_state_name = "running"
    _: app_state_name = "not-running"
expect(app_state_name).to_equal("running")

var commands = CommandRegistry.create()
expect(commands.command_count()).to_equal(0)
expect(commands.has_command("missing")).to_equal(false)
expect(commands.js_invoke_shim().contains("__web_ui_invoke")).to_equal(true)
expect(NATIVE_WEB_UI_INVOKE).to_equal(-800)

var bus = EventBus.create()
expect(bus.listener_count()).to_equal(0)

var input = InputBridge.create()
expect(input.mouse_x).to_equal(0)
expect(input.mouse_down).to_equal(false)
var event_name = "unexpected"
match WebUIEvent.CloseRequested:
    WebUIEvent.CloseRequested: event_name = "close-requested"
    _: event_name = "not-close-requested"
expect(event_name).to_equal("close-requested")

var allowed_payload = Payload.empty()
allowed_payload.set("/tmp", "allowed")
val fs = FsPlugin.create(allowed_payload.keys())
expect(fs.is_path_allowed("/tmp/web-ui.txt")).to_equal(true)
expect(fs.is_path_allowed("/etc/passwd")).to_equal(false)
val plugins = PluginRegistry.create()
expect(plugins.plugin_count()).to_equal(0)

val config = AppConfig.default_config()
expect(config.title).to_equal("WebUI App")
expect(config.width).to_equal(800)
expect(config.target_fps).to_equal(60)

expect(pack_rgba(1, 2, 3, 4)).to_equal(16909060)

val attr = WebUiAttr.create("id", "root")
expect(attr.name).to_equal("id")
expect(attr.value).to_equal("root")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/web_ui/web_ui_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut web_ui facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
