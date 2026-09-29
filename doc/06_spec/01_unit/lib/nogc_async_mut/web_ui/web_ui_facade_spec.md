# Web UI Facade Re-export Specification

> Verifies that the `nogc_async_mut.web_ui` facade exposes the pure application state, payload, command registry, event bus, input, plugin, bridge, DOM, and window helpers needed by native web UI integrations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web UI Facade Re-export Specification

Verifies that the `nogc_async_mut.web_ui` facade exposes the pure application state, payload, command registry, event bus, input, plugin, bridge, DOM, and window helpers needed by native web UI integrations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WEB-UI-FACADE-001 |
| Category | Web UI |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the `nogc_async_mut.web_ui` facade exposes the pure application
state, payload, command registry, event bus, input, plugin, bridge, DOM, and
window helpers needed by native web UI integrations.

## Syntax

The spec constructs facade values directly and checks observable state rather
than using tautological match arms.

## Examples

`Payload.empty()` creates a mutable payload map whose duplicate key updates keep
the key count stable and return the latest value.

## Scenarios

### nogc_async_mut web_ui facade

#### re-exports pure web_ui data and registry helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports pure web_ui data and registry helpers
   - Expected: payload.len() equals `2`
   - Expected: payload.keys().len() equals `2`
   - Expected: app_state_name equals `running`
   - Expected: commands.command_count() equals `0`
   - Expected: commands.has_command("missing") is false
   - Expected: commands.js_invoke_shim() contains `__web_ui_invoke`
   - Expected: NATIVE_WEB_UI_INVOKE equals `-800`
   - Expected: bus.listener_count() equals `0`
   - Expected: input.mouse_x equals `0`
   - Expected: input.mouse_down is false
   - Expected: event_name equals `close-requested`
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

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports pure web_ui data and registry helpers")
var payload = Payload.empty()
payload.set("name", "simple")
payload.set("mode", "async")
payload.set("mode", "nogc")
expect(payload.len()).to_equal(2)
expect(payload.keys().len()).to_equal(2)
match payload.get("mode"):
    Some(value): expect(value).to_equal("nogc")
    nil: expect("").to_equal("nogc")

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6d1d7da27e190b8f605c0629457f15e6f274dfc5bfb613ac4b954fd814aca54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6d1d7da27e190b8f605c0629457f15e6f274dfc5bfb613ac4b954fd814aca54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6d1d7da27e190b8f605c0629457f15e6f274dfc5bfb613ac4b954fd814aca54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports pure web_ui data and registry helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
