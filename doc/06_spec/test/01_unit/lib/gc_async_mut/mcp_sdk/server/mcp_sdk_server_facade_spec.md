# Mcp Sdk Server Facade Specification

> 1. var cfg = server config

<!-- sdn-diagram:id=mcp_sdk_server_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_sdk_server_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_sdk_server_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_sdk_server_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Sdk Server Facade Specification

## Scenarios

### gc_async_mut mcp sdk server facade

#### re-exports builder, pagination, method detection, and router helpers

1. var cfg = server config
   - Expected: cfg.info.name equals `simple`
2. cfg = server add tool json
   - Expected: server_tool_count(cfg) equals `1`
   - Expected: parse_cursor("offset:5") equals `5`
   - Expected: make_cursor(10) equals `offset:10`
   - Expected: has_method(msg, "tools/list") is true
   - Expected: detect_method(msg, ["initialize", "tools/list"]) equals `tools/list`
3. router clear caches
   - Expected: dispatch_method(cfg, "tools/call", "1") equals `DISPATCH_TOOL`
   - Expected: handle_method(cfg, "resources/read", "1", "{}") equals `RESOURCES_READ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cfg = server_config("simple", "1.0")
expect(cfg.info.name).to_equal("simple")
cfg = server_add_tool_json(cfg, "ping", "{\"name\":\"ping\"}")
expect(server_tool_count(cfg)).to_equal(1)
expect(server_build_tools_list(cfg)).to_contain("\"ping\"")

expect(parse_cursor("offset:5")).to_equal(5)
expect(make_cursor(10)).to_equal("offset:10")
expect(paginate_items(["\"a\"", "\"b\""], "", 1)).to_contain("nextCursor")
expect(paginate_tools_response("1", ["{\"name\":\"a\"}"], "", 10)).to_contain("\"tools\"")

val msg = "{\"jsonrpc\":\"2.0\",\"method\":\"tools/list\",\"id\":1}"
expect(has_method(msg, "tools/list")).to_equal(true)
expect(detect_method(msg, ["initialize", "tools/list"])).to_equal("tools/list")
router_clear_caches()
expect(dispatch_method(cfg, "tools/call", "1")).to_equal("DISPATCH_TOOL")
expect(handle_method(cfg, "resources/read", "1", "{}")).to_equal("RESOURCES_READ")
```

</details>

#### re-exports protocol state helpers

1. state reset
2. state register progress
   - Expected: state_has_progress("tok") is true
3. state remove progress
   - Expected: state_has_progress("tok") is false
4. state cancel request
   - Expected: state_is_cancelled("req") is true
5. state clear cancelled
   - Expected: state_is_cancelled("req") is false
6. state subscribe
   - Expected: state_is_subscribed("file://a") is true
7. state unsubscribe
   - Expected: state_is_subscribed("file://a") is false
8. state set log level
   - Expected: state_get_log_level() equals `3`
   - Expected: state_should_emit_log(4) is true
   - Expected: state_next_request_id() equals `srv-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
state_reset()
state_register_progress("tok", "req")
expect(state_has_progress("tok")).to_equal(true)
state_remove_progress("tok")
expect(state_has_progress("tok")).to_equal(false)

state_cancel_request("req", "stop")
expect(state_is_cancelled("req")).to_equal(true)
state_clear_cancelled("req")
expect(state_is_cancelled("req")).to_equal(false)

state_subscribe("file://a")
expect(state_is_subscribed("file://a")).to_equal(true)
state_unsubscribe("file://a")
expect(state_is_subscribed("file://a")).to_equal(false)

state_set_log_level(log_level_to_int("warning"))
expect(state_get_log_level()).to_equal(3)
expect(state_should_emit_log(4)).to_equal(true)
expect(state_next_request_id()).to_equal("srv-1")
expect(make_progress_notification("tok", 1, 2, "half")).to_contain("notifications/progress")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut mcp sdk server facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
