# Mcp Sdk Server Facade Specification

> Tests covering nogc_async_mut mcp sdk server facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Sdk Server Facade Specification

## Scenarios

### nogc_async_mut mcp sdk server facade

#### re-exports builder, pagination, method detection, and router helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports builder, pagination, method detection, and router helpers
   - Expected: cfg.info.name equals `simple`
   - Expected: server_tool_count(cfg) equals `1`
   - Expected: parse_cursor("offset:5") equals `5`
   - Expected: make_cursor(10) equals `offset:10`
   - Expected: has_method(msg, "tools/list") is true
   - Expected: detect_method(msg, ["initialize", "tools/list"]) equals `tools/list`
   - Expected: dispatch_method(cfg, "tools/call", "1") equals `DISPATCH_TOOL`
   - Expected: handle_method(cfg, "resources/read", "1", "{}") equals `RESOURCES_READ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports builder, pagination, method detection, and router helpers")
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

- re-exports protocol state helpers
   - Expected: state_has_progress("tok") is true
   - Expected: state_has_progress("tok") is false
   - Expected: state_is_cancelled("req") is true
   - Expected: state_is_cancelled("req") is false
   - Expected: state_is_subscribed("file://a") is true
   - Expected: state_is_subscribed("file://a") is false
   - Expected: state_get_log_level() equals `3`
   - Expected: state_should_emit_log(4) is true
   - Expected: state_next_request_id() equals `srv-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports protocol state helpers")
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
| Source | `test/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut mcp sdk server facade.
- nogc_async_mut mcp sdk server facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b39af9898c6d90f96745899646fb4b57ce2c4d1b4a3f9065d3c630dfce028787`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b39af9898c6d90f96745899646fb4b57ce2c4d1b4a3f9065d3c630dfce028787`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b39af9898c6d90f96745899646fb4b57ce2c4d1b4a3f9065d3c630dfce028787`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports builder, pagination, method detection, and router helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/mcp_sdk/server/mcp_sdk_server_facade_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports protocol state helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
