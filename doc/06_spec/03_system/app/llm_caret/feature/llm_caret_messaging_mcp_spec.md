# LLM Caret Messaging MCP

> This executable manual verifies the dedicated stdio MCP protocol registration and an end-to-end private-room send/read flow through canonical PureDatabase messaging semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Messaging MCP

This executable manual verifies the dedicated stdio MCP protocol registration and an end-to-end private-room send/read flow through canonical PureDatabase messaging semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-LLM-MSG-003, REQ-LLM-MSG-013, REQ-LLM-MSG-015, |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_mcp_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations


## Overview

This executable manual verifies the dedicated stdio MCP protocol registration
and an end-to-end private-room send/read flow through canonical PureDatabase
messaging semantics.

**Requirements:** REQ-LLM-MSG-003, REQ-LLM-MSG-013, REQ-LLM-MSG-015,
REQ-LLM-MSG-016

## Scenarios

### LLM Caret dedicated messaging MCP

#### advertises the complete canonical chat tool set with JSON schemas

- Verify: advertises the complete canonical chat tool set with JSON schemas
- Discover the dedicated messaging MCP
   - Expected: listed does not contain `CREATE TABLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-003 REQ-LLM-MSG-013 REQ-LLM-MSG-015 REQ-LLM-MSG-016
step("Verify: advertises the complete canonical chat tool set with JSON schemas")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Discover the dedicated messaging MCP")
configure_test_mcp()
register_messaging_tools()
val listed = response("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/list\",\"params\":{}}")
expect(listed).to_contain("chat_join")
expect(listed).to_contain("chat_open_private")
expect(listed).to_contain("chat_publish_artifact")
expect(listed).to_contain("chat_get_context")
expect(listed).to_contain("\"inputSchema\":{\"type\":\"object\"")
expect(listed.contains("CREATE TABLE")).to_equal(false)
```

</details>

<details>
<summary>Advanced: opens a private room then sends and reads one canonical message</summary>

#### opens a private room then sends and reads one canonical message

- Verify: opens a private room then sends and reads one canonical message
- Create and bind a room
- Route a message to an agent
- Inject the bounded context bundle


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-003 REQ-LLM-MSG-013 REQ-LLM-MSG-015 REQ-LLM-MSG-016
step("Verify: opens a private room then sends and reads one canonical message")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Create and bind a room")
configure_test_mcp()
register_messaging_tools()
val opened = tool_call(2, "chat_open_private", "{\"workspace_id\":\"mcp-ws\",\"identity_id\":\"human-mcp\",\"target_identity_id\":\"agent-mcp\",\"room_id\":\"mcp-dm\",\"idempotency_key\":\"open-mcp-0001\",\"occurred_at\":10}")
expect(opened).to_contain("primitive_direct_room")
step("Route a message to an agent")
val sent = tool_call(3, "chat_send", "{\"workspace_id\":\"mcp-ws\",\"identity_id\":\"human-mcp\",\"room_id\":\"mcp-dm\",\"message_id\":\"mcp-msg-1\",\"body\":\"hello agent\",\"idempotency_key\":\"send-mcp-0001\",\"occurred_at\":11}")
expect(sent).to_contain("accepted")
step("Inject the bounded context bundle")
val read = tool_call(4, "chat_read", "{\"workspace_id\":\"mcp-ws\",\"identity_id\":\"human-mcp\",\"room_id\":\"mcp-dm\",\"after_seq\":0,\"limit\":10,\"occurred_at\":12}")
expect(read).to_contain("canonical_history")
expect(read).to_contain("mcp-msg-1")
expect(read).to_contain("hello agent")
```

</details>


</details>

#### rejects caller-supplied workspace escalation beyond the local capability

- Verify: rejects caller-supplied workspace escalation beyond the local capability
- Observe task and receipt transitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-003 REQ-LLM-MSG-013 REQ-LLM-MSG-015 REQ-LLM-MSG-016
step("Verify: rejects caller-supplied workspace escalation beyond the local capability")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Observe task and receipt transitions")
configure_test_mcp()
register_messaging_tools()
val denied = tool_call(5, "chat_read", "{\"workspace_id\":\"other-workspace\",\"identity_id\":\"attacker\",\"room_id\":\"mcp-dm\",\"occurred_at\":12}")
expect(denied).to_contain("workspace_access_denied")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-LLM-MSG-003, REQ-LLM-MSG-013, REQ-LLM-MSG-015,`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `35fbfb1f572408644e9f862d7314df68cb3fc96712ee13f55e87670eda197743`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `35fbfb1f572408644e9f862d7314df68cb3fc96712ee13f55e87670eda197743`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `35fbfb1f572408644e9f862d7314df68cb3fc96712ee13f55e87670eda197743`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_mcp_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_mcp_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_mcp_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
