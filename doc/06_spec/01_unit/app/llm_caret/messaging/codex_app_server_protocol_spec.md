# Codex App Server Protocol Specification

> Tests covering Codex App Server v2 messaging protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codex App Server Protocol Specification

## Scenarios

### Codex App Server v2 messaging protocol

#### builds initialize and thread requests as newline-safe JSON-RPC bodies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds initialize and thread requests as newline-safe JSON-RPC bodies
- Encode the negotiated client identity and durable thread operations
   - Expected: codex_thread_resume_params("thread-1") equals `{"threadId":"thread-1"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("builds initialize and thread requests as newline-safe JSON-RPC bodies")
step("Encode the negotiated client identity and durable thread operations")
val init = codex_rpc_request(1, "initialize", codex_initialize_params())
expect(init).to_contain("\"jsonrpc\":\"2.0\"")
expect(init).to_contain("\"method\":\"initialize\"")
expect(init).to_contain("llm-caret-messaging")
expect(codex_thread_resume_params("thread-1")).to_equal("{\"threadId\":\"thread-1\"}")
val injected = codex_thread_inject_items_params("thread-1", "room context\nnext")
expect(injected).to_contain("\"threadId\":\"thread-1\"")
expect(injected).to_contain("input_text")
expect(injected).to_contain("room context\\nnext")
```

</details>

#### uses current turn start steer and interrupt preconditions

- uses current turn start steer and interrupt preconditions
- Encode structured input and the active-turn steering precondition


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses current turn start steer and interrupt preconditions")
step("Encode structured input and the active-turn steering precondition")
val start = codex_turn_start_params("thread-1", "implement it", "message-1")
expect(start).to_contain("\"input\":[{\"type\":\"text\"")
expect(start).to_contain("\"clientUserMessageId\":\"message-1\"")
val steer = codex_turn_steer_params("thread-1", "turn-7", "add tests", "message-2")
expect(steer).to_contain("\"expectedTurnId\":\"turn-7\"")
expect(steer).to_contain("add tests")
expect(codex_turn_interrupt_params("thread-1", "turn-7")).to_equal(
    "{\"threadId\":\"thread-1\",\"turnId\":\"turn-7\"}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Codex App Server v2 messaging protocol.
- Codex App Server v2 messaging protocol

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

- `REQ-SSPEC-UNIT`
- `REQ-LLM-MSG-007`
- `REQ-LLM-MSG-013`
- `REQ-LLM-MSG-014`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f818a4f8f68878aebc660cbc3945f0280d4509652e90e0d343f28744ae5d4971`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f818a4f8f68878aebc660cbc3945f0280d4509652e90e0d343f28744ae5d4971`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f818a4f8f68878aebc660cbc3945f0280d4509652e90e0d343f28744ae5d4971`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds initialize and thread requests as newline-safe JSON-RPC bodies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/codex_app_server_protocol_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses current turn start steer and interrupt preconditions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
