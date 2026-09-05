# agent_codex_spec

> Codex uses App Server operations and an explicit local hook fallback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# agent_codex_spec

Codex uses App Server operations and an explicit local hook fallback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/agent_codex_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Codex uses App Server operations and an explicit local hook fallback.

## Scenarios

### Codex AgentControl adapter

#### maps operations to App Server turn and thread methods

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps operations to App Server turn and thread methods
   - Expected: adapter.operation("turn/start", "s1", "m1") equals `enqueue:codex-app-server:turn/start:s1:m1`
   - Expected: adapter.operation("turn/steer", "s1", "m2") equals `enqueue:codex-app-server:turn/steer:s1:m2`
   - Expected: adapter.operation("turn/interrupt", "s1", "t1") equals `enqueue:codex-app-server:turn/interrupt:s1:t1`
   - Expected: adapter.operation("thread/inject_items", "s1", "ctx1") equals `enqueue:codex-app-server:thread/inject_items:s1:ctx1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps operations to App Server turn and thread methods")
val adapter = CodexAppServerAdapter.new(true)
expect(adapter.operation("turn/start", "s1", "m1")).to_equal("enqueue:codex-app-server:turn/start:s1:m1")
expect(adapter.operation("turn/steer", "s1", "m2")).to_equal("enqueue:codex-app-server:turn/steer:s1:m2")
expect(adapter.operation("turn/interrupt", "s1", "t1")).to_equal("enqueue:codex-app-server:turn/interrupt:s1:t1")
expect(adapter.operation("thread/inject_items", "s1", "ctx1")).to_equal("enqueue:codex-app-server:thread/inject_items:s1:ctx1")
```

</details>

#### uses hook fallback and rejects unknown notifications

- uses hook fallback and rejects unknown notifications
   - Expected: adapter.operation("turn/start", "s1", "m1") equals `enqueue:codex-hook-fallback:turn/start:s1:m1`
   - Expected: adapter.accept_notification(session_id, "turn/started", "t1") equals `enqueued:running`
   - Expected: adapter.accept_notification(session_id, "other/event", "x") equals `error:unknown_codex_notification`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses hook fallback and rejects unknown notifications")
var adapter = CodexAppServerAdapter.new(false)
expect(adapter.operation("turn/start", "s1", "m1")).to_equal("enqueue:codex-hook-fallback:turn/start:s1:m1")
val session_id = adapter.attach_session(binding())
expect(adapter.accept_notification(session_id, "turn/started", "t1")).to_equal("enqueued:running")
expect(adapter.accept_notification(session_id, "other/event", "x")).to_equal("error:unknown_codex_notification")
```

</details>

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
- `REQ-LLM-MSG-006`
- `REQ-LLM-MSG-007`
- `REQ-LLM-MSG-008`
- `REQ-LLM-MSG-014`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fcc74d451fb10e83f4cfa3a900f116572498bc0d8eedf5f8c607433561e8fa65`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fcc74d451fb10e83f4cfa3a900f116572498bc0d8eedf5f8c607433561e8fa65`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fcc74d451fb10e83f4cfa3a900f116572498bc0d8eedf5f8c607433561e8fa65`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/agent_codex_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/agent_codex_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/agent_codex_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/agent_codex_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/agent_codex_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/agent_codex_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps operations to App Server turn and thread methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/agent_codex_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses hook fallback and rejects unknown notifications' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
