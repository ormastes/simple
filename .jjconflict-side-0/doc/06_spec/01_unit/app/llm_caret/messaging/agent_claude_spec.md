# agent_claude_spec

> Claude hooks enqueue normalized lifecycle state without external calls.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# agent_claude_spec

Claude hooks enqueue normalized lifecycle state without external calls.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/agent_claude_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Claude hooks enqueue normalized lifecycle state without external calls.

## Scenarios

### Claude AgentControl adapter

#### registers a stable session and normalizes hook transitions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers a stable session and normalizes hook transitions
   - Expected: session_id.starts_with("claude-builder-") is true
   - Expected: adapter.accept_hook(session_id, "UserPromptSubmit", "m1") equals `enqueued:running`
   - Expected: adapter.accept_hook(session_id, "PermissionRequest", "approve tool") equals `enqueued:waiting_input`
   - Expected: adapter.accept_hook(session_id, "Stop", "answer") equals `enqueued:completed`
   - Expected: adapter.registry.event_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("registers a stable session and normalizes hook transitions")
var adapter = ClaudeHooksAdapter.new()
val session_id = adapter.attach_session(binding())
expect(session_id.starts_with("claude-builder-")).to_equal(true)
expect(adapter.accept_hook(session_id, "UserPromptSubmit", "m1")).to_equal("enqueued:running")
expect(adapter.accept_hook(session_id, "PermissionRequest", "approve tool")).to_equal("enqueued:waiting_input")
expect(adapter.accept_hook(session_id, "Stop", "answer")).to_equal("enqueued:completed")
expect(adapter.registry.event_count()).to_equal(4)
```

</details>

#### fails closed for unknown hooks and unavailable sessions

- fails closed for unknown hooks and unavailable sessions
   - Expected: adapter.accept_hook("missing", "Stop", "answer") equals `error:session_unavailable`
   - Expected: adapter.accept_hook(session_id, "UntrustedHook", "payload") equals `error:unknown_claude_hook`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for unknown hooks and unavailable sessions")
var adapter = ClaudeHooksAdapter.new()
expect(adapter.accept_hook("missing", "Stop", "answer")).to_equal("error:session_unavailable")
val session_id = adapter.attach_session(binding())
expect(adapter.accept_hook(session_id, "UntrustedHook", "payload")).to_equal("error:unknown_claude_hook")
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

- Canonical SPipe generation for source `3c0a49b14ce6ee0773d93586adf582c0e29b5cd59b75ffe2e8e66ee51018f3f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c0a49b14ce6ee0773d93586adf582c0e29b5cd59b75ffe2e8e66ee51018f3f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c0a49b14ce6ee0773d93586adf582c0e29b5cd59b75ffe2e8e66ee51018f3f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/agent_claude_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/agent_claude_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/agent_claude_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/agent_claude_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/agent_claude_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/messaging/agent_claude_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/agent_claude_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers a stable session and normalizes hook transitions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/agent_claude_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for unknown hooks and unavailable sessions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
