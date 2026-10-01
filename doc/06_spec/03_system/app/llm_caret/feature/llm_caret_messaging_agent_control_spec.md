# llm_caret_messaging_agent_control_spec

> The composition root owns provider-neutral agent session control.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_caret_messaging_agent_control_spec

The composition root owns provider-neutral agent session control.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The composition root owns provider-neutral agent session control.

## Scenarios

### LLM Caret agent-control composition

#### attaches, injects context, submits, steers, and cancels every provider

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- attaches, injects context, submits, steers, and cancels every provider
- Control the " + provider + " session through the shared application boundary
   - Expected: attached.ok is true
   - Expected: runtime.inject_agent_context(provider, attached.session_id, "context-1").ok is true
   - Expected: runtime.submit_agent_task(provider, attached.session_id, "task-1").ok is true
   - Expected: runtime.steer_agent_task(provider, attached.session_id, "task-2").ok is true
   - Expected: runtime.cancel_agent_task(provider, attached.session_id, "task-2").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaches, injects context, submits, steers, and cancels every provider")
var runtime = MessagingRuntime.memory()
for provider in ["claude", "codex", "gemini"]:
    step("Control the " + provider + " session through the shared application boundary")
    val attached = runtime.attach_agent(provider, binding(provider))
    expect(attached.ok).to_equal(true)
    expect(runtime.inject_agent_context(provider, attached.session_id, "context-1").ok).to_equal(true)
    expect(runtime.submit_agent_task(provider, attached.session_id, "task-1").ok).to_equal(true)
    expect(runtime.steer_agent_task(provider, attached.session_id, "task-2").ok).to_equal(true)
    expect(runtime.cancel_agent_task(provider, attached.session_id, "task-2").ok).to_equal(true)
runtime.close()
```

</details>

#### normalizes provider lifecycle events and rejects unknown providers

- normalizes provider lifecycle events and rejects unknown providers
   - Expected: runtime.accept_agent_event("claude", claude.session_id, "PermissionRequest", "approval").evidence equals `enqueued:waiting_input`
   - Expected: runtime.accept_agent_event("codex", codex.session_id, "turn/completed", "done").evidence equals `enqueued:completed`
   - Expected: runtime.accept_agent_event("gemini", gemini.session_id, "BeforeAgent", "context-2").evidence equals `context_accepted:context-2`
   - Expected: runtime.attach_agent("other", binding("other")).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normalizes provider lifecycle events and rejects unknown providers")
var runtime = MessagingRuntime.memory()
val claude = runtime.attach_agent("claude", binding("claude"))
expect(runtime.accept_agent_event("claude", claude.session_id, "PermissionRequest", "approval").evidence).to_equal("enqueued:waiting_input")
val codex = runtime.attach_agent("codex", binding("codex"))
expect(runtime.accept_agent_event("codex", codex.session_id, "turn/completed", "done").evidence).to_equal("enqueued:completed")
val gemini = runtime.attach_agent("gemini", binding("gemini"))
expect(runtime.accept_agent_event("gemini", gemini.session_id, "BeforeAgent", "context-2").evidence).to_equal("context_accepted:context-2")
expect(runtime.attach_agent("other", binding("other")).ok).to_equal(false)
runtime.close()
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

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-MSG-006`
- `REQ-LLM-MSG-007`
- `REQ-LLM-MSG-008`
- `REQ-LLM-MSG-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bbbf4b7d7830958d71434fe8809026fdc329b8d35179aa3860451fd39f3ded2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bbbf4b7d7830958d71434fe8809026fdc329b8d35179aa3860451fd39f3ded2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bbbf4b7d7830958d71434fe8809026fdc329b8d35179aa3860451fd39f3ded2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attaches, injects context, submits, steers, and cancels every provider' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalizes provider lifecycle events and rejects unknown providers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
