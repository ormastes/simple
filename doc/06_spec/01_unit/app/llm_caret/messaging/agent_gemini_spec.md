# agent_gemini_spec

> Gemini hooks inject bounded context and normalize lifecycle events.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# agent_gemini_spec

Gemini hooks inject bounded context and normalize lifecycle events.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/agent_gemini_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Gemini hooks inject bounded context and normalize lifecycle events.

## Scenarios

### Gemini AgentControl adapter

#### injects BeforeAgent context and records terminal lifecycle state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- injects BeforeAgent context and records terminal lifecycle state
   - Expected: adapter.accept_hook(session_id, "BeforeAgent", "ctx-7") equals `context_accepted:ctx-7`
   - Expected: adapter.registry.session(session_id).context_manifest_id equals `ctx-7`
   - Expected: adapter.accept_hook(session_id, "AfterModel", "milestone") equals `enqueued:running`
   - Expected: adapter.accept_hook(session_id, "AfterAgent", "artifact-1") equals `enqueued:completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("injects BeforeAgent context and records terminal lifecycle state")
var adapter = GeminiHooksAdapter.new()
val session_id = adapter.attach_session(binding())
expect(adapter.accept_hook(session_id, "BeforeAgent", "ctx-7")).to_equal("context_accepted:ctx-7")
expect(adapter.registry.session(session_id).context_manifest_id).to_equal("ctx-7")
expect(adapter.accept_hook(session_id, "AfterModel", "milestone")).to_equal("enqueued:running")
expect(adapter.accept_hook(session_id, "AfterAgent", "artifact-1")).to_equal("enqueued:completed")
```

</details>

#### fails closed for empty context and unknown lifecycle hooks

- fails closed for empty context and unknown lifecycle hooks
   - Expected: adapter.accept_hook(session_id, "BeforeAgent", "") equals `error:context_rejected`
   - Expected: adapter.accept_hook(session_id, "Unknown", "x") equals `error:unknown_gemini_hook`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails closed for empty context and unknown lifecycle hooks")
var adapter = GeminiHooksAdapter.new()
val session_id = adapter.attach_session(binding())
expect(adapter.accept_hook(session_id, "BeforeAgent", "")).to_equal("error:context_rejected")
expect(adapter.accept_hook(session_id, "Unknown", "x")).to_equal("error:unknown_gemini_hook")
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

- Canonical SPipe generation for source `98ad03c489419c16f4aa3cb5e08654de3f71bf4ef0d8e25f175840f81b18c9b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `98ad03c489419c16f4aa3cb5e08654de3f71bf4ef0d8e25f175840f81b18c9b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `98ad03c489419c16f4aa3cb5e08654de3f71bf4ef0d8e25f175840f81b18c9b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/agent_gemini_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/agent_gemini_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/agent_gemini_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/agent_gemini_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/agent_gemini_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 5 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/agent_gemini_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects BeforeAgent context and records terminal lifecycle state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/agent_gemini_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for empty context and unknown lifecycle hooks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
