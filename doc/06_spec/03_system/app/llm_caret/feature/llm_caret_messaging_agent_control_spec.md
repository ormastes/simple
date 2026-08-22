# llm_caret_messaging_agent_control_spec

> Verifies the llm caret messaging agent control behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_caret_messaging_agent_control_spec

Verifies the llm caret messaging agent control behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret messaging agent control behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret agent-control composition

#### attaches, injects context, submits, steers, and cancels every provider

- Verify: attaches, injects context, submits, steers, and cancels every provider
- Control the
   - Expected: attached.ok is true
   - Expected: runtime.inject_agent_context(provider, attached.session_id, "context-1").ok is true
   - Expected: runtime.submit_agent_task(provider, attached.session_id, "task-1").ok is true
   - Expected: runtime.steer_agent_task(provider, attached.session_id, "task-2").ok is true
   - Expected: runtime.cancel_agent_task(provider, attached.session_id, "task-2").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-008 REQ-LLM-MSG-014
step("Verify: attaches, injects context, submits, steers, and cancels every provider")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: normalizes provider lifecycle events and rejects unknown providers
   - Expected: runtime.accept_agent_event("claude", claude.session_id, "PermissionRequest", "approval").evidence equals `enqueued:waiting_input`
   - Expected: runtime.accept_agent_event("codex", codex.session_id, "turn/completed", "done").evidence equals `enqueued:completed`
   - Expected: runtime.accept_agent_event("gemini", gemini.session_id, "BeforeAgent", "context-2").evidence equals `context_accepted:context-2`
   - Expected: runtime.attach_agent("other", binding("other")).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-MSG-006 REQ-LLM-MSG-007 REQ-LLM-MSG-008 REQ-LLM-MSG-014
step("Verify: normalizes provider lifecycle events and rejects unknown providers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `efcb34a19474473071b4a9c23ff959451c3f3f47a721392879dc4fb7b1a522b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `efcb34a19474473071b4a9c23ff959451c3f3f47a721392879dc4fb7b1a522b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `efcb34a19474473071b4a9c23ff959451c3f3f47a721392879dc4fb7b1a522b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_messaging_agent_control_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
