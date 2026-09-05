# Routing Context Specification

> Tests covering LLM Caret routing and bounded context.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Routing Context Specification

## Scenarios

### LLM Caret routing and bounded context

#### should route explicit mentions before fallback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should route explicit mentions before fallback
   - Expected: decision.routed is true
   - Expected: decision.agent_id equals `reviewer`
   - Expected: decision.reason equals `explicit_mention`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should route explicit mentions before fallback")
val message = rc_message("m2", 2, "@reviewer inspect this", "", "", MessageOrigin.Human)
val decision = route_message(message, [], [rc_binding("reviewer")], [rc_profile("reviewer", "reviewer", "review")], "", "reviewer")
expect(decision.routed).to_equal(true)
expect(decision.agent_id).to_equal("reviewer")
expect(decision.reason).to_equal("explicit_mention")
```

</details>

#### should select the reply target deterministically

- should select the reply target deterministically
   - Expected: route_message(reply, [prior], [rc_binding("reviewer")], [rc_profile("reviewer", "reviewer", "review")], "", "").agent_id equals `reviewer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should select the reply target deterministically")
val prior = rc_message("m1", 1, "answer", "", "reviewer", MessageOrigin.AgentAnswer)
val reply = rc_message("m2", 2, "continue", "m1", "", MessageOrigin.Human)
expect(route_message(reply, [prior], [rc_binding("reviewer")], [rc_profile("reviewer", "reviewer", "review")], "", "").agent_id).to_equal("reviewer")
```

</details>

#### should build previous-two context and redact secrets

- should build previous-two context and redact secrets
   - Expected: bundle.accepted is true
   - Expected: bundle.manifest.included_message_ids does not contain `u1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should build previous-two context and redact secrets")
val first = rc_message("m1", 1, "old", "", "", MessageOrigin.Human)
val update = rc_message("u1", 2, "noisy", "", "reviewer", MessageOrigin.AgentUpdate)
val second = rc_message("m2", 3, "token secret-123", "", "", MessageOrigin.Human)
val trigger = rc_message("m3", 4, "review now", "m2", "", MessageOrigin.Human)
val bundle = build_context_bundle("ctx", "task", "reviewer", "r", trigger, [first, update, second],
    [rc_profile("reviewer", "reviewer", "review")], "summary", "source", "hash", ["secret-123"], 2048, 2, "v1", "redact-v1")
expect(bundle.accepted).to_equal(true)
expect(bundle.manifest.included_message_ids).to_contain("m2")
expect(bundle.manifest.included_message_ids).to_contain("m3")
expect(bundle.manifest.included_message_ids.contains("u1")).to_equal(false)
expect(bundle.text_content).to_contain("[REDACTED]")
```

</details>

<details>
<summary>Advanced: should reject cross-room context injection</summary>

#### should reject cross-room context injection

- should reject cross-room context injection
   - Expected: bundle.accepted is false
   - Expected: bundle.error equals `cross_room_trigger_denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should reject cross-room context injection")
val trigger = rc_message("m1", 1, "hello", "", "", MessageOrigin.Human)
val bundle = build_context_bundle("ctx", "task", "reviewer", "private", trigger, [], [], "", "", "", [], 1024, 2, "v1", "v1")
expect(bundle.accepted).to_equal(false)
expect(bundle.error).to_equal("cross_room_trigger_denied")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/routing_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret routing and bounded context.
- LLM Caret routing and bounded context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8b4677bb41e588ac5d58273b7c462ead017f67422158184c4f5e1a8b1d2ff7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8b4677bb41e588ac5d58273b7c462ead017f67422158184c4f5e1a8b1d2ff7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8b4677bb41e588ac5d58273b7c462ead017f67422158184c4f5e1a8b1d2ff7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/app/llm_caret/messaging/routing_context_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/routing_context_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/messaging/routing_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/routing_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/routing_context_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route explicit mentions before fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/messaging/routing_context_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route explicit mentions before fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/routing_context_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should select the reply target deterministically' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/messaging/routing_context_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should select the reply target deterministically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/routing_context_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build previous-two context and redact secrets' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/messaging/routing_context_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build previous-two context and redact secrets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/routing_context_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject cross-room context injection' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
