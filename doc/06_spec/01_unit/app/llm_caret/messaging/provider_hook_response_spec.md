# Provider Hook Response Specification

> Tests covering Claude and Gemini messaging hook stdout contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Hook Response Specification

## Scenarios

### Claude and Gemini messaging hook stdout contracts

<details>
<summary>Advanced: injects bounded room context with the provider event name</summary>

#### injects bounded room context with the provider event name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- injects bounded room context with the provider event name
- Encode context for Claude UserPromptSubmit and Gemini BeforeAgent


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("injects bounded room context with the provider event name")
step("Encode context for Claude UserPromptSubmit and Gemini BeforeAgent")
val claude = provider_hook_response("claude", "UserPromptSubmit", "[#m-1] hello\nnext")
expect(claude).to_contain("\"hookEventName\":\"UserPromptSubmit\"")
expect(claude).to_contain("\"additionalContext\":\"[#m-1] hello\\nnext\"")
expect(claude).to_contain("\"suppressOutput\":true")
val gemini = provider_hook_response("gemini", "BeforeAgent", "task context")
expect(gemini).to_contain("\"hookEventName\":\"BeforeAgent\"")
expect(gemini).to_contain("\"additionalContext\":\"task context\"")
```

</details>


</details>

#### acknowledges non-context lifecycle events without leaking queue identifiers

- acknowledges non-context lifecycle events without leaking queue identifiers
- Return valid quiet JSON for terminal and tool lifecycle events
   - Expected: claude equals `{"continue":true,"suppressOutput":true}`
   - Expected: claude does not contain `event_id`
   - Expected: gemini equals `{"continue":true,"suppressOutput":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("acknowledges non-context lifecycle events without leaking queue identifiers")
step("Return valid quiet JSON for terminal and tool lifecycle events")
val claude = provider_hook_response("claude", "Stop", "private context")
expect(claude).to_equal("{\"continue\":true,\"suppressOutput\":true}")
expect(claude.contains("event_id")).to_equal(false)
val gemini = provider_hook_response("gemini", "AfterAgent", "private context")
expect(gemini).to_equal("{\"continue\":true,\"suppressOutput\":true}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/provider_hook_response_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Claude and Gemini messaging hook stdout contracts.
- Claude and Gemini messaging hook stdout contracts

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
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `284065bb8e58605bdca3cfd8fc17bf2b95c8ae09770b059de6b4650c39feee9c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `284065bb8e58605bdca3cfd8fc17bf2b95c8ae09770b059de6b4650c39feee9c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `284065bb8e58605bdca3cfd8fc17bf2b95c8ae09770b059de6b4650c39feee9c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/provider_hook_response_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/provider_hook_response_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/provider_hook_response_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/provider_hook_response_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/provider_hook_response_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/provider_hook_response_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects bounded room context with the provider event name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/provider_hook_response_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'acknowledges non-context lifecycle events without leaking queue identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
