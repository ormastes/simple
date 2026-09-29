# Plugin Agent Selection Specification

> Tests covering LLM Caret composite plugin agent selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Plugin Agent Selection Specification

## Scenarios

### LLM Caret composite plugin agent selection

#### accepts and persists the complete Claude Codex Gemini selection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts and persists the complete Claude Codex Gemini selection
   - Expected: selected.valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts and persists the complete Claude Codex Gemini selection")
val selected = parse_messaging_agent_selection("claude,codex,gemini")
expect(selected.valid).to_equal(true)
val activation = agent_activation_sdn(selected)
expect(activation).to_contain("simple.llm-caret-messaging.activation/v1")
expect(activation).to_contain("claude")
expect(activation).to_contain("codex")
expect(activation).to_contain("gemini")
```

</details>

#### rejects partial duplicate and unknown selections

- rejects partial duplicate and unknown selections


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects partial duplicate and unknown selections")
expect(parse_messaging_agent_selection("claude,codex").error).to_equal(
    "composite_plugin_requires_claude_codex_gemini")
expect(parse_messaging_agent_selection("claude,codex,codex").error).to_equal(
    "duplicate_agent_selection:codex")
expect(parse_messaging_agent_selection("claude,codex,other").error).to_equal(
    "unsupported_agent_selection:other")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret composite plugin agent selection.
- LLM Caret composite plugin agent selection

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
- `REQ-LLM-MSG-013`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1afa16e924494fef88399f339d049c390bea514a40929fd6266478ca4dc9db03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1afa16e924494fef88399f339d049c390bea514a40929fd6266478ca4dc9db03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1afa16e924494fef88399f339d049c390bea514a40929fd6266478ca4dc9db03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts and persists the complete Claude Codex Gemini selection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/messaging/plugin_agent_selection_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects partial duplicate and unknown selections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
