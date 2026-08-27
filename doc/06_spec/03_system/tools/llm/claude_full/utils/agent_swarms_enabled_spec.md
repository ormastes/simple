# Claude Full agent swarms enabled

> Pure Simple coverage for the teammate feature gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full agent swarms enabled

Pure Simple coverage for the teammate feature gate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for the teammate feature gate.

REQ-LLM-CARET-HIDDEN-008

Claim boundary: this focused owner spec proves ANT override, external opt-in,
and killswitch behavior from `agentSwarmsEnabled.spl`. The aggregate
feature-gate registry owns the exhaustive input matrix. This spec does not
prove shipped CLI/TUI reachability or live process behavior.

## Scenarios

### Claude full agent swarms enabled

### REQ-LLM-CARET-HIDDEN-008: focused agent-swarms owner behavior

#### should always enable ANT users
#### should require external opt-in

- should require external opt-in
- Check external opt-in
   - Expected: isAgentSwarmsEnabled("user", false, false, true) is false
   - Expected: isAgentSwarmsEnabled("user", true, false, true) is true
   - Expected: isAgentSwarmsEnabled("user", false, true, true) is true
   - Expected: isAgentSwarmsEnabled("user", true, true, true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require external opt-in")
step("Check external opt-in")
expect(isAgentSwarmsEnabled("user", false, false, true)).to_equal(false)
expect(isAgentSwarmsEnabled("user", true, false, true)).to_equal(true)
expect(isAgentSwarmsEnabled("user", false, true, true)).to_equal(true)
expect(isAgentSwarmsEnabled("user", true, true, true)).to_equal(true)
```

</details>

#### should respect the external killswitch

- should respect the external killswitch
- Check killswitch
   - Expected: isAgentSwarmsEnabled("user", true, false, false) is false
   - Expected: isAgentSwarmsEnabled("user", false, true, false) is false
   - Expected: isAgentSwarmsEnabled("user", true, true, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should respect the external killswitch")
step("Check killswitch")
expect(isAgentSwarmsEnabled("user", true, false, false)).to_equal(false)
expect(isAgentSwarmsEnabled("user", false, true, false)).to_equal(false)
expect(isAgentSwarmsEnabled("user", true, true, false)).to_equal(false)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7214d81b0373e55d4be17f80a06ce86da3d3ecae93b742fa4385926ee262af6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7214d81b0373e55d4be17f80a06ce86da3d3ecae93b742fa4385926ee262af6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7214d81b0373e55d4be17f80a06ce86da3d3ecae93b742fa4385926ee262af6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=75 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should always enable ANT users' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should always enable ANT users' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require external opt-in' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require external opt-in' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should respect the external killswitch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/agent_swarms_enabled_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should respect the external killswitch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
