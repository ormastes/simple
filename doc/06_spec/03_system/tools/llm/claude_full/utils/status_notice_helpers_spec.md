# Claude Full Status Notice Helpers

> Pure Simple coverage for agent description token notice helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Status Notice Helpers

Pure Simple coverage for agent description token notice helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for agent description token notice helpers.

## Scenarios

### Claude full status notice helpers

#### returns zero when agent definitions are missing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns zero when agent definitions are missing
- Check missing definitions
   - Expected: getAgentDescriptionsTotalTokens(nil) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns zero when agent definitions are missing")
step("Check missing definitions")
expect(getAgentDescriptionsTotalTokens(nil)).to_equal(0)
```

</details>

#### ignores built-in agents

- ignores built-in agents
- Check built-in filter
   - Expected: getAgentDescriptionsTotalTokens(Some(definitions)) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores built-in agents")
step("Check built-in filter")
val definitions = AgentDefinitionsResult(activeAgents: [
    StatusNoticeAgentDefinition(agentType: "general", whenToUse: "Built in helper", source: "built-in")
])
expect(getAgentDescriptionsTotalTokens(Some(definitions))).to_equal(0)
```

</details>

#### sums rough token estimates for custom agent descriptions

- sums rough token estimates for custom agent descriptions
- Check custom agent total
   - Expected: getAgentDescriptionsTotalTokens(Some(definitions)) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sums rough token estimates for custom agent descriptions")
step("Check custom agent total")
val definitions = AgentDefinitionsResult(activeAgents: [
    StatusNoticeAgentDefinition(agentType: "alpha", whenToUse: "abcd", source: "project"),
    StatusNoticeAgentDefinition(agentType: "beta", whenToUse: "abcdefghij", source: "user")
])
expect(getAgentDescriptionsTotalTokens(Some(definitions))).to_equal(7)
```

</details>

#### uses JavaScript string length for Unicode descriptions

- uses JavaScript string length for Unicode descriptions
- Check Unicode length
   - Expected: getAgentDescriptionsTotalTokens(Some(definitions)) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses JavaScript string length for Unicode descriptions")
step("Check Unicode length")
val definitions = AgentDefinitionsResult(activeAgents: [
    StatusNoticeAgentDefinition(agentType: "é", whenToUse: "é", source: "project")
])
expect(getAgentDescriptionsTotalTokens(Some(definitions))).to_equal(1)
```

</details>

#### exports the upstream threshold

- exports the upstream threshold
- Check threshold
   - Expected: AGENT_DESCRIPTIONS_THRESHOLD equals `15000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports the upstream threshold")
step("Check threshold")
expect(AGENT_DESCRIPTIONS_THRESHOLD).to_equal(15000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e5f6570bc0eb2cbcfe474f89841962460dface73a62a746690d9b3531ec3c084`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5f6570bc0eb2cbcfe474f89841962460dface73a62a746690d9b3531ec3c084`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5f6570bc0eb2cbcfe474f89841962460dface73a62a746690d9b3531ec3c084`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero when agent definitions are missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores built-in agents' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/status_notice_helpers_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sums rough token estimates for custom agent descriptions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
