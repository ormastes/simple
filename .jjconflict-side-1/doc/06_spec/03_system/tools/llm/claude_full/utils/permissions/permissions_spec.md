# Claude Full Permissions Slice

> Focused Simple coverage for deterministic permission rule-selection helpers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Permissions Slice

Focused Simple coverage for deterministic permission rule-selection helpers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for deterministic permission rule-selection helpers
from utils/permissions/permissions.ts.

## Scenarios

### Claude full permissions parity

#### should model rule flattening

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model rule flattening
- Check rule extraction
   - Expected: getAllowRulesRoute("project", "Read,Bash") equals `allow:project:Read,Bash`
   - Expected: getDenyRulesRoute("user", "Bash") equals `deny:user:Bash`
   - Expected: getAskRulesRoute("local", "Write") equals `ask:local:Write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model rule flattening")
step("Check rule extraction")
expect(getAllowRulesRoute("project", "Read,Bash")).to_equal("allow:project:Read,Bash")
expect(getDenyRulesRoute("user", "Bash")).to_equal("deny:user:Bash")
expect(getAskRulesRoute("local", "Write")).to_equal("ask:local:Write")
```

</details>

#### should model tool rule matching

- should model tool rule matching
- Check tool matching
   - Expected: toolMatchesRuleRoute("Read", "Read", "") is true
   - Expected: toolMatchesRuleRoute("Read", "Read", "file") is false
   - Expected: toolMatchesRuleRoute("mcp__server1__tool1", "mcp__server1", "") is true
   - Expected: toolMatchesRuleRoute("mcp__server1__tool1", "mcp__server1__*", "") is true
   - Expected: toolAlwaysAllowedRuleRoute("Read", true) equals `allow Read`
   - Expected: toolAlwaysAllowedRuleRoute("Read", false) equals `null`
   - Expected: getDenyRuleForToolRoute("Bash", false) equals `null`
   - Expected: getAskRuleForToolRoute("Bash", false) equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model tool rule matching")
step("Check tool matching")
expect(toolMatchesRuleRoute("Read", "Read", "")).to_equal(true)
expect(toolMatchesRuleRoute("Read", "Read", "file")).to_equal(false)
expect(toolMatchesRuleRoute("mcp__server1__tool1", "mcp__server1", "")).to_equal(true)
expect(toolMatchesRuleRoute("mcp__server1__tool1", "mcp__server1__*", "")).to_equal(true)
expect(toolAlwaysAllowedRuleRoute("Read", true)).to_equal("allow Read")
expect(toolAlwaysAllowedRuleRoute("Read", false)).to_equal("null")
expect(getDenyRuleForToolRoute("Bash", false)).to_equal("null")
expect(getAskRuleForToolRoute("Bash", false)).to_equal("null")
```

</details>

#### should model agent and content rule helpers

- should model agent and content rule helpers
- Check agent and content helpers
   - Expected: getDenyRuleForAgentRoute("Agent", "builder", "builder") equals `deny agent builder`
   - Expected: getDenyRuleForAgentRoute("Agent", "builder", "reviewer") equals `null`
   - Expected: filterDeniedAgentsRoute("builder,reviewer,writer", "reviewer") equals `builder,writer`
   - Expected: getRuleByContentsForToolNameRoute("Bash", "Bash", "deny", "deny", "python") equals `python`
   - Expected: getRuleByContentsForToolNameRoute("Bash", "Read", "deny", "deny", "python") equals `null`
   - Expected: getRuleByContentsForToolRoute("Bash", "Bash", "deny", "deny", "python") equals `python`
   - Expected: permissionsSourceLinesModeled() equals `1486`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model agent and content rule helpers")
step("Check agent and content helpers")
expect(getDenyRuleForAgentRoute("Agent", "builder", "builder")).to_equal("deny agent builder")
expect(getDenyRuleForAgentRoute("Agent", "builder", "reviewer")).to_equal("null")
expect(filterDeniedAgentsRoute("builder,reviewer,writer", "reviewer")).to_equal("builder,writer")
expect(getRuleByContentsForToolNameRoute("Bash", "Bash", "deny", "deny", "python")).to_equal("python")
expect(getRuleByContentsForToolNameRoute("Bash", "Read", "deny", "deny", "python")).to_equal("null")
expect(getRuleByContentsForToolRoute("Bash", "Bash", "deny", "deny", "python")).to_equal("python")
expect(permissionsSourceLinesModeled()).to_equal(1486)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc5e61fd3bcfadb4b0aad9cae77d3f2769a3b9d98e55f0d0cd247ce2afcd4689`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc5e61fd3bcfadb4b0aad9cae77d3f2769a3b9d98e55f0d0cd247ce2afcd4689`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc5e61fd3bcfadb4b0aad9cae77d3f2769a3b9d98e55f0d0cd247ce2afcd4689`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model rule flattening' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model rule flattening' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model tool rule matching' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model tool rule matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model agent and content rule helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/permissions_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model agent and content rule helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
