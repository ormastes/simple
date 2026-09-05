# Claude Full Standalone Agent

> Pure Simple coverage for standalone agent utility parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Standalone Agent

Pure Simple coverage for standalone agent utility parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/standalone_agent_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for standalone agent utility parity.

## Scenarios

### Claude full standalone agent

#### returns standalone agent name outside a team

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns standalone agent name outside a team
- Check standalone context
   - Expected: getStandaloneAgentName(nil, Some(context)) equals `Some("solo")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns standalone agent name outside a team")
step("Check standalone context")
val context = StandaloneAgentContext(name: "solo", color: "blue")
expect(getStandaloneAgentName(nil, Some(context))).to_equal(Some("solo"))
```

</details>

#### returns nil when no standalone context exists

- returns nil when no standalone context exists
- Check missing context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil when no standalone context exists")
step("Check missing context")
expect(getStandaloneAgentName(nil, nil)).to_be_nil()
```

</details>

#### lets swarm team context take precedence

- lets swarm team context take precedence
- Check team precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lets swarm team context take precedence")
step("Check team precedence")
val context = StandaloneAgentContext(name: "solo", color: "blue")
expect(getStandaloneAgentName(Some("team"), Some(context))).to_be_nil()
```

</details>

#### treats empty team name as no team

- treats empty team name as no team
- Check empty team name
   - Expected: getStandaloneAgentName(Some(""), Some(context)) equals `Some("solo")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats empty team name as no team")
step("Check empty team name")
val context = StandaloneAgentContext(name: "solo", color: "blue")
expect(getStandaloneAgentName(Some(""), Some(context))).to_equal(Some("solo"))
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a9453b7c3a6fb23d68802ee06e5adc46fee5a7b7491001d23bdd94d69c80ca2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a9453b7c3a6fb23d68802ee06e5adc46fee5a7b7491001d23bdd94d69c80ca2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a9453b7c3a6fb23d68802ee06e5adc46fee5a7b7491001d23bdd94d69c80ca2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/standalone_agent_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/standalone_agent_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/standalone_agent_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/standalone_agent_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/standalone_agent_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns standalone agent name outside a team' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/standalone_agent_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil when no standalone context exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/standalone_agent_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets swarm team context take precedence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
