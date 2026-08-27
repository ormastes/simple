# Claude Full teammate model utils

> Pure Simple coverage for provider-aware teammate fallback model selection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full teammate model utils

Pure Simple coverage for provider-aware teammate fallback model selection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for provider-aware teammate fallback model selection.

## Scenarios

### Claude full teammate model utils

#### uses the first-party Opus 4.6 fallback by default

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the first-party Opus 4.6 fallback by default
- Check first-party fallback
   - Expected: getHardcodedTeammateModelFallback("firstParty") equals `claude-opus-4-6`
   - Expected: getHardcodedTeammateModelFallback("") equals `claude-opus-4-6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses the first-party Opus 4.6 fallback by default")
step("Check first-party fallback")
expect(getHardcodedTeammateModelFallback("firstParty")).to_equal("claude-opus-4-6")
expect(getHardcodedTeammateModelFallback("")).to_equal("claude-opus-4-6")
```

</details>

#### uses the Bedrock Opus 4.6 provider id

- uses the Bedrock Opus 4.6 provider id
- Check Bedrock fallback
   - Expected: getHardcodedTeammateModelFallback("bedrock") equals `us.anthropic.claude-opus-4-6-v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses the Bedrock Opus 4.6 provider id")
step("Check Bedrock fallback")
expect(getHardcodedTeammateModelFallback("bedrock")).to_equal("us.anthropic.claude-opus-4-6-v1")
```

</details>

#### uses provider-compatible Opus 4.6 ids case-insensitively

- uses provider-compatible Opus 4.6 ids case-insensitively
- Check Vertex and Foundry fallback
   - Expected: getHardcodedTeammateModelFallback(" VERTEX ") equals `claude-opus-4-6`
   - Expected: getHardcodedTeammateModelFallback("foundry") equals `claude-opus-4-6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses provider-compatible Opus 4.6 ids case-insensitively")
step("Check Vertex and Foundry fallback")
expect(getHardcodedTeammateModelFallback(" VERTEX ")).to_equal("claude-opus-4-6")
expect(getHardcodedTeammateModelFallback("foundry")).to_equal("claude-opus-4-6")
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

- Canonical SPipe generation for source `fdb0207a407f31786b2356d0db46300602c057903b18405fc4c04a11cd88d8eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdb0207a407f31786b2356d0db46300602c057903b18405fc4c04a11cd88d8eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdb0207a407f31786b2356d0db46300602c057903b18405fc4c04a11cd88d8eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the first-party Opus 4.6 fallback by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the Bedrock Opus 4.6 provider id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/swarm/teammateModel_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses provider-compatible Opus 4.6 ids case-insensitively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
