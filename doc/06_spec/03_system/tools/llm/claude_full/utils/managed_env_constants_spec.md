# Claude full managed env constants

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude full managed env constants

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Claude full managed env constants

#### should detect provider-managed env vars case-insensitively

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should detect provider-managed env vars case-insensitively


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect provider-managed env vars case-insensitively")
expect(isProviderManagedEnvVar("anthropic_model")).to_be(true)
expect(isProviderManagedEnvVar("CLAUDE_CODE_USE_VERTEX")).to_be(true)
expect(isProviderManagedEnvVar("PATH")).to_be(false)
```

</details>

#### should detect Vertex region overrides by prefix

- should detect Vertex region overrides by prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect Vertex region overrides by prefix")
expect(
    isProviderManagedEnvVar("vertex_region_claude_future_model")
).to_be(true)
```

</details>

#### should keep dangerous shell settings available

- should keep dangerous shell settings available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep dangerous shell settings available")
expect(dangerousShellSettings()).to_contain("apiKeyHelper")
expect(dangerousShellSettings()).to_contain("statusLine")
```

</details>

#### should keep representative safe env vars available

- should keep representative safe env vars available


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep representative safe env vars available")
expect(safeEnvVars()).to_contain("ANTHROPIC_CUSTOM_HEADERS")
expect(safeEnvVars()).to_contain("MAX_MCP_OUTPUT_TOKENS")
expect(safeEnvVars()).to_contain("VERTEX_REGION_CLAUDE_4_5_SONNET")
```

</details>

#### should expose experimental hidden-feature gates only as safe env vars

- should expose experimental hidden-feature gates only as safe env vars


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose experimental hidden-feature gates only as safe env vars")
val safe = safeEnvVars()
expect(safe).to_contain("CLAUDE_CODE_DISABLE_EXPERIMENTAL_BETAS")
expect(safe).to_contain("CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS")
expect(isProviderManagedEnvVar(
    "CLAUDE_CODE_DISABLE_EXPERIMENTAL_BETAS"
)).to_be(false)
expect(isProviderManagedEnvVar(
    "CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS"
)).to_be(false)
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

- Canonical SPipe generation for source `8feb3813a51f05f6f25c3bc051fe9b24dc656ad9307e6b273ca988241d0d0617`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8feb3813a51f05f6f25c3bc051fe9b24dc656ad9307e6b273ca988241d0d0617`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8feb3813a51f05f6f25c3bc051fe9b24dc656ad9307e6b273ca988241d0d0617`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:16:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect provider-managed env vars case-insensitively' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should detect provider-managed env vars case-insensitively' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect Vertex region overrides by prefix' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should detect Vertex region overrides by prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep dangerous shell settings available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep dangerous shell settings available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep representative safe env vars available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/managed_env_constants_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose experimental hidden-feature gates only as safe env vars' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
