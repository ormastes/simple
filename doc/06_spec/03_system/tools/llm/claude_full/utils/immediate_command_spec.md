# Claude Full immediate command utils

> Pure Simple coverage for inference-config command immediacy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full immediate command utils

Pure Simple coverage for inference-config command immediacy.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/immediate_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for inference-config command immediacy.

## Scenarios

### Claude full immediate command utils

#### enables immediacy for ants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- enables immediacy for ants
- Check ant user type override
   - Expected: shouldInferenceConfigCommandBeImmediate("ant", false) is true
   - Expected: shouldInferenceConfigCommandBeImmediate("ant", true) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables immediacy for ants")
step("Check ant user type override")
expect(shouldInferenceConfigCommandBeImmediate("ant", false)).to_equal(true)
expect(shouldInferenceConfigCommandBeImmediate("ant", true)).to_equal(true)
```

</details>

#### enables external users through the experiment flag

- enables external users through the experiment flag
- Check experiment route
   - Expected: shouldInferenceConfigCommandBeImmediate("external", true) is true
   - Expected: shouldInferenceConfigCommandBeImmediate("external", false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables external users through the experiment flag")
step("Check experiment route")
expect(shouldInferenceConfigCommandBeImmediate("external", true)).to_equal(true)
expect(shouldInferenceConfigCommandBeImmediate("external", false)).to_equal(false)
```

</details>

#### keeps the upstream experiment key visible

- keeps the upstream experiment key visible
- Check experiment key
   - Expected: immediateModelCommandExperimentKey() equals `tengu_immediate_model_command`
   - Expected: immediateCommandParityScope() equals `inference-config command immediacy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the upstream experiment key visible")
step("Check experiment key")
expect(immediateModelCommandExperimentKey()).to_equal("tengu_immediate_model_command")
expect(immediateCommandParityScope()).to_equal("inference-config command immediacy")
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

- Canonical SPipe generation for source `307e07e591fdbda1299f3d2e95ec9ab4113c7b0f7b4bb09b1ce2018ac307f82c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `307e07e591fdbda1299f3d2e95ec9ab4113c7b0f7b4bb09b1ce2018ac307f82c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `307e07e591fdbda1299f3d2e95ec9ab4113c7b0f7b4bb09b1ce2018ac307f82c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/immediate_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/immediate_command_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/immediate_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/immediate_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/immediate_command_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables immediacy for ants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/immediate_command_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables external users through the experiment flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/immediate_command_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the upstream experiment key visible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
