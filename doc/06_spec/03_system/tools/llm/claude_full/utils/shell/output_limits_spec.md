# Claude Full shell output limits

> Pure Simple coverage for bounded bash output limit validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full shell output limits

Pure Simple coverage for bounded bash output limit validation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for bounded bash output limit validation.

## Scenarios

### Claude full shell output limits

#### uses upstream constants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses upstream constants
- Check constants
   - Expected: bashMaxOutputDefault() equals `30000`
   - Expected: bashMaxOutputUpperLimit() equals `150000`
   - Expected: bashMaxOutputEnvName() equals `BASH_MAX_OUTPUT_LENGTH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses upstream constants")
step("Check constants")
expect(bashMaxOutputDefault()).to_equal(30000)
expect(bashMaxOutputUpperLimit()).to_equal(150000)
expect(bashMaxOutputEnvName()).to_equal("BASH_MAX_OUTPUT_LENGTH")
```

</details>

#### defaults missing values

- defaults missing values
- Check empty env value
   - Expected: getMaxOutputLengthFromOptionalEnvValue(nil) equals `30000`
   - Expected: getMaxOutputLengthFromEnvValue("") equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults missing values")
step("Check empty env value")
expect(getMaxOutputLengthFromOptionalEnvValue(nil)).to_equal(30000)
expect(getMaxOutputLengthFromEnvValue("")).to_equal(30000)
```

</details>

#### accepts positive bounded integer prefixes

- accepts positive bounded integer prefixes
- Check valid env value
   - Expected: getMaxOutputLengthFromEnvValue("1200") equals `1200`
   - Expected: getMaxOutputLengthFromEnvValue("  +1200ms") equals `1200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts positive bounded integer prefixes")
step("Check valid env value")
expect(getMaxOutputLengthFromEnvValue("1200")).to_equal(1200)
expect(getMaxOutputLengthFromEnvValue("  +1200ms")).to_equal(1200)
```

</details>

#### rejects invalid or non-positive values

- rejects invalid or non-positive values
- Check invalid env values
   - Expected: getMaxOutputLengthFromEnvValue("nope") equals `30000`
   - Expected: getMaxOutputLengthFromEnvValue("0") equals `30000`
   - Expected: getMaxOutputLengthFromEnvValue("-1") equals `30000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid or non-positive values")
step("Check invalid env values")
expect(getMaxOutputLengthFromEnvValue("nope")).to_equal(30000)
expect(getMaxOutputLengthFromEnvValue("0")).to_equal(30000)
expect(getMaxOutputLengthFromEnvValue("-1")).to_equal(30000)
```

</details>

#### caps values above the upper limit

- caps values above the upper limit
- Check capped env value
   - Expected: getMaxOutputLengthFromEnvValue("200000") equals `150000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caps values above the upper limit")
step("Check capped env value")
expect(getMaxOutputLengthFromEnvValue("200000")).to_equal(150000)
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

- Canonical SPipe generation for source `c8c88afa4778a63c5c4c0d5ca4e7153c7ed3a506b1e760da02893750dc67a4b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c8c88afa4778a63c5c4c0d5ca4e7153c7ed3a506b1e760da02893750dc67a4b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c8c88afa4778a63c5c4c0d5ca4e7153c7ed3a506b1e760da02893750dc67a4b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses upstream constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults missing values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/shell/output_limits_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts positive bounded integer prefixes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
