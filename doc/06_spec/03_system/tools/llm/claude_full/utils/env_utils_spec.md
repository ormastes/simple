# Claude Full env utils

> Pure Simple coverage for deterministic env value helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full env utils

Pure Simple coverage for deterministic env value helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/env_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure Simple coverage for deterministic env value helpers.

## Scenarios

### Claude full env utils

#### matches node options by whitespace-delimited exact flag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches node options by whitespace-delimited exact flag
- Check node option matching
   - Expected: hasNodeOption("--trace-warnings --max-old-space-size=4096", "--trace-warnings") is true
   - Expected: hasNodeOption("--trace-warnings-extra", "--trace-warnings") is false
   - Expected: hasNodeOption("", "--trace-warnings") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches node options by whitespace-delimited exact flag")
step("Check node option matching")
expect(hasNodeOption("--trace-warnings --max-old-space-size=4096", "--trace-warnings")).to_equal(true)
expect(hasNodeOption("--trace-warnings-extra", "--trace-warnings")).to_equal(false)
expect(hasNodeOption("", "--trace-warnings")).to_equal(false)
```

</details>

#### parses truthy env values

- parses truthy env values
- Check truthy values
   - Expected: isEnvTruthy(Some("1")) is true
   - Expected: isEnvTruthy(Some(" YES ")) is true
   - Expected: isEnvTruthy(Some("off")) is false
   - Expected: isEnvTruthy(nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses truthy env values")
step("Check truthy values")
expect(isEnvTruthy(Some("1"))).to_equal(true)
expect(isEnvTruthy(Some(" YES "))).to_equal(true)
expect(isEnvTruthy(Some("off"))).to_equal(false)
expect(isEnvTruthy(nil)).to_equal(false)
```

</details>

#### parses defined falsy env values

- parses defined falsy env values
- Check defined falsy values
   - Expected: isEnvDefinedFalsy(Some("0")) is true
   - Expected: isEnvDefinedFalsy(Some(" false ")) is true
   - Expected: isEnvDefinedFalsy(Some("yes")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses defined falsy env values")
step("Check defined falsy values")
expect(isEnvDefinedFalsy(Some("0"))).to_equal(true)
expect(isEnvDefinedFalsy(Some(" false "))).to_equal(true)
expect(isEnvDefinedFalsy(Some("yes"))).to_equal(false)
```

</details>

#### does not treat missing or empty values as defined falsy

- does not treat missing or empty values as defined falsy
- Check missing values
   - Expected: isEnvDefinedFalsy(nil) is false
   - Expected: isEnvDefinedFalsy(Some("")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not treat missing or empty values as defined falsy")
step("Check missing values")
expect(isEnvDefinedFalsy(nil)).to_equal(false)
expect(isEnvDefinedFalsy(Some(""))).to_equal(false)
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

- Canonical SPipe generation for source `c1bde048f48164c58f4ae2b246ea9c8136ed333138fcf415dab97d0f71c9b4fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1bde048f48164c58f4ae2b246ea9c8136ed333138fcf415dab97d0f71c9b4fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1bde048f48164c58f4ae2b246ea9c8136ed333138fcf415dab97d0f71c9b4fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/llm/claude_full/utils/env_utils_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/env_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/env_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/env_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/env_utils_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches node options by whitespace-delimited exact flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/env_utils_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses truthy env values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/env_utils_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses defined falsy env values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
