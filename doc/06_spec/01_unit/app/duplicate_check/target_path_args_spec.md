# Target Path Args Specification

> Tests covering duplicate-check target argument parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Path Args Specification

## Scenarios

### duplicate-check target argument parsing

#### requires a positional target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires a positional target
   - Expected: target_path_from_args([]) equals ``
   - Expected: target_path_from_args(["--min-tokens", "30", "--format", "json"]) equals ``
   - Expected: target_path_from_args(["--min-tokens=30", "--format=json"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires a positional target")
expect(target_path_from_args([])).to_equal("")
expect(target_path_from_args(["--min-tokens", "30", "--format", "json"])).to_equal("")
expect(target_path_from_args(["--min-tokens=30", "--format=json"])).to_equal("")
```

</details>

#### preserves targets before or after options

- preserves targets before or after options
   - Expected: target_path_from_args(["fixtures", "--min-lines", "5"]) equals `fixtures`
   - Expected: target_path_from_args(["--min-lines", "5", "fixtures"]) equals `fixtures`
   - Expected: target_path_from_args(["--token", "--format=json", "fixtures"]) equals `fixtures`
   - Expected: target_path_from_args(["--mode=token", "fixtures"]) equals `fixtures`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves targets before or after options")
expect(target_path_from_args(["fixtures", "--min-lines", "5"])).to_equal("fixtures")
expect(target_path_from_args(["--min-lines", "5", "fixtures"])).to_equal("fixtures")
expect(target_path_from_args(["--token", "--format=json", "fixtures"])).to_equal("fixtures")
expect(target_path_from_args(["--mode=token", "fixtures"])).to_equal("fixtures")
```

</details>

#### rejects unknown options instead of treating their values as targets

- rejects unknown options instead of treating their values as targets
   - Expected: target_path_from_args(["--bogus", "fixtures"]) equals ``
   - Expected: target_path_from_args(["fixtures", "--bogus"]) equals ``
   - Expected: target_path_from_args(["--bogus=fixtures"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown options instead of treating their values as targets")
expect(target_path_from_args(["--bogus", "fixtures"])).to_equal("")
expect(target_path_from_args(["fixtures", "--bogus"])).to_equal("")
expect(target_path_from_args(["--bogus=fixtures"])).to_equal("")
```

</details>

#### rejects malformed known options and extra targets

- rejects malformed known options and extra targets
   - Expected: target_path_from_args(["--token=garbage", "fixtures"]) equals ``
   - Expected: target_path_from_args(["--mode=", "fixtures"]) equals ``
   - Expected: target_path_from_args(["--mode", "fixtures"]) equals ``
   - Expected: target_path_from_args(["first", "second"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects malformed known options and extra targets")
expect(target_path_from_args(["--token=garbage", "fixtures"])).to_equal("")
expect(target_path_from_args(["--mode=", "fixtures"])).to_equal("")
expect(target_path_from_args(["--mode", "fixtures"])).to_equal("")
expect(target_path_from_args(["first", "second"])).to_equal("")
```

</details>

#### rejects invalid mode and format values in split and equals forms

- rejects invalid mode and format values in split and equals forms
   - Expected: target_path_from_args(["fixtures", "--mode", "tokne"]) equals ``
   - Expected: target_path_from_args(["fixtures", "--mode=tokne"]) equals ``
   - Expected: target_path_from_args(["fixtures", "--format", "yaml"]) equals ``
   - Expected: target_path_from_args(["fixtures", "--format=yaml"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid mode and format values in split and equals forms")
expect(target_path_from_args(["fixtures", "--mode", "tokne"])).to_equal("")
expect(target_path_from_args(["fixtures", "--mode=tokne"])).to_equal("")
expect(target_path_from_args(["fixtures", "--format", "yaml"])).to_equal("")
expect(target_path_from_args(["fixtures", "--format=yaml"])).to_equal("")
```

</details>

#### leaves explicit help to command dispatch

- leaves explicit help to command dispatch
   - Expected: target_path_from_args(["--help"]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves explicit help to command dispatch")
expect(target_path_from_args(["--help"])).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/duplicate_check/target_path_args_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering duplicate-check target argument parsing.
- duplicate-check target argument parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc70bfe17983824a03e3e94ceb90a8d1e49a67b74ad71e9b26e5aa0fdd3eda2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc70bfe17983824a03e3e94ceb90a8d1e49a67b74ad71e9b26e5aa0fdd3eda2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc70bfe17983824a03e3e94ceb90a8d1e49a67b74ad71e9b26e5aa0fdd3eda2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/duplicate_check/target_path_args_spec.spl
mirror: doc/06_spec/01_unit/app/duplicate_check/target_path_args_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/duplicate_check/target_path_args_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/duplicate_check/target_path_args_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/duplicate_check/target_path_args_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a positional target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/duplicate_check/target_path_args_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves targets before or after options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/duplicate_check/target_path_args_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown options instead of treating their values as targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
