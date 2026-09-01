# Parse Utils Specification

> Tests covering ParseUtils.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parse Utils Specification

## Scenarios

### ParseUtils

#### finds a flag value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds a flag value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds a flag value")
val args = ["--mode", "fast", "--verbose"]
val mode = _parse_flag_value(args, "--mode")
expect mode.unwrap() == "fast"
```

</details>

#### returns nil for a missing flag value

- returns nil for a missing flag value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for a missing flag value")
val args = ["--verbose"]
val mode = _parse_flag_value(args, "--mode")
expect mode == nil
```

</details>

#### detects boolean flags

- detects boolean flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects boolean flags")
val args = ["--mode", "fast", "--verbose"]
expect _has_flag(args, "--verbose") == true
expect _has_flag(args, "--quiet") == false
```

</details>

#### splits comma separated flags and drops blanks

- splits comma separated flags and drops blanks


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits comma separated flags and drops blanks")
val flags = _parse_csv_flags("native, , smf")
expect flags.len() == 2
expect flags[0] == "native"
expect flags[1] == "smf"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/parse_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ParseUtils.
- ParseUtils

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2100a6c59238b99823eb661e8f4abd9d85fb3cfdf8b49b31f5e98b09a9850b41`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2100a6c59238b99823eb661e8f4abd9d85fb3cfdf8b49b31f5e98b09a9850b41`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2100a6c59238b99823eb661e8f4abd9d85fb3cfdf8b49b31f5e98b09a9850b41`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/parse_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/parse_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/parse_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/parse_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/parse_utils_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a flag value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/parse_utils_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for a missing flag value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/parse_utils_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects boolean flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
