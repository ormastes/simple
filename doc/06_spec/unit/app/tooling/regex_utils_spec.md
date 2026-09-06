# Regex Utils Specification

> Tests covering Regex Utils.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regex Utils Specification

## Scenarios

### Regex Utils

#### matches digit patterns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches digit patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches digit patterns")
expect regex_is_match(r"\d+", "build 42 passed") == true
expect regex_is_match(r"^\d+$", "42x") == false
```

</details>

#### finds the first number with range metadata

- finds the first number with range metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds the first number with range metadata")
val found = regex_find(r"\d+", "run 128 ms")
match found:
    Some(m):
        expect m.text == "128"
        expect m.start == 4
        expect m.end == 7
    nil:
        expect false
```

</details>

#### replaces all numeric runs

- replaces all numeric runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces all numeric runs")
val replaced = regex_replace_all(r"\d+", "p50=12 p95=48", "N")
expect replaced == "pN=N pN=N"
```

</details>

#### splits comma separated text and trims spacing

- splits comma separated text and trims spacing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits comma separated text and trims spacing")
val parts = regex_split(r",\s*", "alpha, beta,gamma")
expect parts.len() == 3
expect parts[1] == "beta"
```

</details>

#### validates common email and ipv4 shapes

- validates common email and ipv4 shapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates common email and ipv4 shapes")
expect is_valid_email("dev@example.com") == true
expect is_valid_email("@example.com") == false
expect is_valid_ipv4("192.168.0.1") == true
expect is_valid_ipv4("999.168.0.1") == false
```

</details>

#### extracts numeric strings in order

- extracts numeric strings in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts numeric strings in order")
val nums = extract_numbers("x=7 y=11 z=19")
expect nums.len() == 3
expect nums[0] == "7"
expect nums[2] == "19"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/regex_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Regex Utils.
- Regex Utils

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

- Canonical SPipe generation for source `0adc0bd454c68df7c5c402210498e880b745c50a8b2f95873cd1137caa13a4c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0adc0bd454c68df7c5c402210498e880b745c50a8b2f95873cd1137caa13a4c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0adc0bd454c68df7c5c402210498e880b745c50a8b2f95873cd1137caa13a4c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/regex_utils_spec.spl
mirror: doc/06_spec/unit/app/tooling/regex_utils_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/regex_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/regex_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/regex_utils_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches digit patterns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/regex_utils_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds the first number with range metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/regex_utils_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces all numeric runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
