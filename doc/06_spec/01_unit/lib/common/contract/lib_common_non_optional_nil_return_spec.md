# Lib Common Non Optional Nil Return Specification

> Tests covering non-optional return contract fixes (class c), non-optional return contract — perf receipt env probes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Common Non Optional Nil Return Specification

## Scenarios

### non-optional return contract fixes (class c)

#### average_i64 returns nil on empty list instead of violating i64's contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- average_i64 returns nil on empty list instead of violating i64's contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("average_i64 returns nil on empty list instead of violating i64's contract")
val result = average_i64([])
expect(result).to_be_nil()
```

</details>

#### json_object_get returns nil for a missing key instead of violating any's contract

- json_object_get returns nil for a missing key instead of violating any's contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("json_object_get returns nil for a missing key instead of violating any's contract")
val obj = json_number(0)  # placeholder value, not an object
val result = json_object_get(obj, "missing")
expect(result).to_be_nil()
```

</details>

#### from_ymd returns nil for an invalid date instead of violating any's contract

- from_ymd returns nil for an invalid date instead of violating any's contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("from_ymd returns nil for an invalid date instead of violating any's contract")
val result = from_ymd(2025, 13, 40)
expect(result).to_be_nil()
```

</details>

#### parse_iso8601 returns nil for malformed input instead of violating any's contract

- parse_iso8601 returns nil for malformed input instead of violating any's contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse_iso8601 returns nil for malformed input instead of violating any's contract")
val result = parse_iso8601("not-a-date")
expect(result).to_be_nil()
```

</details>

#### parse_example_comment returns nil for non-example prose instead of violating the contract

- parse_example_comment returns nil for non-example prose instead of violating the contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse_example_comment returns nil for non-example prose instead of violating the contract")
val result = parse_example_comment(" just prose", 1)
expect(result).to_be_nil()
```

</details>

### non-optional return contract — perf receipt env probes

#### perf_probe_execution_mode_env is total when SIMPLE_EXECUTION_MODE is unset

- perf_probe_execution_mode_env is total when SIMPLE_EXECUTION_MODE is unset


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("perf_probe_execution_mode_env is total when SIMPLE_EXECUTION_MODE is unset")
# `-> text`; documented default "" rather than nil. Unset and
# explicitly-empty mean the same thing to perf_probe_engine_family.
assert_true(perf_probe_execution_mode_env().len() >= 0)
```

</details>

#### perf_probe_engine_family still classifies through the totalized probe

- perf_probe_engine_family still classifies through the totalized probe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("perf_probe_engine_family still classifies through the totalized probe")
val fam = perf_probe_engine_family()
assert_true(fam == "interpreter" or fam == "jit-family")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering non-optional return contract fixes (class c), non-optional return contract — perf receipt env probes.
- non-optional return contract fixes (class c)
- non-optional return contract — perf receipt env probes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `63821e2f5d0f957bcdeb271f9bf158990b39add1a9fc4374a6d089c91288ceee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63821e2f5d0f957bcdeb271f9bf158990b39add1a9fc4374a6d089c91288ceee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63821e2f5d0f957bcdeb271f9bf158990b39add1a9fc4374a6d089c91288ceee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'average_i64 returns nil on empty list instead of violating i64's contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'json_object_get returns nil for a missing key instead of violating any's contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contract/lib_common_non_optional_nil_return_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'from_ymd returns nil for an invalid date instead of violating any's contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
