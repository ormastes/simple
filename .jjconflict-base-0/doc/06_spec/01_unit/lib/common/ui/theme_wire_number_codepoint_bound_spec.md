# Theme Wire Number Codepoint Bound Specification

> Tests covering theme wire unsigned number parsing, theme wire signed number parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Theme Wire Number Codepoint Bound Specification

## Scenarios

### theme wire unsigned number parsing

#### accepts canonical ASCII digits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts canonical ASCII digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts canonical ASCII digits")
assert_equal(_theme_wire_parse_u32("0").is_ok(), true)
assert_equal(_theme_wire_parse_u32("4294967295").is_ok(), true)
```

</details>

#### rejects an empty, noncanonical or overflowing number

- rejects an empty, noncanonical or overflowing number


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty, noncanonical or overflowing number")
assert_equal(_theme_wire_parse_u32("").is_ok(), false)
assert_equal(_theme_wire_parse_u32("01").is_ok(), false)
assert_equal(_theme_wire_parse_u32("4294967296").is_ok(), false)
```

</details>

#### rejects non-ASCII digits without over-running the codepoint index

- rejects non-ASCII digits without over-running the codepoint index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-ASCII digits without over-running the codepoint index")
assert_equal(_theme_wire_parse_u32("1é").is_ok(), false)
assert_equal(_theme_wire_parse_u32("é1").is_ok(), false)
assert_equal(_theme_wire_parse_u32("12漢").is_ok(), false)
assert_equal(_theme_wire_parse_u32("😀").is_ok(), false)
```

</details>

### theme wire signed number parsing

#### accepts canonical ASCII signed digits

- accepts canonical ASCII signed digits


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts canonical ASCII signed digits")
assert_equal(_theme_wire_parse_i32("0").is_ok(), true)
assert_equal(_theme_wire_parse_i32("-1").is_ok(), true)
assert_equal(_theme_wire_parse_i32("2147483647").is_ok(), true)
assert_equal(_theme_wire_parse_i32("-2147483648").is_ok(), true)
```

</details>

#### rejects noncanonical, negative-zero and overflowing forms

- rejects noncanonical, negative-zero and overflowing forms


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects noncanonical, negative-zero and overflowing forms")
assert_equal(_theme_wire_parse_i32("").is_ok(), false)
assert_equal(_theme_wire_parse_i32("-0").is_ok(), false)
assert_equal(_theme_wire_parse_i32("-").is_ok(), false)
assert_equal(_theme_wire_parse_i32("2147483648").is_ok(), false)
```

</details>

#### rejects non-ASCII digits without over-running the codepoint index

- rejects non-ASCII digits without over-running the codepoint index


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-ASCII digits without over-running the codepoint index")
assert_equal(_theme_wire_parse_i32("-1é").is_ok(), false)
assert_equal(_theme_wire_parse_i32("-é").is_ok(), false)
assert_equal(_theme_wire_parse_i32("12漢").is_ok(), false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering theme wire unsigned number parsing, theme wire signed number parsing.
- theme wire unsigned number parsing
- theme wire signed number parsing

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

- Canonical SPipe generation for source `17af3a0e67b1e9dea6ae2971a976b6daf981314a816a99a6c45bd3c6512bdaa6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17af3a0e67b1e9dea6ae2971a976b6daf981314a816a99a6c45bd3c6512bdaa6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17af3a0e67b1e9dea6ae2971a976b6daf981314a816a99a6c45bd3c6512bdaa6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts canonical ASCII digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty, noncanonical or overflowing number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/theme_wire_number_codepoint_bound_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-ASCII digits without over-running the codepoint index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
