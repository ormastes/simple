# Serial Proxy Baud Guard Specification

> Tests covering serial proxy baud guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Proxy Baud Guard Specification

## Scenarios

### serial proxy baud guard

#### valid baud values

#### parses decimal baud rates

- call parse_baud_or_zero with valid rates
   - Expected: parse_baud_or_zero("9600") equals `9600`
   - Expected: parse_baud_or_zero("115200") equals `115200`
   - Expected: parse_baud_or_zero(" 57600 ") equals `57600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("call parse_baud_or_zero with valid rates")
expect(parse_baud_or_zero("9600")).to_equal(9600)
expect(parse_baud_or_zero("115200")).to_equal(115200)
expect(parse_baud_or_zero(" 57600 ")).to_equal(57600)
```

</details>

#### malformed baud values

#### returns zero for non-numeric, negative, empty input

- call parse_baud_or_zero with malformed values
   - Expected: parse_baud_or_zero("abc") equals `0`
   - Expected: parse_baud_or_zero("-5") equals `0`
   - Expected: parse_baud_or_zero("") equals `0`
   - Expected: parse_baud_or_zero("   ") equals `0`
   - Expected: parse_baud_or_zero("115k2") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("call parse_baud_or_zero with malformed values")
expect(parse_baud_or_zero("abc")).to_equal(0)
expect(parse_baud_or_zero("-5")).to_equal(0)
expect(parse_baud_or_zero("")).to_equal(0)
expect(parse_baud_or_zero("   ")).to_equal(0)
expect(parse_baud_or_zero("115k2")).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/serial_proxy_baud_guard_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering serial proxy baud guard.
- serial proxy baud guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da3332f3f159c1164077d417318a85d639aa9197c4185f6bf5f6bea3367b3d48`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da3332f3f159c1164077d417318a85d639aa9197c4185f6bf5f6bea3367b3d48`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da3332f3f159c1164077d417318a85d639aa9197c4185f6bf5f6bea3367b3d48`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/io/serial_proxy_baud_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/io/serial_proxy_baud_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/serial_proxy_baud_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/serial_proxy_baud_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/serial_proxy_baud_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/io/serial_proxy_baud_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses decimal baud rates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/serial_proxy_baud_guard_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns zero for non-numeric, negative, empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
