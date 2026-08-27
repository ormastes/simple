# Static File Range Parse Specification

> Tests covering static file Range parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static File Range Parse Specification

## Scenarios

### static file Range parsing

#### parses bounded byte range

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses bounded byte range
   - Expected: range[0] equals `2`
   - Expected: range[1] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses bounded byte range")
val range = static_file_parse_range("bytes=2-4", 10)
expect(range[0]).to_equal(2)
expect(range[1]).to_equal(4)
```

</details>

#### rejects overflowing range numbers

- rejects overflowing range numbers
   - Expected: range[0] equals `-1`
   - Expected: range[1] equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects overflowing range numbers")
val range = static_file_parse_range("bytes=999999999999999999999999999999-", 10)
expect(range[0]).to_equal(-1)
expect(range[1]).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering static file Range parsing.
- static file Range parsing

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

- Canonical SPipe generation for source `a6c7e68fea2ce3a05d32e9ccd0dd063cbeb45555a7b7c604a1042f63041597ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6c7e68fea2ce3a05d32e9ccd0dd063cbeb45555a7b7c604a1042f63041597ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6c7e68fea2ce3a05d32e9ccd0dd063cbeb45555a7b7c604a1042f63041597ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses bounded byte range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/static_file_range_parse_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overflowing range numbers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
