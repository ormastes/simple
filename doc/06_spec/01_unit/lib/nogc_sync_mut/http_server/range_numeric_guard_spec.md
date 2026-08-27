# Range Numeric Guard Specification

> Tests covering nogc sync http server range numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Range Numeric Guard Specification

## Scenarios

### nogc sync http server range numeric guard

#### parses range bounds through a parser that can actually fail

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses range bounds through a parser that can actually fail
   - Expected: s1 equals `10`
   - Expected: e1 equals `20`
   - Expected: s2 equals `5`
   - Expected: e2 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses range bounds through a parser that can actually fail")
# oracle: well-formed bounds round-trip exactly
val (s1, e1) = parse_range_header("bytes=10-20")
expect(s1).to_equal(10)
expect(e1).to_equal(20)
val (s2, e2) = parse_range_header("bytes=5-")
expect(s2).to_equal(5)
expect(e2).to_equal(-1)
```

</details>

#### fails closed on a malformed bound instead of coercing it

- fails closed on a malformed bound instead of coercing it
   - Expected: s1 equals `0`
   - Expected: e1 equals `-1`
   - Expected: s2 equals `0`
   - Expected: e2 equals `-1`
   - Expected: s3 equals `0`
   - Expected: e3 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on a malformed bound instead of coercing it")
# oracle: whole-entity sentinel (0, -1) — never the historical silent (0, 0)
val (s1, e1) = parse_range_header("bytes=abc-def")
expect(s1).to_equal(0)
expect(e1).to_equal(-1)
val (s2, e2) = parse_range_header("bytes=-7")
expect(s2).to_equal(0)
expect(e2).to_equal(-1)
val (s3, e3) = parse_range_header("")
expect(s3).to_equal(0)
expect(e3).to_equal(-1)
```

</details>

#### never reintroduces the coercing to_int spellings

- never reintroduces the coercing to_int spellings
   - Expected: s equals `0`
   - Expected: e equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never reintroduces the coercing to_int spellings")
# oracle: a negative start is rejected, not parsed into a negative slice
val (s, e) = parse_range_header("bytes=abc-20")
expect(s).to_equal(0)
expect(e).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc sync http server range numeric guard.
- nogc sync http server range numeric guard

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f0b7d9f90204b27a9280f6113d066d7f707f6864b53e4a3bc5317bb717c360b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0b7d9f90204b27a9280f6113d066d7f707f6864b53e4a3bc5317bb717c360b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0b7d9f90204b27a9280f6113d066d7f707f6864b53e4a3bc5317bb717c360b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses range bounds through a parser that can actually fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on a malformed bound instead of coercing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/http_server/range_numeric_guard_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never reintroduces the coercing to_int spellings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
