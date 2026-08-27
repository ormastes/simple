# Range Numeric Guard Specification

> Tests covering gc async http server range numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Range Numeric Guard Specification

## Scenarios

### gc async http server range numeric guard

#### parses well-formed byte ranges exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses well-formed byte ranges exactly
   - Expected: parse_range_header("bytes=10-20") equals `(10, 20)`
   - Expected: parse_range_header("bytes=0-0") equals `(0, 0)`
   - Expected: parse_range_header("bytes=5-") equals `(5, -1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses well-formed byte ranges exactly")
# oracle: bytes=START-END parses to (START, END) verbatim
expect(parse_range_header("bytes=10-20")).to_equal((10, 20))
expect(parse_range_header("bytes=0-0")).to_equal((0, 0))
# oracle: open-ended range keeps end = -1 (whole remainder)
expect(parse_range_header("bytes=5-")).to_equal((5, -1))
```

</details>

#### fails closed on a malformed bound instead of coercing it

- fails closed on a malformed bound instead of coercing it
   - Expected: parse_range_header("bytes=abc-def") equals `(0, -1)`
   - Expected: parse_range_header("bytes=abc-") equals `(0, -1)`
   - Expected: parse_range_header("bytes=-def") equals `(0, -1)`
   - Expected: parse_range_header("bytes=1x-9") equals `(0, -1)`
   - Expected: parse_range_header("items=2-5") equals `(0, -1)`
   - Expected: create_content_range(10, 20, 100) equals `bytes 10-20/100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on a malformed bound instead of coercing it")
# oracle: non-numeric bounds must yield the whole-entity sentinel (0, -1),
# never a silently-coerced (0, 0)
expect(parse_range_header("bytes=abc-def")).to_equal((0, -1))
expect(parse_range_header("bytes=abc-")).to_equal((0, -1))
expect(parse_range_header("bytes=-def")).to_equal((0, -1))
expect(parse_range_header("bytes=1x-9")).to_equal((0, -1))
# oracle: non-bytes units are ignored
expect(parse_range_header("items=2-5")).to_equal((0, -1))
# oracle: Content-Range formatting round-trips parsed bounds
expect(create_content_range(10, 20, 100)).to_equal("bytes 10-20/100")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/range_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc async http server range numeric guard.
- gc async http server range numeric guard

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

- Canonical SPipe generation for source `d73f1934d1934fa90b99d3111076a1ec4326469dfe0b6ced31468acb026c59c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d73f1934d1934fa90b99d3111076a1ec4326469dfe0b6ced31468acb026c59c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d73f1934d1934fa90b99d3111076a1ec4326469dfe0b6ced31468acb026c59c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/http_server/range_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/http_server/range_numeric_guard_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http_server/range_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http_server/range_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http_server/range_numeric_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses well-formed byte ranges exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/range_numeric_guard_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on a malformed bound instead of coercing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
