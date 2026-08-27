# Accept Header Quality Specification

> Tests covering http server accept header quality parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Accept Header Quality Specification

## Scenarios

### http server accept header quality parsing

#### extracts the q= quality value instead of always defaulting to 1.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts the q= quality value instead of always defaulting to 1.0
   - Expected: first[0] equals `text/html`
   - Expected: second[0] equals `application/json`
   - Expected: first[1] equals `0.8`
   - Expected: second[1] equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the q= quality value instead of always defaulting to 1.0")
val parsed = parse_accept_header("text/html;q=0.8,application/json;q=0.5")

val first = parsed[0]
val second = parsed[1]

expect(first[0]).to_equal("text/html")
expect(second[0]).to_equal("application/json")

# Real bug under test: the quality (q=) value was parsed from the
# Accept header string but discarded -- every entry always got
# quality 1.0 regardless of what "q=" said in the source text.
expect(first[1]).to_equal(0.8)
expect(second[1]).to_equal(0.5)
```

</details>

#### defaults quality to 1.0 when no q= parameter is present

- defaults quality to 1.0 when no q= parameter is present
   - Expected: first[0] equals `text/plain`
   - Expected: first[1] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults quality to 1.0 when no q= parameter is present")
val parsed = parse_accept_header("text/plain")
val first = parsed[0]
expect(first[0]).to_equal("text/plain")
expect(first[1]).to_equal(1.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/accept_header_quality_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering http server accept header quality parsing.
- http server accept header quality parsing

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

- Canonical SPipe generation for source `fc8255395da2d840545a872fc5889e772cc0bf54ad83c484c9d645c24503a673`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc8255395da2d840545a872fc5889e772cc0bf54ad83c484c9d645c24503a673`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc8255395da2d840545a872fc5889e772cc0bf54ad83c484c9d645c24503a673`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/http_server/accept_header_quality_spec.spl
mirror: doc/06_spec/01_unit/lib/http_server/accept_header_quality_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http_server/accept_header_quality_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http_server/accept_header_quality_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http_server/accept_header_quality_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/http_server/accept_header_quality_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the q= quality value instead of always defaulting to 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/accept_header_quality_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults quality to 1.0 when no q= parameter is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
