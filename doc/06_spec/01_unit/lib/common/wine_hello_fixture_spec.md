# Wine Hello Fixture Specification

> Tests covering Wine hello fixture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Hello Fixture Specification

## Scenarios

### Wine hello fixture

#### builds the known executable milestone fixture

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds the known executable milestone fixture
   - Expected: result.status equals `executed`
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`
   - Expected: result.stdout_handle equals `-11`
   - Expected: result.bytes_written equals `25`
   - Expected: result.exit_code equals `0`
   - Expected: wine_hello_exe_can_execute(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds the known executable milestone fixture")
val result = wine_hello_exe_probe(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.stdout_handle).to_equal(-11)
expect(result.bytes_written).to_equal(25)
expect(result.exit_code).to_equal(0)
expect(wine_hello_exe_can_execute(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_hello_fixture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine hello fixture.
- Wine hello fixture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `5d0f666e953d869c3ba4ed7e642aa340ce906f67082c4fcd75197f4d38b2bcd9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5d0f666e953d869c3ba4ed7e642aa340ce906f67082c4fcd75197f4d38b2bcd9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5d0f666e953d869c3ba4ed7e642aa340ce906f67082c4fcd75197f4d38b2bcd9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/wine_hello_fixture_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_hello_fixture_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_hello_fixture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_hello_fixture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_hello_fixture_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_hello_fixture_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds the known executable milestone fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
