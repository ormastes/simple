# Vacuous Print Only Test Detection Specification

> Tests covering no vacuous print-only test files in the MCP feature trees.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vacuous Print Only Test Detection Specification

## Scenarios

### no vacuous print-only test files in the MCP feature trees

#### scans a non-empty set of test files (guards against a vacuous scan)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scans a non-empty set of test files (guards against a vacuous scan)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scans a non-empty set of test files (guards against a vacuous scan)")
# A scan that finds nothing may have scanned nothing. This control MUST
# produce hits, otherwise the absence check below proves nothing.
var total = 0
for dir in SCANNED_DIRS:
    total = total + test_files_in(dir).len()
expect(total).to_be_greater_than(0)
```

</details>

#### detects that the oracle-token rule itself can fail

- detects that the oracle-token rule itself can fail
   - Expected: has_oracle(print_only) is false
   - Expected: has_oracle(asserted) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects that the oracle-token rule itself can fail")
# Positive control for the predicate: a print-only body has no oracle.
val print_only = "fn main():\n    if ok:\n        print(\"ok\")\n    else:\n        print(\"fail\")\n"
expect(has_oracle(print_only)).to_equal(false)
val asserted = "describe \"x\":\n    it \"y\":\n        expect(1).to_equal(1)\n"
expect(has_oracle(asserted)).to_equal(true)
```

</details>

#### finds no test file lacking any assertion

- finds no test file lacking any assertion
   - Expected: bad.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds no test file lacking any assertion")
val bad = vacuous_files()
expect(bad.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering no vacuous print-only test files in the MCP feature trees.
- no vacuous print-only test files in the MCP feature trees

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f8c932aed527b0ae40cc1d68f680bc76bda78aa495e4efda49cd3079391d928a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8c932aed527b0ae40cc1d68f680bc76bda78aa495e4efda49cd3079391d928a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8c932aed527b0ae40cc1d68f680bc76bda78aa495e4efda49cd3079391d928a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.spl
mirror: doc/06_spec/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans a non-empty set of test files (guards against a vacuous scan)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects that the oracle-token rule itself can fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/lib/mcp/vacuous_print_only_test_detection_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds no test file lacking any assertion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
