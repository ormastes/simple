# Sibling Describe Red Specification

> Tests covering first sibling, second sibling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sibling Describe Red Specification

## Scenarios

### first sibling

#### executes first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes first
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FIXTURES
step("executes first")
expect(1).to_equal(1)
```

</details>

### second sibling

#### fails deliberately

- fails deliberately
   - Expected: 1 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FIXTURES
step("fails deliberately")
expect(1).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering first sibling, second sibling.
- first sibling
- second sibling

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

- `REQ-SSPEC-FIXTURES`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60387ec28c321bbf1c5cd725c75a3e7a1a0425b8fcca05261d7d9d4377df0bd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60387ec28c321bbf1c5cd725c75a3e7a1a0425b8fcca05261d7d9d4377df0bd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60387ec28c321bbf1c5cd725c75a3e7a1a0425b8fcca05261d7d9d4377df0bd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl
mirror: doc/06_spec/fixtures/pure_simple_tooling/sibling_describe_red_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/fixtures/pure_simple_tooling/sibling_describe_red_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/fixtures/pure_simple_tooling/sibling_describe_red_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/fixtures/pure_simple_tooling/sibling_describe_red_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails deliberately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
