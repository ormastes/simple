# Native-Only Mode Tests

> Tests restricted to native compiled mode via `@mode: native` annotation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native-Only Mode Tests

Tests restricted to native compiled mode via `@mode: native` annotation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing Framework |
| Status | Active |
| Source | `test/03_system/feature/mode_filter/native_only_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests restricted to native compiled mode via `@mode: native` annotation.

## Scenarios

### Native-only features

#### runs compiled code

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs compiled code
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs compiled code")
expect(42).to_equal(42)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0e5abfb640f272cdd598365b66441edfbfdb8d71c21d65131b1f6517c72b129b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e5abfb640f272cdd598365b66441edfbfdb8d71c21d65131b1f6517c72b129b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e5abfb640f272cdd598365b66441edfbfdb8d71c21d65131b1f6517c72b129b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **75/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/feature/mode_filter/native_only_spec.spl
mirror: doc/06_spec/03_system/feature/mode_filter/native_only_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=75; blocker cap makes effective=49
doc/06_spec/03_system/feature/mode_filter/native_only_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/mode_filter/native_only_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/mode_filter/native_only_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/mode_filter/native_only_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/feature/mode_filter/native_only_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/mode_filter/native_only_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs compiled code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
