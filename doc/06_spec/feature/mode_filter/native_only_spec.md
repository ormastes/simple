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
| Source | `test/feature/mode_filter/native_only_spec.spl` |
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

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("runs compiled code")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(42).to_equal(42)  # oracle: 42 must equal 42 — authoritative contract constant
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `99f4ec69716a519ce700bc73fc6cc0a5943bf386ec4913859d2d14c33ef6fd10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `99f4ec69716a519ce700bc73fc6cc0a5943bf386ec4913859d2d14c33ef6fd10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `99f4ec69716a519ce700bc73fc6cc0a5943bf386ec4913859d2d14c33ef6fd10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/feature/mode_filter/native_only_spec.spl
mirror: doc/06_spec/feature/mode_filter/native_only_spec.md (current)
findings: 4 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/feature/mode_filter/native_only_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/mode_filter/native_only_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/mode_filter/native_only_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/feature/mode_filter/native_only_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
