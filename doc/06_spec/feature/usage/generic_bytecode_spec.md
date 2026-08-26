# Generic Template Bytecode in SMF

> Tests storage of generic function templates in the SMF (Simple Module Format) bytecode format.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Template Bytecode in SMF

Tests storage of generic function templates in the SMF (Simple Module Format) bytecode format.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GENERIC-001 |
| Category | Compiler |
| Status | In Progress |
| Source | `test/feature/usage/generic_bytecode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests storage of generic function templates in the SMF (Simple Module Format)
bytecode format.

## Syntax

```simple
# Generic function stored in .smf
use std.spec.step

fn identity<T>(x: T) -> T: x
```

## Scenarios

### Generic Template Bytecode in SMF

#### stores generic function templates in .smf

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores generic function templates in .smf
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("stores generic function templates in .smf")
# Placeholder — real SMF generic bytecode tests go here
expect(true).to_equal(true)
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

- Canonical SPipe generation for source `23d4cc0965e2b04545a3c06b683023b67f066b0a86c6efa198432bfdc4d79c97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23d4cc0965e2b04545a3c06b683023b67f066b0a86c6efa198432bfdc4d79c97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23d4cc0965e2b04545a3c06b683023b67f066b0a86c6efa198432bfdc4d79c97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/feature/usage/generic_bytecode_spec.spl
mirror: doc/06_spec/feature/usage/generic_bytecode_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/feature/usage/generic_bytecode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/generic_bytecode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/generic_bytecode_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/feature/usage/generic_bytecode_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores generic function templates in .smf' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
