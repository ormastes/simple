# Shb Import Test Specification

> Tests covering SHB Import Test.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Import Test Specification

## Scenarios

### SHB Import Test

#### imports compiler.shb.shb_hash and hashes source text deterministically

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- import compiler.shb.shb_hash through the normal module path
- hash the same source twice and different sources once
   - Expected: shb_source_hash("fn foo(): 42") equals `shb_source_hash("fn foo(): 42")`
   - Expected: shb_source_hash("fn foo(): 42") == shb_source_hash("fn foo(): 43") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("import compiler.shb.shb_hash through the normal module path")
step("hash the same source twice and different sources once")
expect(shb_source_hash("fn foo(): 42")).to_equal(shb_source_hash("fn foo(): 42"))
expect(shb_source_hash("fn foo(): 42") == shb_source_hash("fn foo(): 43")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/shb/shb_import_test_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHB Import Test.
- SHB Import Test

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

- Canonical SPipe generation for source `4c7ff5491c02f48636186468cfe52b01a9a25b54c13b20c2a81952885e428877`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c7ff5491c02f48636186468cfe52b01a9a25b54c13b20c2a81952885e428877`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c7ff5491c02f48636186468cfe52b01a9a25b54c13b20c2a81952885e428877`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/unit/compiler/shb/shb_import_test_spec.spl
mirror: doc/06_spec/unit/compiler/shb/shb_import_test_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/shb/shb_import_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/shb/shb_import_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/shb/shb_import_test_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports compiler.shb.shb_hash and hashes source text deterministically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
