# Packed Struct E2e Specification

> Tests covering bitfield existing syntax e2e.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Packed Struct E2e Specification

## Scenarios

### bitfield existing syntax e2e

#### round-trips field read/write

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips field read/write
   - Expected: f.a equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips field read/write")
var f: TestFlags = TestFlags.new(0)
f.a = 3
expect(f.a).to_equal(3)
```

</details>

#### preserves adjacent fields on write

- preserves adjacent fields on write
   - Expected: f.a equals `3`
   - Expected: f.b equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves adjacent fields on write")
var f: TestFlags = TestFlags.new(0)
f.a = 3
f.b = 5
expect(f.a).to_equal(3)
expect(f.b).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/packed_struct_e2e_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bitfield existing syntax e2e.
- bitfield existing syntax e2e

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b24d78182dca6bac39c312bfbca78e35dc257a3da47cafa3e03863a59a3c659`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b24d78182dca6bac39c312bfbca78e35dc257a3da47cafa3e03863a59a3c659`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b24d78182dca6bac39c312bfbca78e35dc257a3da47cafa3e03863a59a3c659`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/packed_struct_e2e_spec.spl
mirror: doc/06_spec/01_unit/compiler/packed_struct_e2e_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/packed_struct_e2e_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/packed_struct_e2e_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/packed_struct_e2e_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/packed_struct_e2e_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips field read/write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/packed_struct_e2e_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves adjacent fields on write' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
