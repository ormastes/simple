# Processing Ir Metal Valid Unavailable Specification

> Tests covering Linux Metal ProcessingIR unavailable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Processing Ir Metal Valid Unavailable Specification

## Scenarios

### Linux Metal ProcessingIR unavailable

#### rejects valid canonical FillU32 without a Metal backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects valid canonical FillU32 without a Metal backend
   - Expected: result.completed is false
   - Expected: result.reason equals `metal-unavailable`
   - Expected: result.values.len() equals `0`
   - Expected: result.backend_handle equals `0`
   - Expected: result.device_identity equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects valid canonical FillU32 without a Metal backend")
val result = processing_ir_execute_metal(processing_ir_fill_u32(64, 0xA1B2C3D4u32))
expect(result.completed).to_equal(false)
expect(result.reason).to_equal("metal-unavailable")
expect(result.values.len()).to_equal(0)
expect(result.backend_handle).to_equal(0)
expect(result.device_identity).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/processing_ir_metal_valid_unavailable_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Linux Metal ProcessingIR unavailable.
- Linux Metal ProcessingIR unavailable

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f490068a1ab5a6b9e643988f2b0384a62b82dd5850b7da7e630866ffd5ed90f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f490068a1ab5a6b9e643988f2b0384a62b82dd5850b7da7e630866ffd5ed90f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f490068a1ab5a6b9e643988f2b0384a62b82dd5850b7da7e630866ffd5ed90f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/rendering/processing_ir_metal_valid_unavailable_spec.spl
mirror: doc/06_spec/02_integration/rendering/processing_ir_metal_valid_unavailable_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/processing_ir_metal_valid_unavailable_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/processing_ir_metal_valid_unavailable_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/processing_ir_metal_valid_unavailable_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/processing_ir_metal_valid_unavailable_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects valid canonical FillU32 without a Metal backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
