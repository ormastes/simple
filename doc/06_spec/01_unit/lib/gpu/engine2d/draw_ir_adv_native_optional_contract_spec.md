# Draw Ir Adv Native Optional Contract Specification

> Tests covering Draw IR native optional lowering contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Adv Native Optional Contract Specification

## Scenarios

### Draw IR native optional lowering contract

#### concretely rebinds the guarded target evidence without unwrapping the guard result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- concretely rebinds the guarded target evidence without unwrapping the guard result


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("concretely rebinds the guarded target evidence without unwrapping the guard result")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
expect(source).to_contain("if target_font != nil:")
expect(source).to_contain(
    "val evidence: DrawIrTargetFontEvidence = target_font")
expect(source.contains("val evidence = target_font.?")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Draw IR native optional lowering contract.
- Draw IR native optional lowering contract

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
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3155dce6bd2097860142af5d7f1ca03604fa0d2a7df8e9e14d0016871dba4c81`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3155dce6bd2097860142af5d7f1ca03604fa0d2a7df8e9e14d0016871dba4c81`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3155dce6bd2097860142af5d7f1ca03604fa0d2a7df8e9e14d0016871dba4c81`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gpu/engine2d/draw_ir_adv_native_optional_contract_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'concretely rebinds the guarded target evidence without unwrapping the guard result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
