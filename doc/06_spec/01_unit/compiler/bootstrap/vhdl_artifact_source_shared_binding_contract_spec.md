# Vhdl Artifact Source Shared Binding Contract Specification

> Tests covering VHDL artifact source strict shared bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Artifact Source Shared Binding Contract Specification

## Scenarios

### VHDL artifact source strict shared bindings

#### selects the stable source through a scalar index

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects the stable source through a scalar index
   - Expected: source does not contain `var selected: SourceFile? = nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects the stable source through a scalar index")
val source = file_read("src/compiler/80.driver/driver_vhdl_artifact_build.spl")

expect(source).to_contain("var selected_index = -1")
expect(source).to_contain("Some(sources[selected_index])")
expect(source.contains("var selected: SourceFile? = nil")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VHDL artifact source strict shared bindings.
- VHDL artifact source strict shared bindings

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
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `894e9b23a178c55f0edab2ca642373cd1499cebefca5ad7cbd1627673df0f514`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `894e9b23a178c55f0edab2ca642373cd1499cebefca5ad7cbd1627673df0f514`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `894e9b23a178c55f0edab2ca642373cd1499cebefca5ad7cbd1627673df0f514`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap/vhdl_artifact_source_shared_binding_contract_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects the stable source through a scalar index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
