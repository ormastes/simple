# Mir Switch Calls Shared Binding Contract Specification

> Tests covering MIR switch/call strict shared bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Switch Calls Shared Binding Contract Specification

## Scenarios

### MIR switch/call strict shared bindings

#### derives enum and optional payload values without reassignment

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives enum and optional payload values without reassignment
   - Expected: source does not contain `var payload_hir_type = result_payload_type`
   - Expected: source does not contain `var bound_payload = pl`
   - Expected: source does not contain `var payload_local = raw_payload_local`
   - Expected: source does not contain `var payload_local = pl`
   - Expected: source does not contain `var str_rendered: LocalId? = nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derives enum and optional payload values without reassignment")
val source = file_read("src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl")

expect(source).to_contain("val payload_hir_type: HirType? = match result_payload_type:")
expect(source).to_contain("val bound_payload = match payload_hir_type:")
expect(source).to_contain("val payload_local = match inner.kind:")
expect(source).to_contain("val payload_local = match self.enum_match_expr_type(base):")
expect(source).to_contain("val disc_local = match disc_res:")
expect(source).to_contain("val str_rendered: LocalId? = match str_src.kind:")
expect(source.contains("var payload_hir_type = result_payload_type")).to_equal(false)
expect(source.contains("var bound_payload = pl")).to_equal(false)
expect(source.contains("var payload_local = raw_payload_local")).to_equal(false)
expect(source.contains("var payload_local = pl")).to_equal(false)
expect(source.contains("var str_rendered: LocalId? = nil")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR switch/call strict shared bindings.
- MIR switch/call strict shared bindings

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

- Canonical SPipe generation for source `6634cd6426df86562b809bd166ebed29f3a2ee46ada198f7d9afb58edc56c89d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6634cd6426df86562b809bd166ebed29f3a2ee46ada198f7d9afb58edc56c89d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6634cd6426df86562b809bd166ebed29f3a2ee46ada198f7d9afb58edc56c89d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap/mir_switch_calls_shared_binding_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives enum and optional payload values without reassignment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
