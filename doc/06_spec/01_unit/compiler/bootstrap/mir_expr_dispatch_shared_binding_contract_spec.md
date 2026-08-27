# Mir Expr Dispatch Shared Binding Contract Specification

> Tests covering MIR expression dispatch strict shared bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mir Expr Dispatch Shared Binding Contract Specification

## Scenarios

### MIR expression dispatch strict shared bindings

#### derives return, field, and branch optionals as values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives return, field, and branch optionals as values
   - Expected: source does not contain `self.find_local_hir_type(base_local.id) ?? HirType`
   - Expected: source does not contain `var ret_out: HirType? = nil`
   - Expected: source does not contain `var declared_return: HirType? = nil`
   - Expected: source does not contain `var field_elem_type_override: HirType? = nil`
   - Expected: source does not contain `var field_elem_type_override2: HirType? = nil`
   - Expected: source does not contain `var expected_if_type: HirType? = nil`
   - Expected: source does not contain `var expected_match_type: HirType? = nil`
   - Expected: source does not contain `var enum_raw_bool = enum_eq_local`
   - Expected: source does not contain `var raw_bool_val = eq_local`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derives return, field, and branch optionals as values")
val source = file_read("src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl")

expect(source).to_contain("me field_array_element_override(struct_name: text, field_idx: i64) -> HirType?:")
expect(source).to_contain("val declared_return: HirType? = match cur_builder.current_function:")
expect(source).to_contain("val expected_if_type: HirType? = if expr.has_type_: expr.type_ else: nil")
expect(source).to_contain("val expected_match_type: HirType? = if expr.has_type_: expr.type_ else: nil")
expect(source).to_contain("val enum_raw_bool = match op:")
expect(source).to_contain("val raw_bool_val = match op:")
expect(source).to_contain("match self.find_local_hir_type(base_local.id):")
expect(source).to_contain("if base_hir_type != nil and base_hir_type != 0:")
expect(source.contains("self.find_local_hir_type(base_local.id) ?? HirType")).to_equal(false)
expect(source.contains("var ret_out: HirType? = nil")).to_equal(false)
expect(source.contains("var declared_return: HirType? = nil")).to_equal(false)
expect(source.contains("var field_elem_type_override: HirType? = nil")).to_equal(false)
expect(source.contains("var field_elem_type_override2: HirType? = nil")).to_equal(false)
expect(source.contains("var expected_if_type: HirType? = nil")).to_equal(false)
expect(source.contains("var expected_match_type: HirType? = nil")).to_equal(false)
expect(source.contains("var enum_raw_bool = enum_eq_local")).to_equal(false)
expect(source.contains("var raw_bool_val = eq_local")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR expression dispatch strict shared bindings.
- MIR expression dispatch strict shared bindings

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

- Canonical SPipe generation for source `c977d794f33c6728ecbe57bb48fd9e10dca3103b6682260107913b1e0edda6b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c977d794f33c6728ecbe57bb48fd9e10dca3103b6682260107913b1e0edda6b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c977d794f33c6728ecbe57bb48fd9e10dca3103b6682260107913b1e0edda6b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap/mir_expr_dispatch_shared_binding_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives return, field, and branch optionals as values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
