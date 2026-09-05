# Stage4 Hir Value Name Dispatch Specification

> Tests covering Stage4 HIR value-name dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage4 Hir Value Name Dispatch Specification

## Scenarios

### Stage4 HIR value-name dispatch

#### keeps lowercase value expressions out of type resolution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps lowercase value expressions out of type resolution
- Inspect one lowercase value expression
   - Expected: lowering.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps lowercase value expressions out of type resolution")
step("Inspect one lowercase value expression")
val (lowering, _) = lower_value_consumer()

expect(lowering.errors.len()).to_equal(0)
```

</details>

#### registers the imported callable after parameter rebinding

- registers the imported callable after parameter rebinding


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registers the imported callable after parameter rebinding")
val (_, hir) = lower_value_consumer()

val local = hir.symbols.lookup("emit")
val qualified = hir.symbols.lookup("provider.emit")
val registered = local != nil or qualified != nil
expect(registered).to_be(true)
```

</details>

#### rebinds erased Param elements before reading names or types

- rebinds erased Param elements before reading names or types
   - Expected: lowering does not contain `raw_params[first_raw_param].type_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rebinds erased Param elements before reading names or types")
val lowering = read_file_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl")

expect(lowering).to_contain("val receiver_param: Param = raw_params[0]")
expect(lowering).to_contain("val raw_param: Param = raw_params[first_raw_param]")
expect(lowering).to_contain("val raw_param_type: Type = raw_param.type_")
expect(lowering).to_contain("val param: Param = params[i]")
expect(lowering.contains("raw_params[first_raw_param].type_")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage4 HIR value-name dispatch.
- Stage4 HIR value-name dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `155a3203720d0205293e45d50d3218c667f16d8c915162c02483077adf54dd8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `155a3203720d0205293e45d50d3218c667f16d8c915162c02483077adf54dd8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `155a3203720d0205293e45d50d3218c667f16d8c915162c02483077adf54dd8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl
mirror: doc/06_spec/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps lowercase value expressions out of type resolution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the imported callable after parameter rebinding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/stage4_hir_value_name_dispatch_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rebinds erased Param elements before reading names or types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
