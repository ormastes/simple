# Module Surface Projected Type Shape Specification

> Tests covering module_surface_projected_type_shape, module_surface_declarations neighbors resolve by name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Surface Projected Type Shape Specification

## Scenarios

### module_surface_projected_type_shape

#### classifies a named field type as named and projects its name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies a named field type as named and projects its name
   - Expected: shape equals `named`
   - Expected: module_surface_projected_type_name(cell, shape) equals `Cell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a named field type as named and projects its name")
val shape = module_surface_projected_type_shape(cell)
expect(shape).to_equal("named")
expect(module_surface_projected_type_name(cell, shape)).to_equal("Cell")
```

</details>

#### classifies an array field type as array and projects the element name

- classifies an array field type as array and projects the element name
   - Expected: shape equals `array`
   - Expected: module_surface_projected_type_name(cells, shape) equals `Cell`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies an array field type as array and projects the element name")
val shape = module_surface_projected_type_shape(cells)
expect(shape).to_equal("array")
expect(module_surface_projected_type_name(cells, shape)).to_equal("Cell")
```

</details>

#### projects an empty name for a type with no scalar identity

- projects an empty name for a type with no scalar identity
   - Expected: shape equals `other`
   - Expected: module_surface_projected_type_name(infer, shape) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("projects an empty name for a type with no scalar identity")
val shape = module_surface_projected_type_shape(infer)
expect(shape).to_equal("other")
expect(module_surface_projected_type_name(infer, shape)).to_equal("")
```

</details>

### module_surface_declarations neighbors resolve by name

#### keeps the callable projection helper importable

- keeps the callable projection helper importable


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the callable projection helper importable")
expect(module_surface_callable_from_function != nil).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering module_surface_projected_type_shape, module_surface_declarations neighbors resolve by name.
- module_surface_projected_type_shape
- module_surface_declarations neighbors resolve by name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `f1bd133a39b654cc2fa6932f7ef842e14c5ec86850eece2cd497a5fa99c288d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f1bd133a39b654cc2fa6932f7ef842e14c5ec86850eece2cd497a5fa99c288d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f1bd133a39b654cc2fa6932f7ef842e14c5ec86850eece2cd497a5fa99c288d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/module_surface_projected_type_shape_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/module_surface_projected_type_shape_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/module_surface_projected_type_shape_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies a named field type as named and projects its name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies an array field type as array and projects the element name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects an empty name for a type with no scalar identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
