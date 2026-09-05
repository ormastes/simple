# Jit Container I64 Boxing Defect Class Specification

> Tests covering positive control: small values round-trip through every container on both engines, defect class: a large i64 must survive every container kind.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Container I64 Boxing Defect Class Specification

## Scenarios

### positive control: small values round-trip through every container on both engines

#### produces a non-empty transcript on both engines

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces a non-empty transcript on both engines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a non-empty transcript on both engines")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_true(interp.len() > 0)
assert_true(jit.len() > 0)
```

</details>

#### agrees on the small value through a scalar, a list, a nested list, a struct and a tuple

- agrees on the small value through a scalar, a list, a nested list, a struct and a tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on the small value through a scalar, a list, a nested list, a struct and a tuple")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_reading(jit, "ctl_scalar"), _reading(interp, "ctl_scalar"))
assert_equal(_reading(jit, "ctl_list"), _reading(interp, "ctl_list"))
assert_equal(_reading(jit, "ctl_nested"), _reading(interp, "ctl_nested"))
assert_equal(_reading(jit, "ctl_struct"), _reading(interp, "ctl_struct"))
assert_equal(_reading(jit, "ctl_tuple"), _reading(interp, "ctl_tuple"))
```

</details>

#### reads a real value for every control, not an empty string

- reads a real value for every control, not an empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a real value for every control, not an empty string")
# A missing key would make every comparison above compare "" to "",
# which passes vacuously. Pin the actual content.
val interp = _run_lane("interpret")
assert_equal(_reading(interp, "ctl_list"), "ctl_list=7")
assert_equal(_reading(interp, "ctl_tuple"), "ctl_tuple=7")
```

</details>

### defect class: a large i64 must survive every container kind

#### survives a scalar (already correct -- guards against regression)

- survives a scalar (already correct -- guards against regression)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("survives a scalar (already correct -- guards against regression)")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_reading(jit, "big_scalar"), _reading(interp, "big_scalar"))
```

</details>

#### survives a struct field (already correct -- guards against regression)

- survives a struct field (already correct -- guards against regression)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("survives a struct field (already correct -- guards against regression)")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_reading(jit, "big_struct"), _reading(interp, "big_struct"))
```

</details>

#### survives a list element

- survives a list element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("survives a list element")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_reading(jit, "big_list"), _reading(interp, "big_list"))
```

</details>

#### survives a nested list element

- survives a nested list element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("survives a nested list element")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_reading(jit, "big_nested"), _reading(interp, "big_nested"))
```

</details>

#### survives a tuple element

- survives a tuple element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("survives a tuple element")
val interp = _run_lane("interpret")
val jit = _run_lane("jit")
assert_equal(_reading(jit, "big_tuple"), _reading(interp, "big_tuple"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering positive control: small values round-trip through every container on both engines, defect class: a large i64 must survive every container kind.
- positive control: small values round-trip through every container on both engines
- defect class: a large i64 must survive every container kind

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `03dd7e3e1d4a7b574c2aa054133b3718b5ee74f01e06553cabfaac8293ea927f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `03dd7e3e1d4a7b574c2aa054133b3718b5ee74f01e06553cabfaac8293ea927f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `03dd7e3e1d4a7b574c2aa054133b3718b5ee74f01e06553cabfaac8293ea927f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.spl
mirror: doc/06_spec/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces a non-empty transcript on both engines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on the small value through a scalar, a list, a nested list, a struct and a tuple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/jit_container_i64_boxing_defect_class_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a real value for every control, not an empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
