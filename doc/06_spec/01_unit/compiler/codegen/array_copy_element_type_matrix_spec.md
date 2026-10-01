# Array Copy Element Type Matrix Specification

> Tests covering every integer element type survives a binding copy, non-integer element types survive a binding copy, the element-type matrix agrees across both engines.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array Copy Element Type Matrix Specification

## Scenarios

### every integer element type survives a binding copy

#### copies a [u64] without altering its elements

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- copies a [u64] without altering its elements
- Bind a [u64] to a second name and read element 0
   - Expected: copy[0] equals `11u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [u64] without altering its elements")
step("Bind a [u64] to a second name and read element 0")
val src = _u64s()
val copy = src
expect(copy[0]).to_equal(11u64)
```

</details>

#### copies a [i64] without altering its elements

- copies a [i64] without altering its elements
   - Expected: copy[0] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [i64] without altering its elements")
val src = _i64s()
val copy = src
expect(copy[0]).to_equal(11)
```

</details>

#### copies a [u32] without altering its elements

- copies a [u32] without altering its elements
   - Expected: copy[0] equals `11u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [u32] without altering its elements")
val src = _u32s()
val copy = src
expect(copy[0]).to_equal(11u32)
```

</details>

#### copies a [u16] without altering its elements

- copies a [u16] without altering its elements
   - Expected: copy[0] equals `11u16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [u16] without altering its elements")
val src = _u16s()
val copy = src
expect(copy[0]).to_equal(11u16)
```

</details>

#### copies a [u8] without altering its elements

- copies a [u8] without altering its elements
   - Expected: copy[0] equals `11u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [u8] without altering its elements")
# [u8] is the OTHER packed layout (gc_flags::BYTE_PACKED). It is the
# most likely next home for this class of defect.
val src = _u8s()
val copy = src
expect(copy[0]).to_equal(11u8)
```

</details>

### non-integer element types survive a binding copy

#### copies a [f64] without altering its elements

- copies a [f64] without altering its elements
   - Expected: copy[0] == 11.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [f64] without altering its elements")
val src = _f64s()
val copy = src
expect(copy[0] == 11.5).to_equal(true)
```

</details>

#### copies a [text] without altering its elements

- copies a [text] without altering its elements
   - Expected: copy[0] equals `eleven`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [text] without altering its elements")
val src = _texts()
val copy = src
expect(copy[0]).to_equal("eleven")
```

</details>

#### copies a [bool] without altering its elements

- copies a [bool] without altering its elements
   - Expected: copy[0] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("copies a [bool] without altering its elements")
val src = _bools()
val copy = src
expect(copy[0]).to_equal(true)
```

</details>

### the element-type matrix agrees across both engines

#### gives every element type the same copied value under JIT and interpreter

- gives every element type the same copied value under JIT and interpreter
- Run the whole element-type matrix under the cranelift JIT
- Run the identical program under the tree-walk interpreter
- Each type must report the value that was stored
- A divide-by-eight would turn 11 into 1 — that must not appear
   - Expected: jit_out does not contain `u64=1\n`
- Both engines must agree byte for byte across the whole matrix
   - Expected: jit_out equals `interp_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives every element type the same copied value under JIT and interpreter")
step("Run the whole element-type matrix under the cranelift JIT")
val jit_out = _run_matrix_in_mode("jit")

step("Run the identical program under the tree-walk interpreter")
val interp_out = _run_matrix_in_mode("interpreter")

step("Each type must report the value that was stored")
expect(jit_out).to_contain("u64=11")
expect(jit_out).to_contain("i64=11")
expect(jit_out).to_contain("u8=11")
expect(jit_out).to_contain("u32=11")
expect(jit_out).to_contain("u16=11")
expect(jit_out).to_contain("text=eleven")
expect(jit_out).to_contain("bool=true")

step("A divide-by-eight would turn 11 into 1 — that must not appear")
expect(jit_out.contains("u64=1\n")).to_equal(false)

step("Both engines must agree byte for byte across the whole matrix")
expect(jit_out).to_equal(interp_out)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering every integer element type survives a binding copy, non-integer element types survive a binding copy, the element-type matrix agrees across both engines.
- every integer element type survives a binding copy
- non-integer element types survive a binding copy
- the element-type matrix agrees across both engines

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `8d13dad9a3760a6101deb6bd650e56356c01af66c7154a90fbd60457b8a7bffc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d13dad9a3760a6101deb6bd650e56356c01af66c7154a90fbd60457b8a7bffc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d13dad9a3760a6101deb6bd650e56356c01af66c7154a90fbd60457b8a7bffc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies a [u64] without altering its elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies a [i64] without altering its elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/array_copy_element_type_matrix_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'copies a [u32] without altering its elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
