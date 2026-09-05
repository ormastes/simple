# Int Width Boxing Matrix Class Specification

> Tests covering integer width boxing matrix across erased-slot boundaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Int Width Boxing Matrix Class Specification

## Scenarios

### integer width boxing matrix across erased-slot boundaries

<details>
<summary>Advanced: runs the matrix to completion under the interpreter (control arm)</summary>

#### runs the matrix to completion under the interpreter (control arm)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the matrix to completion under the interpreter (control arm)
- Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter
- A truncated run is not evidence — the probe must reach its end marker
- The interpreter is the control arm and must be clean
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs the matrix to completion under the interpreter (control arm)")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("A truncated run is not evidence — the probe must reach its end marker")
expect(interp).to_contain("INT_WIDTH_BOXING_MATRIX PROBE: DONE")

step("The interpreter is the control arm and must be clean")
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>


</details>

#### round-trips every integer width through every erased slot on the JIT

- round-trips every integer width through every erased slot on the JIT
- Run the same probe under SIMPLE_EXECUTION_MODE=jit
- Boundary 1 — array literal, signed widths
- Boundary 1 — unsigned widths; u64 is the width the untagging `>> 3` defect hit
- Boundary 2 — a typed array literal returned from a function is a separate lowering path
- Boundary 3 — push() writes through a different lowering than the literal; both directions must agree
- Boundary 4 — a tuple slot
- Neither known numeric signature of the class: `v << 3 | TAG_SPECIAL`, and an untagging `>> 3`
- A never-unboxed tagged word leaks as `<value:0x..>` or `<special:N>`
   - Expected: jit does not contain `<value:0x`
   - Expected: jit does not contain `<special:`
- Fixing the i8/bool machine-width collision must not push bool into the integer tag
- The aggregate verdict — any FAIL line anywhere is a red
   - Expected: jit does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips every integer width through every erased slot on the JIT")
step("Run the same probe under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")
expect(jit).to_contain("INT_WIDTH_BOXING_MATRIX PROBE: DONE")

step("Boundary 1 — array literal, signed widths")
expect(jit).to_contain("PASS lit_i8_0")
expect(jit).to_contain("PASS lit_i16_0")
expect(jit).to_contain("PASS lit_i32_0")
expect(jit).to_contain("PASS lit_i64_0")

step("Boundary 1 — unsigned widths; u64 is the width the untagging `>> 3` defect hit")
expect(jit).to_contain("PASS lit_u8_0")
expect(jit).to_contain("PASS lit_u16_0")
expect(jit).to_contain("PASS lit_u32_0")
expect(jit).to_contain("PASS lit_u64_0")

step("Boundary 2 — a typed array literal returned from a function is a separate lowering path")
expect(jit).to_contain("PASS ret_i8_0")
expect(jit).to_contain("PASS ret_i16_0")
expect(jit).to_contain("PASS ret_i32_0")
expect(jit).to_contain("PASS ret_i64_0")
expect(jit).to_contain("PASS ret_u8_0")
expect(jit).to_contain("PASS ret_u16_0")
expect(jit).to_contain("PASS ret_u32_0")
expect(jit).to_contain("PASS ret_u64_0")

step("Boundary 3 — push() writes through a different lowering than the literal; both directions must agree")
expect(jit).to_contain("PASS push_i8_0")
expect(jit).to_contain("PASS push_i16_0")
expect(jit).to_contain("PASS push_i32_0")
expect(jit).to_contain("PASS push_i64_0")
expect(jit).to_contain("PASS push_u8_0")
expect(jit).to_contain("PASS push_u32_0")
expect(jit).to_contain("PASS push_u64_0")

step("Boundary 4 — a tuple slot")
expect(jit).to_contain("PASS tuple_i8_0")
expect(jit).to_contain("PASS tuple_i32_0")
expect(jit).to_contain("PASS tuple_i64_0")
expect(jit).to_contain("PASS tuple_u64_0")

step("Neither known numeric signature of the class: `v << 3 | TAG_SPECIAL`, and an untagging `>> 3`")
expect(jit).to_contain("PASS sig_tag_special_shift_i8")
expect(jit).to_contain("PASS sig_untag_shift_u64")

step("A never-unboxed tagged word leaks as `<value:0x..>` or `<special:N>`")
expect(jit.contains("<value:0x")).to_equal(false)
expect(jit.contains("<special:")).to_equal(false)

step("Fixing the i8/bool machine-width collision must not push bool into the integer tag")
expect(jit).to_contain("PASS bool_elem_true")
expect(jit).to_contain("PASS bool_elem_false")

step("The aggregate verdict — any FAIL line anywhere is a red")
expect(jit.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering integer width boxing matrix across erased-slot boundaries.
- integer width boxing matrix across erased-slot boundaries

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fc7ebbe654acb16304025b49c931c2c16c0ffafd8b6aa70c0249d22900ea9fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fc7ebbe654acb16304025b49c931c2c16c0ffafd8b6aa70c0249d22900ea9fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fc7ebbe654acb16304025b49c931c2c16c0ffafd8b6aa70c0249d22900ea9fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the matrix to completion under the interpreter (control arm)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips every integer width through every erased slot on the JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
