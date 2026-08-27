# Advanced Types Specification

> Tests covering Advanced Type Integration via Compiler Facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Types Specification

## Scenarios

### Advanced Type Integration via Compiler Facade

#### rejects recursive value layouts but permits class and array indirection

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects recursive value layouts but permits class and array indirection
   - Expected: direct.is_success() is false
   - Expected: mutual.is_success() is false
   - Expected: reference.is_success() is true
   - Expected: array.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects recursive value layouts but permits class and array indirection")
val direct_path = "/tmp/sml_advanced_types_direct_value_cycle.spl"
val mutual_path = "/tmp/sml_advanced_types_mutual_value_cycle.spl"
val reference_path = "/tmp/sml_advanced_types_reference_cycle.spl"
val array_path = "/tmp/sml_advanced_types_array_value_cycle.spl"
write_file(direct_path, direct_value_cycle_program())
write_file(mutual_path, mutual_value_cycle_program())
write_file(reference_path, reference_cycle_program())
write_file(array_path, array_cycle_program())

val direct = check_file(direct_path)
val mutual = check_file(mutual_path)
val reference = check_file(reference_path)
val array = check_file(array_path)

expect(direct.is_success()).to_equal(false)
expect(direct.get_errors().join("\n")).to_contain("recursive by-value struct layout: Direct.next -> Direct")
expect(mutual.is_success()).to_equal(false)
expect(mutual.get_errors().join("\n")).to_contain("recursive by-value struct layout:")
expect(mutual.get_errors().join("\n")).to_contain("Left")
expect(mutual.get_errors().join("\n")).to_contain("Right")
expect(reference.is_success()).to_equal(true)
expect(array.is_success()).to_equal(true)

delete_file(direct_path)
delete_file(mutual_path)
delete_file(reference_path)
delete_file(array_path)
```

</details>

#### rejects a recursive value layout split across imported modules

- rejects a recursive value layout split across imported modules
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects a recursive value layout split across imported modules")
val left_path = "build/sml_value_layout_left.spl"
val right_path = "build/sml_value_layout_right.spl"
write_file(left_path, cross_module_left_program())
write_file(right_path, cross_module_right_program())

val result = compile_files([left_path, right_path], CompileMode.Check)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("recursive by-value struct layout:")
expect(result.get_errors().join("\n")).to_contain("Left")
expect(result.get_errors().join("\n")).to_contain("Right")
delete_file(left_path)
delete_file(right_path)
```

</details>

#### when checking supported advanced type forms

#### accepts unions with payloads and pattern matching

- accepts unions with payloads and pattern matching
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts unions with payloads and pattern matching")
val src_path = "/tmp/sml_advanced_types_union_ok.spl"
val out_path = "/tmp/sml_advanced_types_union_ok.smf"
delete_file(out_path)
write_file(src_path, union_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### compiles union-based control flow into an smf artifact

- compiles union-based control flow into an smf artifact
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles union-based control flow into an smf artifact")
val src_path = "/tmp/sml_advanced_types_union_compile.spl"
val out_path = "/tmp/sml_advanced_types_union_compile.smf"
delete_file(out_path)
write_file(src_path, union_program())

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### accepts result propagation with the try operator

- accepts result propagation with the try operator
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts result propagation with the try operator")
val src_path = "/tmp/sml_advanced_types_try_ok.spl"
val out_path = "/tmp/sml_advanced_types_try_ok.smf"
delete_file(out_path)
write_file(src_path, try_operator_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### compiles a try-operator program into an smf artifact

- compiles a try-operator program into an smf artifact
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles a try-operator program into an smf artifact")
val src_path = "/tmp/sml_advanced_types_try_compile.spl"
val out_path = "/tmp/sml_advanced_types_try_compile.smf"
delete_file(out_path)
write_file(src_path, try_operator_program())

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### accepts SIMD vector annotations in function signatures

- accepts SIMD vector annotations in function signatures
   - Expected: result.is_success() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts SIMD vector annotations in function signatures")
val src_path = "/tmp/sml_advanced_types_simd_ok.spl"
val out_path = "/tmp/sml_advanced_types_simd_ok.smf"
delete_file(out_path)
write_file(src_path, simd_annotation_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### compiles a program with SIMD-typed signatures

- compiles a program with SIMD-typed signatures
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiles a program with SIMD-typed signatures")
val src_path = "/tmp/sml_advanced_types_simd_compile.spl"
val out_path = "/tmp/sml_advanced_types_simd_compile.smf"
delete_file(out_path)
write_file(src_path, simd_annotation_program())

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(out_path)).to_equal(true)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### when checking unsupported advanced type syntax

#### rejects intersection type syntax with a concrete parser error

- rejects intersection type syntax with a concrete parser error
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects intersection type syntax with a concrete parser error")
val src_path = "/tmp/sml_advanced_types_intersection_bad.spl"
val out_path = "/tmp/sml_advanced_types_intersection_bad.smf"
delete_file(out_path)
write_file(src_path, intersection_syntax_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("Ampersand")
delete_file(src_path)
delete_file(out_path)
```

</details>

#### rejects refinement-style where clauses with a concrete parser error

- rejects refinement-style where clauses with a concrete parser error
   - Expected: result.is_success() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects refinement-style where clauses with a concrete parser error")
val src_path = "/tmp/sml_advanced_types_refinement_bad.spl"
val out_path = "/tmp/sml_advanced_types_refinement_bad.smf"
delete_file(out_path)
write_file(src_path, refinement_syntax_program())

val result = check_file(src_path)

expect(result.is_success()).to_equal(false)
expect(result.get_errors().join("\n")).to_contain("Where")
delete_file(src_path)
delete_file(out_path)
```

</details>

#### does not emit an artifact for rejected intersection syntax

- does not emit an artifact for rejected intersection syntax
   - Expected: result.is_ok() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not emit an artifact for rejected intersection syntax")
val src_path = "/tmp/sml_advanced_types_intersection_compile_bad.spl"
val out_path = "/tmp/sml_advanced_types_intersection_compile_bad.smf"
delete_file(out_path)
write_file(src_path, intersection_syntax_program())

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(false)
expect(rt_file_exists(out_path)).to_equal(false)
delete_file(src_path)
delete_file(out_path)
```

</details>

#### does not emit an artifact for rejected refinement syntax

- does not emit an artifact for rejected refinement syntax
   - Expected: result.is_ok() is false
   - Expected: rt_file_exists(out_path) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not emit an artifact for rejected refinement syntax")
val src_path = "/tmp/sml_advanced_types_refinement_compile_bad.spl"
val out_path = "/tmp/sml_advanced_types_refinement_compile_bad.smf"
delete_file(out_path)
write_file(src_path, refinement_syntax_program())

val result = compile_to_smf(src_path, out_path)

expect(result.is_ok()).to_equal(false)
expect(rt_file_exists(out_path)).to_equal(false)
delete_file(src_path)
delete_file(out_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/advanced_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Advanced Type Integration via Compiler Facade.
- Advanced Type Integration via Compiler Facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `965c57d6edbd32cece23abf0d84b07a47e1c7612278cab76a12cf9904ba56f0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `965c57d6edbd32cece23abf0d84b07a47e1c7612278cab76a12cf9904ba56f0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `965c57d6edbd32cece23abf0d84b07a47e1c7612278cab76a12cf9904ba56f0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/compiler/advanced_types_spec.spl
mirror: doc/06_spec/02_integration/compiler/advanced_types_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/advanced_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/advanced_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/advanced_types_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects recursive value layouts but permits class and array indirection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/advanced_types_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a recursive value layout split across imported modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/advanced_types_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts unions with payloads and pattern matching' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
