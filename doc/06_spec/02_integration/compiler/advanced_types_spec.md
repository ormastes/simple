# Advanced Types Specification

> 1. delete file

<!-- sdn-diagram:id=advanced_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=advanced_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

advanced_types_spec -> std
advanced_types_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=advanced_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Types Specification

## Scenarios

### Advanced Type Integration via Compiler Facade

#### when checking supported advanced type forms

#### accepts unions with payloads and pattern matching

1. delete file
2. write file
   - Expected: result.is_success() is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_success() is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_success() is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(out_path) is true
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_success() is false
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_success() is false
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_ok() is false
   - Expected: rt_file_exists(out_path) is false
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. delete file
2. write file
   - Expected: result.is_ok() is false
   - Expected: rt_file_exists(out_path) is false
3. delete file
4. delete file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Advanced Type Integration via Compiler Facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
