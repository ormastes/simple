# Compiler Integration Specification

> <details>

<!-- sdn-diagram:id=compiler_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_integration_spec -> std
compiler_integration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Integration Specification

## Scenarios

### Compiler Documentation Warnings

#### checks single file for missing documentation

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create test file
val test_file = "test_doc_warn.spl"
val content = "fn undocumented_function():{NL}    42{NL}"

val write_ok = file_write(test_file, content)
expect(write_ok).to_equal(true)

# Check for warnings
val warnings = check_file_documentation(test_file)

# Should find warning for undocumented function
expect(warnings.len()).to_be_greater_than(0)

# Cleanup
val cleanup = shell("rm -f {test_file}")
expect(cleanup.exit_code).to_equal(0)
```

</details>

#### returns empty warnings for documented file

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create test file with documentation
val test_file = "test_doc_ok.spl"
val content = "# This function is documented{NL}fn documented_function():{NL}    42{NL}"

val write_ok = file_write(test_file, content)
expect(write_ok).to_equal(true)

# Check for warnings
val warnings = check_file_documentation(test_file)

# Should find no warnings
expect(warnings.len()).to_equal(0)

# Cleanup
val cleanup = shell("rm -f {test_file}")
expect(cleanup.exit_code).to_equal(0)
```

</details>

#### formats warning message correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create test DocItem
val item = DocItem(
    name: "test_fn",
    kind: "fn",
    file: "test.spl",
    line: 42,
    has_comment: false,
    has_docstring: false,
    comment_text: "",
    docstring_text: ""
)

val warning = format_warning(item)

# Should contain function name
expect(warning.contains("test_fn")).to_equal(true)

# Should contain file and line
expect(warning.contains("test.spl:42")).to_equal(true)

# Should contain "missing documentation"
expect(warning.contains("missing documentation")).to_equal(true)
```

</details>

#### checks multiple files

<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create two test files
val test_file1 = "test_multi1.spl"
val test_file2 = "test_multi2.spl"

val content1 = "fn undoc1():{NL}    1{NL}"
val content2 = "# Documented{NL}fn doc2():{NL}    2{NL}"

val write1 = file_write(test_file1, content1)
val write2 = file_write(test_file2, content2)

expect(write1).to_equal(true)
expect(write2).to_equal(true)

# Check both files
val files = [test_file1, test_file2]
val result = check_multiple_files(files)
val all_warnings = result.0
val files_with_warnings = result.1

# Should find warnings in first file only
expect(files_with_warnings.len()).to_equal(1)
expect(all_warnings.len()).to_be_greater_than(0)

# Cleanup
val cleanup1 = shell("rm -f {test_file1}")
val cleanup2 = shell("rm -f {test_file2}")
expect(cleanup1.exit_code).to_equal(0)
expect(cleanup2.exit_code).to_equal(0)
```

</details>

#### handles non-existent file gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_file_documentation("nonexistent_file_xyz.spl")

# Should return empty array, not crash
expect(warnings.len()).to_equal(0)
```

</details>

#### detects undocumented struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "test_struct.spl"
val content = "struct UndocumentedStruct:{NL}    field: i64{NL}"

val write_ok = file_write(test_file, content)
expect(write_ok).to_equal(true)

val warnings = check_file_documentation(test_file)

# Should find warning for struct
expect(warnings.len()).to_be_greater_than(0)

# Check warning mentions struct
val first_warning = warnings[0]
expect(first_warning.contains("struct")).to_equal(true)

# Cleanup
val cleanup = shell("rm -f {test_file}")
expect(cleanup.exit_code).to_equal(0)
```

</details>

#### detects undocumented class

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "test_class.spl"
val content = "class UndocumentedClass:{NL}    field: i64{NL}"

val write_ok = file_write(test_file, content)
expect(write_ok).to_equal(true)

val warnings = check_file_documentation(test_file)

# Should find warning for class
expect(warnings.len()).to_be_greater_than(0)

# Cleanup
val cleanup = shell("rm -f {test_file}")
expect(cleanup.exit_code).to_equal(0)
```

</details>

#### detects undocumented enum

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "test_enum.spl"
val content = "enum UndocumentedEnum:{NL}    Variant1{NL}    Variant2{NL}"

val write_ok = file_write(test_file, content)
expect(write_ok).to_equal(true)

val warnings = check_file_documentation(test_file)

# Should find warning for enum
expect(warnings.len()).to_be_greater_than(0)

# Cleanup
val cleanup = shell("rm -f {test_file}")
expect(cleanup.exit_code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/compiler_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Compiler Documentation Warnings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
