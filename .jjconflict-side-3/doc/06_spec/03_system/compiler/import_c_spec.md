# Import C Specification

> <details>

<!-- sdn-diagram:id=import_c_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=import_c_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

import_c_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=import_c_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import C Specification

## Scenarios

### import_c — AST types

#### defines CImport struct with header_path and struct_matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImport:")).to_equal(true)
expect(src.contains("header_path: text")).to_equal(true)
expect(src.contains("struct_matches: [CImportMatch]")).to_equal(true)
```

</details>

#### defines CImportMatch with simple_name, c_name, strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportMatch:")).to_equal(true)
expect(src.contains("simple_name: text")).to_equal(true)
expect(src.contains("c_name: text")).to_equal(true)
```

</details>

#### defines CImportDefine for user define forwarding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportDefine:")).to_equal(true)
expect(src.contains("define_forwards: [CImportDefine]")).to_equal(true)
```

</details>

#### defines CImportResult with structs and errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportResult:")).to_equal(true)
expect(src.contains("structs: [CImportedStruct]")).to_equal(true)
expect(src.contains("errors: [text]")).to_equal(true)
```

</details>

#### defines CImportedStruct with layout_kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportedStruct:")).to_equal(true)
expect(src.contains("layout_kind: text")).to_equal(true)
```

</details>

#### defines CImportedField with aka_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportedField:")).to_equal(true)
expect(src.contains("aka_name: text")).to_equal(true)
```

</details>

### import_c — header resolution

#### defines resolve_c_header function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("fn resolve_c_header(header_path: text, include_paths: [text]) -> text")).to_equal(true)
```

</details>

#### checks src/include as default path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("src/include/")).to_equal(true)
```

</details>

#### validates self-contained headers reject system includes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("fn validate_self_contained")).to_equal(true)
expect(src.contains("system include not allowed")).to_equal(true)
```

</details>

#### defines default_include_paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("fn default_include_paths")).to_equal(true)
```

</details>

### import_c — C to Simple conversion

#### defines convert_c_structs entry point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("fn convert_c_structs")).to_equal(true)
```

</details>

#### defines c_type_to_simple type mapping

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("fn c_type_to_simple(c_type: text, is_pointer: bool) -> text")).to_equal(true)
```

</details>

#### maps standard C integer types to Simple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("uint8_t")).to_equal(true)
expect(src.contains("uint32_t")).to_equal(true)
expect(src.contains("int64_t")).to_equal(true)
expect(src.contains("size_t")).to_equal(true)
```

</details>

#### maps pointer types to ptr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("return \"ptr\"")).to_equal(true)
```

</details>

#### uses c_find_matching_struct for name resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("c_find_matching_struct")).to_equal(true)
```

</details>

### import_c — field matching

#### defines match_fields function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn match_fields")).to_equal(true)
```

</details>

#### resolves aka aliases with exact match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn find_aka_field")).to_equal(true)
expect(src.contains("sf.aka_name")).to_equal(true)
```

</details>

#### defines FieldMatch and FieldMatchResult

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("struct FieldMatch:")).to_equal(true)
expect(src.contains("struct FieldMatchResult:")).to_equal(true)
```

</details>

#### reports unmatched Simple fields as errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("unmatched_simple")).to_equal(true)
expect(src.contains("field has no match in C struct")).to_equal(true)
```

</details>

#### tracks unmatched C fields for warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("unmatched_c")).to_equal(true)
```

</details>

#### uses c_find_matching_field for normalized matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("c_find_matching_field")).to_equal(true)
```

</details>

### import_c — pipeline integration

#### process_c_import orchestrates resolve, parse, convert

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("fn process_c_import")).to_equal(true)
expect(src.contains("resolve_c_header")).to_equal(true)
expect(src.contains("parse_c_header_with_defines")).to_equal(true)
expect(src.contains("convert_c_structs")).to_equal(true)
```

</details>

#### builds define map from CImportDefine list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("fn build_define_map")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/import_c_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- import_c — AST types
- import_c — header resolution
- import_c — C to Simple conversion
- import_c — field matching
- import_c — pipeline integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
