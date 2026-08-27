# Import C Specification

> Tests covering import_c — AST types, import_c — header resolution, import_c — C to Simple conversion, import_c — field matching, import_c — pipeline integration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import C Specification

## Scenarios

### import_c — AST types

#### defines CImport struct with header_path and struct_matches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines CImport struct with header_path and struct_matches
   - Expected: src contains `struct CImport:`
   - Expected: src contains `header_path: text`
   - Expected: src contains `struct_matches: [CImportMatch]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CImport struct with header_path and struct_matches")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImport:")).to_equal(true)
expect(src.contains("header_path: text")).to_equal(true)
expect(src.contains("struct_matches: [CImportMatch]")).to_equal(true)
```

</details>

#### defines CImportMatch with simple_name, c_name, strict

- defines CImportMatch with simple_name, c_name, strict
   - Expected: src contains `struct CImportMatch:`
   - Expected: src contains `simple_name: text`
   - Expected: src contains `c_name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CImportMatch with simple_name, c_name, strict")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportMatch:")).to_equal(true)
expect(src.contains("simple_name: text")).to_equal(true)
expect(src.contains("c_name: text")).to_equal(true)
```

</details>

#### defines CImportDefine for user define forwarding

- defines CImportDefine for user define forwarding
   - Expected: src contains `struct CImportDefine:`
   - Expected: src contains `define_forwards: [CImportDefine]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CImportDefine for user define forwarding")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportDefine:")).to_equal(true)
expect(src.contains("define_forwards: [CImportDefine]")).to_equal(true)
```

</details>

#### defines CImportResult with structs and errors

- defines CImportResult with structs and errors
   - Expected: src contains `struct CImportResult:`
   - Expected: src contains `structs: [CImportedStruct]`
   - Expected: src contains `errors: [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CImportResult with structs and errors")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportResult:")).to_equal(true)
expect(src.contains("structs: [CImportedStruct]")).to_equal(true)
expect(src.contains("errors: [text]")).to_equal(true)
```

</details>

#### defines CImportedStruct with layout_kind

- defines CImportedStruct with layout_kind
   - Expected: src contains `struct CImportedStruct:`
   - Expected: src contains `layout_kind: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CImportedStruct with layout_kind")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportedStruct:")).to_equal(true)
expect(src.contains("layout_kind: text")).to_equal(true)
```

</details>

#### defines CImportedField with aka_name

- defines CImportedField with aka_name
   - Expected: src contains `struct CImportedField:`
   - Expected: src contains `aka_name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CImportedField with aka_name")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportedField:")).to_equal(true)
expect(src.contains("aka_name: text")).to_equal(true)
```

</details>

### import_c — header resolution

#### defines resolve_c_header function

- defines resolve_c_header function
   - Expected: src contains `fn resolve_c_header(header_path: text, include_paths: [text]) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines resolve_c_header function")
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("fn resolve_c_header(header_path: text, include_paths: [text]) -> text")).to_equal(true)
```

</details>

#### checks src/include as default path

- checks src/include as default path
   - Expected: src contains `src/include/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks src/include as default path")
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("src/include/")).to_equal(true)
```

</details>

#### validates self-contained headers reject system includes

- validates self-contained headers reject system includes
   - Expected: src contains `fn validate_self_contained`
   - Expected: src contains `system include not allowed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates self-contained headers reject system includes")
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("fn validate_self_contained")).to_equal(true)
expect(src.contains("system include not allowed")).to_equal(true)
```

</details>

#### defines default_include_paths

- defines default_include_paths
   - Expected: src contains `fn default_include_paths`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines default_include_paths")
val src = read_text("src/compiler/10.frontend/c_import/c_import_resolve.spl")
expect(src.contains("fn default_include_paths")).to_equal(true)
```

</details>

### import_c — C to Simple conversion

#### defines convert_c_structs entry point

- defines convert_c_structs entry point
   - Expected: src contains `fn convert_c_structs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines convert_c_structs entry point")
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("fn convert_c_structs")).to_equal(true)
```

</details>

#### defines c_type_to_simple type mapping

- defines c_type_to_simple type mapping
   - Expected: src contains `fn c_type_to_simple(c_type: text, is_pointer: bool) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines c_type_to_simple type mapping")
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("fn c_type_to_simple(c_type: text, is_pointer: bool) -> text")).to_equal(true)
```

</details>

#### maps standard C integer types to Simple

- maps standard C integer types to Simple
   - Expected: src contains `uint8_t`
   - Expected: src contains `uint32_t`
   - Expected: src contains `int64_t`
   - Expected: src contains `size_t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps standard C integer types to Simple")
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("uint8_t")).to_equal(true)
expect(src.contains("uint32_t")).to_equal(true)
expect(src.contains("int64_t")).to_equal(true)
expect(src.contains("size_t")).to_equal(true)
```

</details>

#### maps pointer types to ptr

- maps pointer types to ptr
   - Expected: src contains `return "ptr"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps pointer types to ptr")
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("return \"ptr\"")).to_equal(true)
```

</details>

#### uses c_find_matching_struct for name resolution

- uses c_find_matching_struct for name resolution
   - Expected: src contains `c_find_matching_struct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses c_find_matching_struct for name resolution")
val src = read_text("src/compiler/10.frontend/c_import/c_to_simple.spl")
expect(src.contains("c_find_matching_struct")).to_equal(true)
```

</details>

### import_c — field matching

#### defines match_fields function

- defines match_fields function
   - Expected: src contains `fn match_fields`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines match_fields function")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn match_fields")).to_equal(true)
```

</details>

#### resolves aka aliases with exact match

- resolves aka aliases with exact match
   - Expected: src contains `fn find_aka_field`
   - Expected: src contains `sf.aka_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves aka aliases with exact match")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn find_aka_field")).to_equal(true)
expect(src.contains("sf.aka_name")).to_equal(true)
```

</details>

#### defines FieldMatch and FieldMatchResult

- defines FieldMatch and FieldMatchResult
   - Expected: src contains `struct FieldMatch:`
   - Expected: src contains `struct FieldMatchResult:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines FieldMatch and FieldMatchResult")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("struct FieldMatch:")).to_equal(true)
expect(src.contains("struct FieldMatchResult:")).to_equal(true)
```

</details>

#### reports unmatched Simple fields as errors

- reports unmatched Simple fields as errors
   - Expected: src contains `unmatched_simple`
   - Expected: src contains `field has no match in C struct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports unmatched Simple fields as errors")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("unmatched_simple")).to_equal(true)
expect(src.contains("field has no match in C struct")).to_equal(true)
```

</details>

#### tracks unmatched C fields for warnings

- tracks unmatched C fields for warnings
   - Expected: src contains `unmatched_c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks unmatched C fields for warnings")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("unmatched_c")).to_equal(true)
```

</details>

#### uses c_find_matching_field for normalized matching

- uses c_find_matching_field for normalized matching
   - Expected: src contains `c_find_matching_field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses c_find_matching_field for normalized matching")
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("c_find_matching_field")).to_equal(true)
```

</details>

### import_c — pipeline integration

#### process_c_import orchestrates resolve, parse, convert

- process_c_import orchestrates resolve, parse, convert
   - Expected: src contains `fn process_c_import`
   - Expected: src contains `resolve_c_header`
   - Expected: src contains `parse_c_header_with_defines`
   - Expected: src contains `convert_c_structs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("process_c_import orchestrates resolve, parse, convert")
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("fn process_c_import")).to_equal(true)
expect(src.contains("resolve_c_header")).to_equal(true)
expect(src.contains("parse_c_header_with_defines")).to_equal(true)
expect(src.contains("convert_c_structs")).to_equal(true)
```

</details>

#### builds define map from CImportDefine list

- builds define map from CImportDefine list
   - Expected: src contains `fn build_define_map`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds define map from CImportDefine list")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering import_c — AST types, import_c — header resolution, import_c — C to Simple conversion, import_c — field matching, import_c — pipeline integration.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7e8db8478814c6e7ca95d86023a05ead453aee1191d2c03f5e7818c4d88044f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7e8db8478814c6e7ca95d86023a05ead453aee1191d2c03f5e7818c4d88044f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7e8db8478814c6e7ca95d86023a05ead453aee1191d2c03f5e7818c4d88044f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/import_c_spec.spl
mirror: doc/06_spec/03_system/compiler/import_c_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/import_c_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/import_c_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/import_c_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines CImport struct with header_path and struct_matches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/import_c_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines CImportMatch with simple_name, c_name, strict' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/import_c_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines CImportDefine for user define forwarding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
