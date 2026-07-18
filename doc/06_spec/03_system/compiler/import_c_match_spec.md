# Import C Match Specification

> <details>

<!-- sdn-diagram:id=import_c_match_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=import_c_match_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

import_c_match_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=import_c_match_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import C Match Specification

## Scenarios

### import_c match — name normalization

#### normalize_c_name strips underscores and lowercases

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn normalize_c_name(name: text) -> text")).to_equal(true)
expect(src.contains("ch != \"_\"")).to_equal(true)
expect(src.contains("ch != \"-\"")).to_equal(true)
```

</details>

#### lowercases via char_code_at + 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("ch >= \"A\" and ch <= \"Z\"")).to_equal(true)
expect(src.contains("code + 32")).to_equal(true)
```

</details>

### import_c match — strict vs non-strict

#### c_names_match uses normalize_c_name for both sides

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("normalize_c_name(simple_name) == normalize_c_name(c_name)")).to_equal(true)
```

</details>

#### c_names_match_strict uses exact equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("simple_name == c_name")).to_equal(true)
```

</details>

#### CImportMatch has strict flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("strict: bool")).to_equal(true)
```

</details>

#### CImport has strict_match default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("strict_match: bool")).to_equal(true)
expect(src.contains("strict_match: false")).to_equal(true)
```

</details>

### import_c match — aka field aliases

#### CImportedField has aka_name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("aka_name: text")).to_equal(true)
```

</details>

#### find_aka_field performs exact match on C field names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn find_aka_field(aka_name: text, c_field_names: [text]) -> text")).to_equal(true)
```

</details>

#### aka takes priority over auto-matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("sf.aka_name != \"\"")).to_equal(true)
```

</details>

#### aka referencing nonexistent field produces error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("aka field not found in C struct")).to_equal(true)
```

</details>

### import_c match — field coverage validation

#### extra Simple field (not in C) produces error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("field has no match in C struct")).to_equal(true)
```

</details>

#### extra C field (not in Simple) tracked as unmatched_c

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("unmatched_c: [text]")).to_equal(true)
```

</details>

#### validate_field_match collects all errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("fn validate_field_match")).to_equal(true)
```

</details>

#### FieldMatch records simple_name, c_name, and aka_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/c_field_match.spl")
expect(src.contains("struct FieldMatch:")).to_equal(true)
expect(src.contains("simple_name: text")).to_equal(true)
expect(src.contains("c_name: text")).to_equal(true)
expect(src.contains("aka_name: text")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/import_c_match_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- import_c match — name normalization
- import_c match — strict vs non-strict
- import_c match — aka field aliases
- import_c match — field coverage validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
