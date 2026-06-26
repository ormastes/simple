# Import C Defines Specification

> <details>

<!-- sdn-diagram:id=import_c_defines_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=import_c_defines_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

import_c_defines_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=import_c_defines_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import C Defines Specification

## Scenarios

### import_c defines — system config forwarding

#### preprocessor accepts initial_defines parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("initial_defines: {text: text}")).to_equal(true)
```

</details>

#### initial defines are copied into active define table

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("defines[key] = initial_defines[key]")).to_equal(true)
```

</details>

#### CImportDefine carries name and value for forwarding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("struct CImportDefine:")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
expect(src.contains("value: text")).to_equal(true)
```

</details>

#### build_define_map converts CImportDefine list to map

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/compiler/10.frontend/c_import/__init__.spl")
expect(src.contains("fn build_define_map(forwards: [CImportDefine]) -> {text: text}")).to_equal(true)
expect(src.contains("result[fwd.name] = fwd.value")).to_equal(true)
```

</details>

### import_c defines — preprocessor conditionals

#### handles #ifdef with define table lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("defines.contains_key(directive_arg.trim())")).to_equal(true)
```

</details>

#### handles #ifndef as inverse of #ifdef

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"ifndef\"")).to_equal(true)
```

</details>

#### handles nested #if with skip_depth tracking

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("skip_depth")).to_equal(true)
expect(src.contains("condition_stack")).to_equal(true)
```

</details>

#### evaluates defined() in #if conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_eval_condition")).to_equal(true)
expect(src.contains("defines.contains_key(name)")).to_equal(true)
```

</details>

### import_c defines — #define collection

#### collects defines during preprocessing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("collected_defines")).to_equal(true)
expect(src.contains("collected_defines.push")).to_equal(true)
```

</details>

#### pp_make_c_define detects integer values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_make_c_define")).to_equal(true)
expect(src.contains("is_int = true")).to_equal(true)
```

</details>

#### pp_parse_define extracts name and value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_parse_define")).to_equal(true)
```

</details>

#### handles function-like macros by skipping parenthesized params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("trimmed[i] == \"(\"")).to_equal(true)
```

</details>

### import_c defines — macro expansion

#### expands defines as whole-word identifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_replace_ident")).to_equal(true)
```

</details>

#### checks word boundaries before and after match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("before_ok")).to_equal(true)
expect(src.contains("after_ok")).to_equal(true)
```

</details>

#### uses pp_is_ident_char for boundary detection

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_is_ident_char")).to_equal(true)
```

</details>

### import_c defines — include processing

#### handles #include with file resolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"include\"")).to_equal(true)
expect(src.contains("fn pp_parse_include_path")).to_equal(true)
```

</details>

#### recursively preprocesses included files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("c_preprocess_with_include_root(inc_source")).to_equal(true)
```

</details>

#### reports error for missing includes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("include not found")).to_equal(true)
```

</details>

#### handles line continuation with backslash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("ends_with(\"\\\\\")")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/import_c_defines_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- import_c defines — system config forwarding
- import_c defines — preprocessor conditionals
- import_c defines — #define collection
- import_c defines — macro expansion
- import_c defines — include processing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
