# C Parser Specification

> <details>

<!-- sdn-diagram:id=c_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=c_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

c_parser_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=c_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Parser Specification

## Scenarios

### C Parser — type definitions

#### defines CField struct with name, c_type, bit_width, is_pointer, array_size

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CField:")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
expect(src.contains("c_type: text")).to_equal(true)
expect(src.contains("bit_width: i32")).to_equal(true)
expect(src.contains("is_pointer: bool")).to_equal(true)
expect(src.contains("array_size: i32")).to_equal(true)
```

</details>

#### defines CStruct with name, fields, is_union, is_class

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CStruct:")).to_equal(true)
expect(src.contains("fields: [CField]")).to_equal(true)
expect(src.contains("is_union: bool")).to_equal(true)
expect(src.contains("is_class: bool")).to_equal(true)
```

</details>

#### defines CEnum with name and values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CEnum:")).to_equal(true)
expect(src.contains("struct CEnumValue:")).to_equal(true)
expect(src.contains("values: [CEnumValue]")).to_equal(true)
```

</details>

#### defines CTypedef with name and target_type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CTypedef:")).to_equal(true)
expect(src.contains("target_type: text")).to_equal(true)
```

</details>

#### defines CDefine with name, value, is_integer, int_value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CDefine:")).to_equal(true)
expect(src.contains("is_integer: bool")).to_equal(true)
expect(src.contains("int_value: i64")).to_equal(true)
```

</details>

#### defines CParseResult aggregating all parsed elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CParseResult:")).to_equal(true)
expect(src.contains("structs: [CStruct]")).to_equal(true)
expect(src.contains("enums: [CEnum]")).to_equal(true)
expect(src.contains("typedefs: [CTypedef]")).to_equal(true)
expect(src.contains("defines: [CDefine]")).to_equal(true)
expect(src.contains("errors: [text]")).to_equal(true)
```

</details>

#### defines CToken for lexer output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CToken:")).to_equal(true)
expect(src.contains("kind: text")).to_equal(true)
expect(src.contains("value: text")).to_equal(true)
```

</details>

### C Parser — lexer

#### defines c_tokenize function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("fn c_tokenize(source: text) -> [CToken]")).to_equal(true)
```

</details>

#### handles C-style line and block comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("next == \"/\"")).to_equal(true)
expect(src.contains("next == \"*\"")).to_equal(true)
```

</details>

#### tokenizes preprocessor directives with pp_ prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("pp_\" + directive")).to_equal(true)
```

</details>

#### recognizes C keywords as distinct token kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("fn c_keyword_kind(ident: text) -> text")).to_equal(true)
expect(src.contains("kw_struct")).to_equal(true)
expect(src.contains("kw_class")).to_equal(true)
expect(src.contains("kw_union")).to_equal(true)
expect(src.contains("kw_enum")).to_equal(true)
expect(src.contains("kw_typedef")).to_equal(true)
```

</details>

#### handles hex number literals (0x prefix)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("num_val = \"0x\"")).to_equal(true)
expect(src.contains("== \"X\"")).to_equal(true)
```

</details>

#### handles string and char literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("kind: \"string\"")).to_equal(true)
expect(src.contains("kind: \"char\"")).to_equal(true)
```

</details>

#### handles line continuation in preprocessor directives

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("\\\\")).to_equal(true)
```

</details>

### C Parser — preprocessor

#### defines c_preprocess function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn c_preprocess(source: text, initial_defines")).to_equal(true)
```

</details>

#### handles #ifdef and #ifndef conditionals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"ifdef\"")).to_equal(true)
expect(src.contains("directive == \"ifndef\"")).to_equal(true)
```

</details>

#### handles #if/#elif/#else/#endif

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"if\"")).to_equal(true)
expect(src.contains("directive == \"elif\"")).to_equal(true)
expect(src.contains("directive == \"else\"")).to_equal(true)
expect(src.contains("directive == \"endif\"")).to_equal(true)
```

</details>

#### collects #define constants as CDefine

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"define\"")).to_equal(true)
expect(src.contains("collected_defines")).to_equal(true)
```

</details>

#### handles #include within include root

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"include\"")).to_equal(true)
expect(src.contains("include_root")).to_equal(true)
```

</details>

#### performs whole-word identifier replacement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_replace_ident")).to_equal(true)
expect(src.contains("pp_is_ident_char")).to_equal(true)
```

</details>

#### evaluates defined() conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_eval_condition")).to_equal(true)
expect(src.contains("defined(")).to_equal(true)
```

</details>

### C Parser — struct parser

#### defines c_parse_all as main entry point

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn c_parse_all(tokens: [CToken]) -> CParseResult")).to_equal(true)
```

</details>

#### parses struct, union, and class definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_struct_or_union")).to_equal(true)
expect(src.contains("kw_struct")).to_equal(true)
expect(src.contains("kw_union")).to_equal(true)
expect(src.contains("kw_class")).to_equal(true)
```

</details>

#### parses fields with type, name, pointer, array, bitfield

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_field")).to_equal(true)
expect(src.contains("is_pointer")).to_equal(true)
expect(src.contains("array_size")).to_equal(true)
expect(src.contains("bit_width")).to_equal(true)
```

</details>

#### handles unsigned/signed type qualifiers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("kw_unsigned")).to_equal(true)
expect(src.contains("kw_signed")).to_equal(true)
```

</details>

#### parses enum definitions with auto-incrementing values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_enum")).to_equal(true)
expect(src.contains("next_value = next_value + 1")).to_equal(true)
```

</details>

#### parses typedef for struct, enum, and simple type aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_typedef")).to_equal(true)
```

</details>

#### handles C++ access specifiers (public/private/protected)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("kw_public")).to_equal(true)
expect(src.contains("kw_private")).to_equal(true)
expect(src.contains("kw_protected")).to_equal(true)
```

</details>

### C Parser — name matching

#### defines normalize_c_name function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn normalize_c_name(name: text) -> text")).to_equal(true)
```

</details>

#### strips underscores and converts to lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("\"_\"")).to_equal(true)
expect(src.contains("\"-\"")).to_equal(true)
expect(src.contains("code + 32")).to_equal(true)
```

</details>

#### defines strict and non-strict matching

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn c_names_match(")).to_equal(true)
expect(src.contains("fn c_names_match_strict(")).to_equal(true)
```

</details>

#### defines find_matching_field and find_matching_struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn c_find_matching_field")).to_equal(true)
expect(src.contains("fn c_find_matching_struct")).to_equal(true)
```

</details>

### C Parser — module structure

#### has __init__.spl with public API exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/__init__.spl")
expect(src.contains("export CField")).to_equal(true)
expect(src.contains("export CStruct")).to_equal(true)
expect(src.contains("export CParseResult")).to_equal(true)
expect(src.contains("export c_tokenize")).to_equal(true)
expect(src.contains("export c_preprocess")).to_equal(true)
expect(src.contains("export c_parse_all")).to_equal(true)
expect(src.contains("export normalize_c_name")).to_equal(true)
```

</details>

#### has parse_c_header and parse_c_header_with_defines entry points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/__init__.spl")
expect(src.contains("fn parse_c_header(source: text) -> CParseResult")).to_equal(true)
expect(src.contains("fn parse_c_header_with_defines")).to_equal(true)
```

</details>

#### pipeline: preprocess -> tokenize -> parse_all

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/common/c_parser/__init__.spl")
expect(src.contains("c_preprocess(source, defines)")).to_equal(true)
expect(src.contains("c_tokenize(preprocessed)")).to_equal(true)
expect(src.contains("c_parse_all(tokens)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/c_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- C Parser — type definitions
- C Parser — lexer
- C Parser — preprocessor
- C Parser — struct parser
- C Parser — name matching
- C Parser — module structure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
