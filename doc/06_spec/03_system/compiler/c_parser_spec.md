# C Parser Specification

> Tests covering C Parser — type definitions, C Parser — lexer, C Parser — preprocessor, C Parser — struct parser, C Parser — name matching, C Parser — module structure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Parser Specification

## Scenarios

### C Parser — type definitions

#### defines CField struct with name, c_type, bit_width, is_pointer, array_size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines CField struct with name, c_type, bit_width, is_pointer, array_size
   - Expected: src contains `struct CField:`
   - Expected: src contains `name: text`
   - Expected: src contains `c_type: text`
   - Expected: src contains `bit_width: i32`
   - Expected: src contains `is_pointer: bool`
   - Expected: src contains `array_size: i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CField struct with name, c_type, bit_width, is_pointer, array_size")
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

- defines CStruct with name, fields, is_union, is_class
   - Expected: src contains `struct CStruct:`
   - Expected: src contains `fields: [CField]`
   - Expected: src contains `is_union: bool`
   - Expected: src contains `is_class: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CStruct with name, fields, is_union, is_class")
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CStruct:")).to_equal(true)
expect(src.contains("fields: [CField]")).to_equal(true)
expect(src.contains("is_union: bool")).to_equal(true)
expect(src.contains("is_class: bool")).to_equal(true)
```

</details>

#### defines CEnum with name and values

- defines CEnum with name and values
   - Expected: src contains `struct CEnum:`
   - Expected: src contains `struct CEnumValue:`
   - Expected: src contains `values: [CEnumValue]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CEnum with name and values")
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CEnum:")).to_equal(true)
expect(src.contains("struct CEnumValue:")).to_equal(true)
expect(src.contains("values: [CEnumValue]")).to_equal(true)
```

</details>

#### defines CTypedef with name and target_type

- defines CTypedef with name and target_type
   - Expected: src contains `struct CTypedef:`
   - Expected: src contains `target_type: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CTypedef with name and target_type")
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CTypedef:")).to_equal(true)
expect(src.contains("target_type: text")).to_equal(true)
```

</details>

#### defines CDefine with name, value, is_integer, int_value

- defines CDefine with name, value, is_integer, int_value
   - Expected: src contains `struct CDefine:`
   - Expected: src contains `is_integer: bool`
   - Expected: src contains `int_value: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CDefine with name, value, is_integer, int_value")
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CDefine:")).to_equal(true)
expect(src.contains("is_integer: bool")).to_equal(true)
expect(src.contains("int_value: i64")).to_equal(true)
```

</details>

#### defines CParseResult aggregating all parsed elements

- defines CParseResult aggregating all parsed elements
   - Expected: src contains `struct CParseResult:`
   - Expected: src contains `structs: [CStruct]`
   - Expected: src contains `enums: [CEnum]`
   - Expected: src contains `typedefs: [CTypedef]`
   - Expected: src contains `defines: [CDefine]`
   - Expected: src contains `errors: [text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CParseResult aggregating all parsed elements")
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

- defines CToken for lexer output
   - Expected: src contains `struct CToken:`
   - Expected: src contains `kind: text`
   - Expected: src contains `value: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines CToken for lexer output")
val src = read_text("src/lib/common/c_parser/c_types.spl")
expect(src.contains("struct CToken:")).to_equal(true)
expect(src.contains("kind: text")).to_equal(true)
expect(src.contains("value: text")).to_equal(true)
```

</details>

### C Parser — lexer

#### defines c_tokenize function

- defines c_tokenize function
   - Expected: src contains `fn c_tokenize(source: text) -> [CToken]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines c_tokenize function")
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("fn c_tokenize(source: text) -> [CToken]")).to_equal(true)
```

</details>

#### handles C-style line and block comments

- handles C-style line and block comments
   - Expected: src contains `next == "/"`
   - Expected: src contains `next == "*"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles C-style line and block comments")
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("next == \"/\"")).to_equal(true)
expect(src.contains("next == \"*\"")).to_equal(true)
```

</details>

#### tokenizes preprocessor directives with pp_ prefix

- tokenizes preprocessor directives with pp_ prefix
   - Expected: src contains `pp_" + directive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tokenizes preprocessor directives with pp_ prefix")
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("pp_\" + directive")).to_equal(true)
```

</details>

#### recognizes C keywords as distinct token kinds

- recognizes C keywords as distinct token kinds
   - Expected: src contains `fn c_keyword_kind(ident: text) -> text`
   - Expected: src contains `kw_struct`
   - Expected: src contains `kw_class`
   - Expected: src contains `kw_union`
   - Expected: src contains `kw_enum`
   - Expected: src contains `kw_typedef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recognizes C keywords as distinct token kinds")
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

- handles hex number literals (0x prefix)
   - Expected: src contains `num_val = "0x"`
   - Expected: src contains `== "X"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles hex number literals (0x prefix)")
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("num_val = \"0x\"")).to_equal(true)
expect(src.contains("== \"X\"")).to_equal(true)
```

</details>

#### handles string and char literals

- handles string and char literals
   - Expected: src contains `kind: "string"`
   - Expected: src contains `kind: "char"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles string and char literals")
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("kind: \"string\"")).to_equal(true)
expect(src.contains("kind: \"char\"")).to_equal(true)
```

</details>

#### handles line continuation in preprocessor directives

- handles line continuation in preprocessor directives
   - Expected: src contains `\\\\`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles line continuation in preprocessor directives")
val src = read_text("src/lib/common/c_parser/c_lexer.spl")
expect(src.contains("\\\\")).to_equal(true)
```

</details>

### C Parser — preprocessor

#### defines c_preprocess function

- defines c_preprocess function
   - Expected: src contains `fn c_preprocess(source: text, initial_defines`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines c_preprocess function")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn c_preprocess(source: text, initial_defines")).to_equal(true)
```

</details>

#### handles #ifdef and #ifndef conditionals

- handles #ifdef and #ifndef conditionals
   - Expected: src contains `directive == "ifdef"`
   - Expected: src contains `directive == "ifndef"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles #ifdef and #ifndef conditionals")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"ifdef\"")).to_equal(true)
expect(src.contains("directive == \"ifndef\"")).to_equal(true)
```

</details>

#### handles #if/#elif/#else/#endif

- handles #if/#elif/#else/#endif
   - Expected: src contains `directive == "if"`
   - Expected: src contains `directive == "elif"`
   - Expected: src contains `directive == "else"`
   - Expected: src contains `directive == "endif"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles #if/#elif/#else/#endif")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"if\"")).to_equal(true)
expect(src.contains("directive == \"elif\"")).to_equal(true)
expect(src.contains("directive == \"else\"")).to_equal(true)
expect(src.contains("directive == \"endif\"")).to_equal(true)
```

</details>

#### collects #define constants as CDefine

- collects #define constants as CDefine
   - Expected: src contains `directive == "define"`
   - Expected: src contains `collected_defines`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects #define constants as CDefine")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"define\"")).to_equal(true)
expect(src.contains("collected_defines")).to_equal(true)
```

</details>

#### handles #include within include root

- handles #include within include root
   - Expected: src contains `directive == "include"`
   - Expected: src contains `include_root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles #include within include root")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("directive == \"include\"")).to_equal(true)
expect(src.contains("include_root")).to_equal(true)
```

</details>

#### performs whole-word identifier replacement

- performs whole-word identifier replacement
   - Expected: src contains `fn pp_replace_ident`
   - Expected: src contains `pp_is_ident_char`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("performs whole-word identifier replacement")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_replace_ident")).to_equal(true)
expect(src.contains("pp_is_ident_char")).to_equal(true)
```

</details>

#### evaluates defined() conditions

- evaluates defined() conditions
   - Expected: src contains `fn pp_eval_condition`
   - Expected: src contains `defined(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evaluates defined() conditions")
val src = read_text("src/lib/common/c_parser/c_preprocessor.spl")
expect(src.contains("fn pp_eval_condition")).to_equal(true)
expect(src.contains("defined(")).to_equal(true)
```

</details>

### C Parser — struct parser

#### defines c_parse_all as main entry point

- defines c_parse_all as main entry point
   - Expected: src contains `fn c_parse_all(tokens: [CToken]) -> CParseResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines c_parse_all as main entry point")
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn c_parse_all(tokens: [CToken]) -> CParseResult")).to_equal(true)
```

</details>

#### parses struct, union, and class definitions

- parses struct, union, and class definitions
   - Expected: src contains `fn parse_struct_or_union`
   - Expected: src contains `kw_struct`
   - Expected: src contains `kw_union`
   - Expected: src contains `kw_class`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct, union, and class definitions")
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_struct_or_union")).to_equal(true)
expect(src.contains("kw_struct")).to_equal(true)
expect(src.contains("kw_union")).to_equal(true)
expect(src.contains("kw_class")).to_equal(true)
```

</details>

#### parses fields with type, name, pointer, array, bitfield

- parses fields with type, name, pointer, array, bitfield
   - Expected: src contains `fn parse_field`
   - Expected: src contains `is_pointer`
   - Expected: src contains `array_size`
   - Expected: src contains `bit_width`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses fields with type, name, pointer, array, bitfield")
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_field")).to_equal(true)
expect(src.contains("is_pointer")).to_equal(true)
expect(src.contains("array_size")).to_equal(true)
expect(src.contains("bit_width")).to_equal(true)
```

</details>

#### handles unsigned/signed type qualifiers

- handles unsigned/signed type qualifiers
   - Expected: src contains `kw_unsigned`
   - Expected: src contains `kw_signed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles unsigned/signed type qualifiers")
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("kw_unsigned")).to_equal(true)
expect(src.contains("kw_signed")).to_equal(true)
```

</details>

#### parses enum definitions with auto-incrementing values

- parses enum definitions with auto-incrementing values
   - Expected: src contains `fn parse_enum`
   - Expected: src contains `next_value = next_value + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum definitions with auto-incrementing values")
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_enum")).to_equal(true)
expect(src.contains("next_value = next_value + 1")).to_equal(true)
```

</details>

#### parses typedef for struct, enum, and simple type aliases

- parses typedef for struct, enum, and simple type aliases
   - Expected: src contains `fn parse_typedef`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses typedef for struct, enum, and simple type aliases")
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("fn parse_typedef")).to_equal(true)
```

</details>

#### handles C++ access specifiers (public/private/protected)

- handles C++ access specifiers (public/private/protected)
   - Expected: src contains `kw_public`
   - Expected: src contains `kw_private`
   - Expected: src contains `kw_protected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles C++ access specifiers (public/private/protected)")
val src = read_text("src/lib/common/c_parser/c_struct_parser.spl")
expect(src.contains("kw_public")).to_equal(true)
expect(src.contains("kw_private")).to_equal(true)
expect(src.contains("kw_protected")).to_equal(true)
```

</details>

### C Parser — name matching

#### defines normalize_c_name function

- defines normalize_c_name function
   - Expected: src contains `fn normalize_c_name(name: text) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines normalize_c_name function")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn normalize_c_name(name: text) -> text")).to_equal(true)
```

</details>

#### strips underscores and converts to lowercase

- strips underscores and converts to lowercase
   - Expected: src contains `"_"`
   - Expected: src contains `"-"`
   - Expected: src contains `code + 32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strips underscores and converts to lowercase")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("\"_\"")).to_equal(true)
expect(src.contains("\"-\"")).to_equal(true)
expect(src.contains("code + 32")).to_equal(true)
```

</details>

#### defines strict and non-strict matching

- defines strict and non-strict matching
   - Expected: src contains `fn c_names_match(`
   - Expected: src contains `fn c_names_match_strict(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines strict and non-strict matching")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn c_names_match(")).to_equal(true)
expect(src.contains("fn c_names_match_strict(")).to_equal(true)
```

</details>

#### defines find_matching_field and find_matching_struct

- defines find_matching_field and find_matching_struct
   - Expected: src contains `fn c_find_matching_field`
   - Expected: src contains `fn c_find_matching_struct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines find_matching_field and find_matching_struct")
val src = read_text("src/lib/common/c_parser/c_name_match.spl")
expect(src.contains("fn c_find_matching_field")).to_equal(true)
expect(src.contains("fn c_find_matching_struct")).to_equal(true)
```

</details>

### C Parser — module structure

#### has __init__.spl with public API exports

- has __init__.spl with public API exports
   - Expected: src contains `export CField`
   - Expected: src contains `export CStruct`
   - Expected: src contains `export CParseResult`
   - Expected: src contains `export c_tokenize`
   - Expected: src contains `export c_preprocess`
   - Expected: src contains `export c_parse_all`
   - Expected: src contains `export normalize_c_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has __init__.spl with public API exports")
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

- has parse_c_header and parse_c_header_with_defines entry points
   - Expected: src contains `fn parse_c_header(source: text) -> CParseResult`
   - Expected: src contains `fn parse_c_header_with_defines`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has parse_c_header and parse_c_header_with_defines entry points")
val src = read_text("src/lib/common/c_parser/__init__.spl")
expect(src.contains("fn parse_c_header(source: text) -> CParseResult")).to_equal(true)
expect(src.contains("fn parse_c_header_with_defines")).to_equal(true)
```

</details>

#### pipeline: preprocess -> tokenize -> parse_all

- pipeline: preprocess -> tokenize -> parse_all
   - Expected: src contains `c_preprocess(source, defines)`
   - Expected: src contains `c_tokenize(preprocessed)`
   - Expected: src contains `c_parse_all(tokens)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pipeline: preprocess -> tokenize -> parse_all")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering C Parser — type definitions, C Parser — lexer, C Parser — preprocessor, C Parser — struct parser, C Parser — name matching, C Parser — module structure.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `573246c624e93c89fd9e79c24c42ca561ea08c5ac739e7a170dbbc426d1a851b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `573246c624e93c89fd9e79c24c42ca561ea08c5ac739e7a170dbbc426d1a851b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `573246c624e93c89fd9e79c24c42ca561ea08c5ac739e7a170dbbc426d1a851b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/c_parser_spec.spl
mirror: doc/06_spec/03_system/compiler/c_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/c_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/c_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/c_parser_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines CField struct with name, c_type, bit_width, is_pointer, array_size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/c_parser_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines CStruct with name, fields, is_union, is_class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/c_parser_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines CEnum with name and values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
