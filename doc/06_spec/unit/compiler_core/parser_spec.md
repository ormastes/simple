# parser_spec

> Purpose: Prove that core.parser.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# parser_spec

Purpose: Prove that core.parser.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that core.parser.
Audience: COMP-CORE maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### core.parser

#### parses a mixed module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a mixed module
- Verify: parses a mixed module
   - Expected: parser_has_errors() is false
   - Expected: module_get_path() equals `test.spl`
   - Expected: decls.len() equals `6`
   - Expected: decl_get_tag(decls[0]) equals `DECL_USE`
   - Expected: decl_get_tag(decls[1]) equals `DECL_EXPORT`
   - Expected: decl_get_tag(decls[2]) equals `DECL_VAL`
   - Expected: decl_get_tag(decls[3]) equals `DECL_VAR`
   - Expected: decl_get_tag(decls[4]) equals `DECL_FN`
   - Expected: decl_get_tag(decls[5]) equals `DECL_STRUCT`
   - Expected: decl_get_imports(decls[0]).len() equals `2`
   - Expected: decl_get_name(decls[4]) equals `add`
   - Expected: decl_get_param_names(decls[4]).len() equals `2`
   - Expected: decl_get_ret_type(decls[4]) equals `TYPE_I64`
   - Expected: decl_get_name(decls[5]) equals `Point`
   - Expected: decl_get_fields(decls[5]).len() equals `2`
   - Expected: decl_get_field_types(decls[5])[0] equals `TYPE_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a mixed module")
step("Verify: parses a mixed module")
# @req: REQ-COMP-CORE-CORE-PARSER-001
val src = "use foo.{bar, baz}\n" +
    "export bar, baz\n" +
    "val x: i64 = 1\n" +
    "var y = 2\n" +
    "fn add(a: i64, b: i64) -> i64:\n" +
    "    return a + b\n" +
    "struct Point:\n" +
    "    x: i64\n" +
    "    y: i64\n" +
    "enum Color:\n" +
    "    Red\n" +
    "    Green\n"

parse(src, "test.spl")
expect(parser_has_errors()).to_equal(false)
expect(module_get_path()).to_equal("test.spl")

val decls = module_get_decls()
expect(decls.len()).to_equal(6)
expect(decl_get_tag(decls[0])).to_equal(DECL_USE)
expect(decl_get_tag(decls[1])).to_equal(DECL_EXPORT)
expect(decl_get_tag(decls[2])).to_equal(DECL_VAL)
expect(decl_get_tag(decls[3])).to_equal(DECL_VAR)
expect(decl_get_tag(decls[4])).to_equal(DECL_FN)
expect(decl_get_tag(decls[5])).to_equal(DECL_STRUCT)

# Use/import details
expect(decl_get_imports(decls[0]).len()).to_equal(2)

# Function details
expect(decl_get_name(decls[4])).to_equal("add")
expect(decl_get_param_names(decls[4]).len()).to_equal(2)
expect(decl_get_ret_type(decls[4])).to_equal(TYPE_I64)

# Struct details
expect(decl_get_name(decls[5])).to_equal("Point")
expect(decl_get_fields(decls[5]).len()).to_equal(2)
expect(decl_get_field_types(decls[5])[0]).to_equal(TYPE_I64)
```

</details>

#### parses enum declaration

- parses enum declaration
- Verify: parses enum declaration
   - Expected: parser_has_errors() is false
   - Expected: decls.len() equals `1`
   - Expected: decl_get_tag(decls[0]) equals `DECL_ENUM`
   - Expected: decl_get_name(decls[0]) equals `E`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses enum declaration")
step("Verify: parses enum declaration")
val src = "enum E:\n  A\n  B\n"
parse(src, "enum.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decls.len()).to_equal(1)
expect(decl_get_tag(decls[0])).to_equal(DECL_ENUM)
expect(decl_get_name(decls[0])).to_equal("E")
```

</details>

#### parses module-level expression as pseudo-decl

- parses module-level expression as pseudo-decl
- Verify: parses module-level expression as pseudo-decl
   - Expected: parser_has_errors() is false
   - Expected: decls.len() equals `1`
   - Expected: decl_get_tag(decls[0]) equals `DECL_VAL`
   - Expected: body.len() equals `1`
   - Expected: stmt_get_tag(s) equals `STMT_EXPR`
   - Expected: expr_get_tag(e) equals `EXPR_BINARY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses module-level expression as pseudo-decl")
step("Verify: parses module-level expression as pseudo-decl")
val src = "1 + 2\n"
parse(src, "expr.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decls.len()).to_equal(1)
# The module-level expression is wrapped in a decl_val_binding
expect(decl_get_tag(decls[0])).to_equal(DECL_VAL)
val body = decl_get_body(decls[0])
expect(body.len()).to_equal(1)
val s = body[0]
expect(stmt_get_tag(s)).to_equal(STMT_EXPR)
val e = stmt_get_expr(s)
expect(expr_get_tag(e)).to_equal(EXPR_BINARY)
```

</details>

#### records parse errors

- records parse errors
- Verify: records parse errors
   - Expected: parser_has_errors() is true
   - Expected: parser_error_count() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records parse errors")
step("Verify: records parse errors")
val src = "fn\n"
parse(src, "bad.spl")
expect(parser_has_errors()).to_equal(true)
expect(parser_error_count() > 0).to_equal(true)
```

</details>

#### parses Option<i64> type annotation

- parses Option<i64> type annotation
- Verify: parses Option<i64> type annotation
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Option<i64> type annotation")
step("Verify: parses Option<i64> type annotation")
val src = "fn get_value() -> Option<i64>:\n    return nil\n"
parse(src, "option_i64.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_I64)
```

</details>

#### parses Option<f64> type annotation

- parses Option<f64> type annotation
- Verify: parses Option<f64> type annotation
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Option<f64> type annotation")
step("Verify: parses Option<f64> type annotation")
val src = "fn get_float() -> Option<f64>:\n    return nil\n"
parse(src, "option_f64.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_F64)
```

</details>

#### parses Option<text> type annotation

- parses Option<text> type annotation
- Verify: parses Option<text> type annotation
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Option<text> type annotation")
step("Verify: parses Option<text> type annotation")
val src = "fn get_name() -> Option<text>:\n    return nil\n"
parse(src, "option_text.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_TEXT)
```

</details>

#### parses Option<bool> type annotation

- parses Option<bool> type annotation
- Verify: parses Option<bool> type annotation
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Option<bool> type annotation")
step("Verify: parses Option<bool> type annotation")
val src = "fn get_flag() -> Option<bool>:\n    return nil\n"
parse(src, "option_bool.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_BOOL)
```

</details>

#### parses Option with unknown inner type

- parses Option with unknown inner type
- Verify: parses Option with unknown inner type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Option with unknown inner type")
step("Verify: parses Option with unknown inner type")
# Option<SomeStruct> falls back to TYPE_OPTION
val src = "fn get_custom() -> Option<SomeStruct>:\n    return nil\n"
parse(src, "option_custom.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION)
```

</details>

#### parses i64? postfix type

- parses i64? postfix type
- Verify: parses i64? postfix type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses i64? postfix type")
step("Verify: parses i64? postfix type")
val src = "fn find_int() -> i64?:\n    return nil\n"
parse(src, "postfix_i64.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_I64)
```

</details>

#### parses f64? postfix type

- parses f64? postfix type
- Verify: parses f64? postfix type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses f64? postfix type")
step("Verify: parses f64? postfix type")
val src = "fn find_float() -> f64?:\n    return nil\n"
parse(src, "postfix_f64.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_F64)
```

</details>

#### parses text? postfix type

- parses text? postfix type
- Verify: parses text? postfix type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses text? postfix type")
step("Verify: parses text? postfix type")
val src = "fn find_name() -> text?:\n    return nil\n"
parse(src, "postfix_text.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_TEXT)
```

</details>

#### parses bool? postfix type

- parses bool? postfix type
- Verify: parses bool? postfix type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bool? postfix type")
step("Verify: parses bool? postfix type")
val src = "fn find_flag() -> bool?:\n    return nil\n"
parse(src, "postfix_bool.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION_BOOL)
```

</details>

#### parses custom? postfix type

- parses custom? postfix type
- Verify: parses custom? postfix type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses custom? postfix type")
step("Verify: parses custom? postfix type")
# CustomType? falls back to TYPE_OPTION
val src = "fn find_custom() -> CustomType?:\n    return nil\n"
parse(src, "postfix_custom.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION)
```

</details>

#### parses Result<i64> type

- parses Result<i64> type
- Verify: parses Result<i64> type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_RESULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Result<i64> type")
step("Verify: parses Result<i64> type")
val src = "fn load() -> Result<i64>:\n    return nil\n"
parse(src, "result.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_RESULT)
```

</details>

#### parses unknown generic type as any

- parses unknown generic type as any
- Verify: parses unknown generic type as any
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_ANY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses unknown generic type as any")
step("Verify: parses unknown generic type as any")
val src = "fn get_list() -> List<i64>:\n    return nil\n"
parse(src, "unknown_generic.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
# An unrecognised generic head is TYPE_ANY (12), not TYPE_VOID (0).
# The old assertion never held: measured, this returns 12.
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_ANY)
```

</details>

#### parses simple i64 type

- parses simple i64 type
- Verify: parses simple i64 type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple i64 type")
step("Verify: parses simple i64 type")
val src = "fn get_int() -> i64:\n    return 42\n"
parse(src, "simple_i64.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_I64)
```

</details>

#### parses simple f64 type

- parses simple f64 type
- Verify: parses simple f64 type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple f64 type")
step("Verify: parses simple f64 type")
val src = "fn get_float() -> f64:\n    return 3.14\n"
parse(src, "simple_f64.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_F64)
```

</details>

#### parses simple text type

- parses simple text type
- Verify: parses simple text type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_TEXT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple text type")
step("Verify: parses simple text type")
val src = "fn get_text() -> text:\n    return \"hello\"\n"
parse(src, "simple_text.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_TEXT)
```

</details>

#### parses simple bool type

- parses simple bool type
- Verify: parses simple bool type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_BOOL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple bool type")
step("Verify: parses simple bool type")
val src = "fn get_bool() -> bool:\n    return true\n"
parse(src, "simple_bool.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_BOOL)
```

</details>

#### parses bare Option type

- parses bare Option type
- Verify: parses bare Option type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_OPTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bare Option type")
step("Verify: parses bare Option type")
val src = "fn get_opt() -> Option:\n    return nil\n"
parse(src, "bare_option.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_OPTION)
```

</details>

#### parses bare Result type

- parses bare Result type
- Verify: parses bare Result type
   - Expected: parser_has_errors() is false
   - Expected: decl_get_ret_type(decls[0]) equals `TYPE_RESULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses bare Result type")
step("Verify: parses bare Result type")
val src = "fn get_res() -> Result:\n    return nil\n"
parse(src, "bare_result.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decl_get_ret_type(decls[0])).to_equal(TYPE_RESULT)
```

</details>

#### parses unknown type as a registered named type

- parses unknown type as a registered named type
- Verify: parses unknown type as a registered named type
   - Expected: parser_has_errors() is false
   - Expected: ret >= TYPE_NAMED_BASE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses unknown type as a registered named type")
step("Verify: parses unknown type as a registered named type")
val src = "fn get_custom() -> CustomStruct:\n    return nil\n"
parse(src, "unknown_type.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
# An unrecognised identifier type is no longer collapsed to TYPE_VOID:
# it is interned and returned as TYPE_NAMED_BASE + <id> (measured 10004
# for this input). e7f77939339, "fix(compiler): preserve and decode
# Result payload types" (2026-07-15), introduced TYPE_NAMED_BASE = 10000
# and made this assertion stale. The exact id depends on interning
# order, so assert the band, not the number.
val ret = decl_get_ret_type(decls[0])
expect(ret >= TYPE_NAMED_BASE).to_equal(true)
```

</details>

#### parses val with Option type

- parses val with Option type
- Verify: parses val with Option type
   - Expected: parser_has_errors() is false
   - Expected: decls.len() equals `1`
   - Expected: decl_get_tag(decls[0]) equals `DECL_VAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses val with Option type")
step("Verify: parses val with Option type")
val src = "val x: Option<i64> = nil\n"
parse(src, "val_option.spl")
expect(parser_has_errors()).to_equal(false)
val decls = module_get_decls()
expect(decls.len()).to_equal(1)
expect(decl_get_tag(decls[0])).to_equal(DECL_VAL)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-CORE-CORE-PARSER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7074c698f3f9b4900c199b21af7c2f11b508cd1c24825345eb507fa83f09ec62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7074c698f3f9b4900c199b21af7c2f11b508cd1c24825345eb507fa83f09ec62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7074c698f3f9b4900c199b21af7c2f11b508cd1c24825345eb507fa83f09ec62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler_core/parser_spec.spl
mirror: doc/06_spec/unit/compiler_core/parser_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler_core/parser_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a mixed module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/parser_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses enum declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/parser_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses module-level expression as pseudo-decl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
