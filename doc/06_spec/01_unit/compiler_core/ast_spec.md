# ast_spec

> Purpose: Prove that core.ast.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ast_spec

Purpose: Prove that core.ast.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/ast_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that core.ast.
Audience: COMP-CORE maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### core.ast

### expressions

#### creates literals and identifiers

- creates literals and identifiers
- Verify: creates literals and identifiers
   - Expected: expr_get_tag(e1) equals `EXPR_INT_LIT`
   - Expected: expr_get_int(e1) equals `42`
   - Expected: expr_get_tag(e2) equals `EXPR_FLOAT_LIT`
   - Expected: expr_get_float(e2) equals `3.14`
   - Expected: expr_get_tag(e3) equals `EXPR_STRING_LIT`
   - Expected: expr_get_str(e3) equals `hi`
   - Expected: expr_get_tag(e4) equals `EXPR_BOOL_LIT`
   - Expected: expr_get_int(e4) equals `1`
   - Expected: expr_get_tag(e5) equals `EXPR_NIL_LIT`
   - Expected: expr_get_tag(e6) equals `EXPR_IDENT`
   - Expected: expr_get_str(e6) equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates literals and identifiers")
step("Verify: creates literals and identifiers")
# @req: REQ-COMP-CORE-CORE-AST-001
val e1 = expr_int_lit(42, 0)
val e2 = expr_float_lit("3.14", 0)
val e3 = expr_string_lit("hi", 0)
val e4 = expr_bool_lit(1, 0)
val e5 = expr_nil_lit(0)
val e6 = expr_ident("x", 0)
expect(expr_get_tag(e1)).to_equal(EXPR_INT_LIT)
expect(expr_get_int(e1)).to_equal(42)
expect(expr_get_tag(e2)).to_equal(EXPR_FLOAT_LIT)
expect(expr_get_float(e2)).to_equal("3.14")
expect(expr_get_tag(e3)).to_equal(EXPR_STRING_LIT)
expect(expr_get_str(e3)).to_equal("hi")
expect(expr_get_tag(e4)).to_equal(EXPR_BOOL_LIT)
expect(expr_get_int(e4)).to_equal(1)
expect(expr_get_tag(e5)).to_equal(EXPR_NIL_LIT)
expect(expr_get_tag(e6)).to_equal(EXPR_IDENT)
expect(expr_get_str(e6)).to_equal("x")
```

</details>

#### creates binary and unary

- creates binary and unary
- Verify: creates binary and unary
   - Expected: expr_get_tag(bin) equals `EXPR_BINARY`
   - Expected: expr_get_left(bin) equals `left`
   - Expected: expr_get_right(bin) equals `right`
   - Expected: expr_get_int(bin) equals `TOK_PLUS`
   - Expected: expr_get_tag(un) equals `EXPR_UNARY`
   - Expected: expr_get_left(un) equals `right`
   - Expected: expr_get_int(un) equals `TOK_MINUS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates binary and unary")
step("Verify: creates binary and unary")
val left = expr_int_lit(1, 0)
val right = expr_int_lit(2, 0)
val bin = expr_binary(TOK_PLUS, left, right, 0)
val un = expr_unary(TOK_MINUS, right, 0)
expect(expr_get_tag(bin)).to_equal(EXPR_BINARY)
expect(expr_get_left(bin)).to_equal(left)
expect(expr_get_right(bin)).to_equal(right)
expect(expr_get_int(bin)).to_equal(TOK_PLUS)
expect(expr_get_tag(un)).to_equal(EXPR_UNARY)
expect(expr_get_left(un)).to_equal(right)
expect(expr_get_int(un)).to_equal(TOK_MINUS)
```

</details>

#### creates arrays, tuples, dicts

- creates arrays, tuples, dicts
- Verify: creates arrays, tuples, dicts
   - Expected: expr_get_tag(a) equals `EXPR_ARRAY_LIT`
   - Expected: expr_get_args(a).len() equals `2`
   - Expected: expr_get_tag(t) equals `EXPR_TUPLE`
   - Expected: expr_get_args(t).len() equals `2`
   - Expected: expr_get_tag(d) equals `EXPR_DICT_LIT`
   - Expected: expr_get_args(d).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates arrays, tuples, dicts")
step("Verify: creates arrays, tuples, dicts")
val a = expr_array_lit([expr_int_lit(1, 0), expr_int_lit(2, 0)], 0)
val t = expr_tuple([expr_int_lit(3, 0), expr_int_lit(4, 0)], 0)
val d = expr_dict_lit([expr_string_lit("k", 0)], [expr_int_lit(9, 0)], 0)
expect(expr_get_tag(a)).to_equal(EXPR_ARRAY_LIT)
expect(expr_get_args(a).len()).to_equal(2)
expect(expr_get_tag(t)).to_equal(EXPR_TUPLE)
expect(expr_get_args(t).len()).to_equal(2)
expect(expr_get_tag(d)).to_equal(EXPR_DICT_LIT)
expect(expr_get_args(d).len()).to_equal(2)
```

</details>

#### creates struct literals and ranges

- creates struct literals and ranges
- Verify: creates struct literals and ranges
   - Expected: expr_get_tag(s) equals `EXPR_STRUCT_LIT`
   - Expected: expr_get_str(s) equals `Point`
   - Expected: expr_get_tag(r) equals `EXPR_RANGE`
   - Expected: expr_get_extra(r) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates struct literals and ranges")
step("Verify: creates struct literals and ranges")
val s = expr_struct_lit("Point", [expr_ident("x", 0)], [expr_int_lit(1, 0)], 0)
val r = expr_range(expr_int_lit(0, 0), expr_int_lit(10, 0), 1, 0)
expect(expr_get_tag(s)).to_equal(EXPR_STRUCT_LIT)
expect(expr_get_str(s)).to_equal("Point")
expect(expr_get_tag(r)).to_equal(EXPR_RANGE)
expect(expr_get_extra(r)).to_equal(1)
```

</details>

#### creates assignments

- creates assignments
- Verify: creates assignments
   - Expected: expr_get_tag(asn) equals `EXPR_ASSIGN`
   - Expected: expr_get_tag(casn) equals `EXPR_COMPOUND_ASSIGN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates assignments")
step("Verify: creates assignments")
val target = expr_ident("x", 0)
val value = expr_int_lit(5, 0)
val asn = expr_assign(target, value, 0)
val casn = expr_compound_assign(TOK_PLUS, target, value, 0)
expect(expr_get_tag(asn)).to_equal(EXPR_ASSIGN)
expect(expr_get_tag(casn)).to_equal(EXPR_COMPOUND_ASSIGN)
```

</details>

#### formats kind names

- formats kind names
- Verify: formats kind names
   - Expected: expr_kind_name(EXPR_INT_LIT) equals `IntLit`
   - Expected: expr_kind_name(EXPR_BINARY) equals `Binary`
   - Expected: expr_kind_name(EXPR_MATCH) equals `Match`
   - Expected: expr_kind_name(EXPR_STRUCT_LIT) equals `StructLit`
   - Expected: expr_kind_name(9999) equals `Unknown(9999)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("formats kind names")
step("Verify: formats kind names")
expect(expr_kind_name(EXPR_INT_LIT)).to_equal("IntLit")
expect(expr_kind_name(EXPR_BINARY)).to_equal("Binary")
expect(expr_kind_name(EXPR_MATCH)).to_equal("Match")
expect(expr_kind_name(EXPR_STRUCT_LIT)).to_equal("StructLit")
expect(expr_kind_name(9999)).to_equal("Unknown(9999)")
```

</details>

### statements

#### creates val/var declarations

- creates val/var declarations
- Verify: creates val/var declarations
   - Expected: stmt_get_tag(sv) equals `STMT_VAL_DECL`
   - Expected: stmt_get_name(sv) equals `x`
   - Expected: stmt_get_type(sv) equals `TYPE_I64`
   - Expected: stmt_get_tag(sv2) equals `STMT_VAR_DECL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates val/var declarations")
step("Verify: creates val/var declarations")
val init = expr_int_lit(1, 0)
val sv = stmt_val_decl("x", TYPE_I64, init, 0)
val sv2 = stmt_var_decl("y", 0, init, 0)
expect(stmt_get_tag(sv)).to_equal(STMT_VAL_DECL)
expect(stmt_get_name(sv)).to_equal("x")
expect(stmt_get_type(sv)).to_equal(TYPE_I64)
expect(stmt_get_tag(sv2)).to_equal(STMT_VAR_DECL)
```

</details>

#### creates control flow statements

- creates control flow statements
- Verify: creates control flow statements
   - Expected: stmt_get_tag(sif) equals `STMT_IF`
   - Expected: stmt_get_tag(sfor) equals `STMT_FOR`
   - Expected: stmt_get_tag(swhile) equals `STMT_WHILE`
   - Expected: stmt_get_tag(smatch) equals `STMT_MATCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates control flow statements")
step("Verify: creates control flow statements")
val cond = expr_bool_lit(1, 0)
val body = [stmt_return_stmt(expr_int_lit(1, 0), 0)]
val sif = stmt_if_stmt(cond, body, [], 0)
val sfor = stmt_for_stmt("i", expr_range(expr_int_lit(0, 0), expr_int_lit(1, 0), 0, 0), body, 0)
val swhile = stmt_while_stmt(cond, body, 0)
val smatch = stmt_match_stmt(cond, [], 0)
expect(stmt_get_tag(sif)).to_equal(STMT_IF)
expect(stmt_get_tag(sfor)).to_equal(STMT_FOR)
expect(stmt_get_tag(swhile)).to_equal(STMT_WHILE)
expect(stmt_get_tag(smatch)).to_equal(STMT_MATCH)
```

</details>

### declarations

#### creates functions and structs

- creates functions and structs
- Verify: creates functions and structs
   - Expected: decl_get_tag(df) equals `DECL_FN`
   - Expected: decl_get_name(df) equals `add`
   - Expected: decl_get_param_names(df).len() equals `1`
   - Expected: decl_get_ret_type(df) equals `TYPE_I64`
   - Expected: decl_get_tag(ds) equals `DECL_STRUCT`
   - Expected: decl_get_fields(ds).len() equals `1`
   - Expected: decl_get_field_types(ds)[0] equals `TYPE_I64`
   - Expected: decl_get_tag(de) equals `DECL_ENUM`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates functions and structs")
step("Verify: creates functions and structs")
val body = [stmt_return_stmt(expr_int_lit(1, 0), 0)]
val df = decl_fn("add", ["a"], [TYPE_I64], TYPE_I64, body, 0)
var no_defs: [i64] = []
val ds = decl_struct_def("Point", ["x"], [TYPE_I64], no_defs, 0)
val de = decl_enum_def("E", ["A"], 0)
expect(decl_get_tag(df)).to_equal(DECL_FN)
expect(decl_get_name(df)).to_equal("add")
expect(decl_get_param_names(df).len()).to_equal(1)
expect(decl_get_ret_type(df)).to_equal(TYPE_I64)
expect(decl_get_tag(ds)).to_equal(DECL_STRUCT)
expect(decl_get_fields(ds).len()).to_equal(1)
expect(decl_get_field_types(ds)[0]).to_equal(TYPE_I64)
expect(decl_get_tag(de)).to_equal(DECL_ENUM)
```

</details>

#### creates use/export/val/var

- creates use/export/val/var
- Verify: creates use/export/val/var
   - Expected: decl_get_tag(du) equals `DECL_USE`
   - Expected: decl_get_imports(du).len() equals `1`
   - Expected: decl_get_tag(dx) equals `DECL_EXPORT`
   - Expected: decl_get_tag(dv) equals `DECL_VAL`
   - Expected: decl_get_tag(dvar) equals `DECL_VAR`
   - Expected: decl_get_is_pub(dv) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("creates use/export/val/var")
step("Verify: creates use/export/val/var")
val du = decl_use_import("mod", ["x"], 0)
val dx = decl_export_names(["x"], 0)
val dv = decl_val_binding("x", TYPE_I64, expr_int_lit(1, 0), 0)
val dvar = decl_var_binding("y", TYPE_TEXT, expr_string_lit("s", 0), 0)
expect(decl_get_tag(du)).to_equal(DECL_USE)
expect(decl_get_imports(du).len()).to_equal(1)
expect(decl_get_tag(dx)).to_equal(DECL_EXPORT)
expect(decl_get_tag(dv)).to_equal(DECL_VAL)
expect(decl_get_tag(dvar)).to_equal(DECL_VAR)
expect(decl_get_is_pub(dv)).to_equal(false)
```

</details>

### module

#### tracks module path and decls

- tracks module path and decls
- Verify: tracks module path and decls
   - Expected: module_get_path() equals `m.spl`
   - Expected: module_get_decls().len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("tracks module path and decls")
step("Verify: tracks module path and decls")
module_set_path("m.spl")
expect(module_get_path()).to_equal("m.spl")
val d = decl_val_binding("x", TYPE_I64, expr_int_lit(1, 0), 0)
module_add_decl(d)
expect(module_get_decls().len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER_CORE`
- `REQ-COMP-CORE-CORE-AST-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a900f91f4b1cceb6116ea3b35c6253efb72bcb2f7eb62e74a22355cff6a8eb6e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a900f91f4b1cceb6116ea3b35c6253efb72bcb2f7eb62e74a22355cff6a8eb6e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a900f91f4b1cceb6116ea3b35c6253efb72bcb2f7eb62e74a22355cff6a8eb6e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler_core/ast_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/ast_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/ast_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/ast_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/ast_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler_core/ast_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates literals and identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ast_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates binary and unary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/ast_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates arrays, tuples, dicts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
