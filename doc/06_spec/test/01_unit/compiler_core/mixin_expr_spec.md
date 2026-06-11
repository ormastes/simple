# Mixin Expr Specification

> <details>

<!-- sdn-diagram:id=mixin_expr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mixin_expr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mixin_expr_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mixin_expr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mixin Expr Specification

## Scenarios

### Mixin Expr

#### should reserve the mixin keyword token

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/tokens.spl")
expect(src.contains("const TOK_KW_MIXIN: i64 = 203")).to_equal(true)
expect(src.contains("if name == \"mixin\": return TOK_KW_MIXIN")).to_equal(true)
expect(src.contains("if kind == TOK_KW_MIXIN: return \"mixin\"")).to_equal(true)
```

</details>

#### should parse mixin calls as __mixin builtin calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_primary_part2.spl")
expect(src.contains("mixin(code_text) -- compile-time code generation")).to_equal(true)
expect(src.contains("if par_kind_get() == 203")).to_equal(true)
expect(src.contains("val mixin_arg = parse_expr()")).to_equal(true)
expect(src.contains("val mixin_callee = expr_ident(\"__mixin\", 0)")).to_equal(true)
expect(src.contains("return expr_call(mixin_callee, mixin_args_list, 0)")).to_equal(true)
```

</details>

#### should evaluate mixin code by parsing generated source

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if name == \"__mixin\"")).to_equal(true)
expect(src.contains("val mx_code = val_to_text(mx_code_val)")).to_equal(true)
expect(src.contains("parse_module_file(mx_code, \"mixin_generated.spl\")")).to_equal(true)
expect(src.contains("val mx_all_decls = module_get_decls()")).to_equal(true)
```

</details>

#### should register generated functions structs and declarations

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("func_table_register(mx_fn_name, mx_did)")).to_equal(true)
expect(src.contains("func_register_return_type(mx_fn_name, decl_get(mx_did).ret_type)")).to_equal(true)
expect(src.contains("struct_table_register(mx_struct_name, mx_did)")).to_equal(true)
expect(src.contains("eval_decl(mx_did2)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/mixin_expr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mixin Expr

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
