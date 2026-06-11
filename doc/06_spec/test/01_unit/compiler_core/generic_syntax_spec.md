# Generic Syntax Specification

> <details>

<!-- sdn-diagram:id=generic_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generic_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generic_syntax_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generic_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Syntax Specification

## Scenarios

### Generic Syntax

#### should parse generic type parameter lists on declarations

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_decls_part1.spl")
expect(src.contains("fn parse_type_params() -> [text]")).to_equal(true)
expect(src.contains("val has_lt: bool = par_kind_get() == 82")).to_equal(true)
expect(src.contains("val has_lt_gen: bool = par_kind_get() == 86")).to_equal(true)
expect(src.contains("type_params.push(param_name)")).to_equal(true)
expect(src.contains("parser_expect(83)")).to_equal(true)
```

</details>

#### should support inline generic constraints

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_decls_part1.spl")
expect(src.contains("parse_type_param_constraint_list")).to_equal(true)
expect(src.contains("val is_limits: bool = par_kind_get() == 214")).to_equal(true)
expect(src.contains("val is_candidates: bool = par_kind_get() == 215")).to_equal(true)
expect(src.contains("file_generic_constraints[param_name] = filtered")).to_equal(true)
expect(src.contains("file_generic_constraint_modes[param_name] = mode_str")).to_equal(true)
```

</details>

#### should attach generic parameters to function declarations

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_decls_part1.spl")
expect(src.contains("val type_params = parse_type_params()")).to_equal(true)
expect(src.contains("decl_fn(fn_name, param_names, param_types, ret_type, body, is_async, type_params, 0)")).to_equal(true)
expect(src.contains("decl_extern_fn(fn_name, param_names, param_types, ret_type, type_params, 0)")).to_equal(true)
```

</details>

#### should persist generic parameters in AST declarations

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/ast_part1.spl")
expect(src.contains("var decl_type_params: [[text]] = []")).to_equal(true)
expect(src.contains("fn decl_fn(name: text, param_names: [text], param_types: [i64], ret_type: i64, body: [i64], is_async: i64, type_params: [text], span_id: i64) -> i64")).to_equal(true)
expect(src.contains("ast_decl_text_set(idx, \"TYPE_PARAMS\", ast_text_list_join(type_params))")).to_equal(true)
expect(src.contains("fn decl_get_type_params(idx: i64) -> [text]")).to_equal(true)
```

</details>

#### should parse generic type annotations without confusing comparisons

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser.spl")
expect(src.contains("Check for generic type: Option<T>, Result<T, E>, Dict<K,V>, etc.")).to_equal(true)
expect(src.contains("val has_generic: bool = has_lt or has_lt_gen")).to_equal(true)
expect(src.contains("if type_name == \"Option\"")).to_equal(true)
expect(src.contains("if type_name == \"Result\"")).to_equal(true)
expect(src.contains("if type_name == \"Dict\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/generic_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generic Syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
