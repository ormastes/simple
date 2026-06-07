# File Class Introspection Specification

> <details>

<!-- sdn-diagram:id=file_class_introspection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_class_introspection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_class_introspection_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_class_introspection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Class Introspection Specification

## Scenarios

### File Class Introspection

#### should desugar dotted FILE access into module_file traits

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_expr.spl")
expect(src.contains(".FILE -> __traits(\"module_file\", \"dotted.path\")")).to_equal(true)
expect(src.contains("ppo_mf_args.push(expr_string_lit(\"module_file\", 0))")).to_equal(true)
expect(src.contains("val ppo_mf_callee = expr_ident(\"__traits\", 0)")).to_equal(true)
```

</details>

#### should desugar class and wildcard access into traits calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_expr.spl")
expect(src.contains(".class -> __traits(\"class_info\", \"TypeName\")")).to_equal(true)
expect(src.contains("ppo_ci_args.push(expr_string_lit(\"class_info\", 0))")).to_equal(true)
expect(src.contains(".* -> __traits(\"module_wildcard\", \"dotted.prefix\")")).to_equal(true)
expect(src.contains("ppo_mw_args.push(expr_string_lit(\"module_wildcard\", 0))")).to_equal(true)
```

</details>

#### should return File structs for module_file queries

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if tr_query == \"module_file\"")).to_equal(true)
expect(src.contains("val mf_file_path = module_get_file_path(mf_mod_name)")).to_equal(true)
expect(src.contains("var mf_fields: [text] = [\"path\", \"module_name\", \"exists\"]")).to_equal(true)
expect(src.contains("return val_make_struct(\"File\", mf_fields, mf_vals)")).to_equal(true)
```

</details>

#### should return Class structs with fields methods and counts

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if tr_query == \"class_info\"")).to_equal(true)
expect(src.contains("val ci_struct_decl = struct_table_lookup(ci_type_name)")).to_equal(true)
expect(src.contains("\"field_count\", \"method_count\"")).to_equal(true)
expect(src.contains("ci_s_vals.push(val_make_int(ci_field_names.len()))")).to_equal(true)
expect(src.contains("return val_make_struct(\"Class\", ci_s_fields, ci_s_vals)")).to_equal(true)
```

</details>

#### should return File arrays for module wildcard queries

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(src.contains("if tr_query == \"module_wildcard\"")).to_equal(true)
expect(src.contains("val mw_prefix = val_to_text(mw_prefix_val) + \".\"")).to_equal(true)
expect(src.contains("for mw_path in loaded_module_paths")).to_equal(true)
expect(src.contains("mw_result.push(val_make_struct(\"File\", mw_f_fields, mw_f_vals))")).to_equal(true)
expect(src.contains("return val_make_array(mw_result)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/file_class_introspection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- File Class Introspection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
