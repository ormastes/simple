# Ignored Return Warning Specification

> <details>

<!-- sdn-diagram:id=ignored_return_warning_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ignored_return_warning_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ignored_return_warning_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ignored_return_warning_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ignored Return Warning Specification

## Scenarios

### Ignored Return Warning

#### should inspect expression statements for direct function calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("Check if this is a function call with ignored return value")).to_equal(true)
expect(src.contains("if e_tag == EXPR_CALL")).to_equal(true)
expect(src.contains("val callee_eid = e_node.left")).to_equal(true)
expect(src.contains("if callee_tag == EXPR_IDENT")).to_equal(true)
```

</details>

#### should use registered return types to suppress void and unknown calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmt_src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
val table_src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
expect(stmt_src.contains("val ret_type = func_lookup_return_type(fn_name)")).to_equal(true)
expect(stmt_src.contains("val is_void = ret_type == 0")).to_equal(true)
expect(stmt_src.contains("val is_unknown = ret_type == -1")).to_equal(true)
expect(stmt_src.contains("if is_void == false and is_unknown == false")).to_equal(true)
expect(table_src.contains("fn func_lookup_return_type(name: text) -> i64")).to_equal(true)
```

</details>

#### should emit normal ignored return warnings with type and function name

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("val type_name = type_tag_name(ret_type)")).to_equal(true)
expect(src.contains("warning: return value of type '")).to_equal(true)
expect(src.contains("from function '")).to_equal(true)
expect(src.contains("is ignored")).to_equal(true)
```

</details>

#### should route must_use and critical cases through R9 diagnostics

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("if must_use_is_registered(fn_name)")).to_equal(true)
expect(src.contains("error[R9]: return value of function '")).to_equal(true)
expect(src.contains("elif must_use_critical_mode")).to_equal(true)
expect(src.contains("discarded in @profile(critical)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/ignored_return_warning_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ignored Return Warning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
