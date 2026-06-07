# Lang Basics Specification

> <details>

<!-- sdn-diagram:id=lang_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lang_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lang_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lang_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lang Basics Specification

## Scenarios

### LangBasics

<details>
<summary>Advanced: should keep while-loop coverage in the core language smoke file</summary>

#### should keep while-loop coverage in the core language smoke file

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/test_lang_basics.spl")
expect(src.contains("while count < 4:")).to_equal(true)
expect(src.contains("total = total + count")).to_equal(true)
expect(src.contains("check_eq_int(\"while sum\", total, 6)")).to_equal(true)
```

</details>


</details>

#### should parse while statements and while expressions

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/parser_stmts.spl")
expect(src.contains("fn parse_while_stmt() -> i64")).to_equal(true)
expect(src.contains("stmt_while_stmt(cond, body, 0)")).to_equal(true)
expect(src.contains("fn parse_while_expr() -> i64")).to_equal(true)
expect(src.contains("expr_while_expr(cond, body, 0)")).to_equal(true)
```

</details>

#### should evaluate while statements with a finite iteration guard

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("fn eval_stmt_while(sid: i64) -> i64")).to_equal(true)
expect(src.contains("while iterations < 1000000")).to_equal(true)
expect(src.contains("if val_is_truthy(cond_val) == false: break")).to_equal(true)
expect(src.contains("eval_set_error(\"while loop exceeded maximum iterations\")")).to_equal(true)
```

</details>

#### should evaluate while expressions with a finite iteration guard

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(src.contains("fn eval_while_expr(eid: i64) -> i64")).to_equal(true)
expect(src.contains("val max_iterations: i64 = 1000000")).to_equal(true)
expect(src.contains("if val_is_truthy(cond_val) == false: break")).to_equal(true)
expect(src.contains("eval_set_error(\"while loop exceeded maximum iterations\")")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/lang_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LangBasics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
