# Tmp Test Specification

> <details>

<!-- sdn-diagram:id=tmp_test_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_test_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_test_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_test_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test Specification

## Scenarios

### tmp test

#### should report undefined identifiers during expression evaluation

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(src.contains("fn eval_ident(eid: i64) -> i64")).to_equal(true)
expect(src.contains("val vid = env_lookup(name)")).to_equal(true)
expect(src.contains("val decl_id = func_table_lookup(name)")).to_equal(true)
expect(src.contains("eval_set_error(\"undefined variable: \" + name)")).to_equal(true)
```

</details>

#### should report undefined variables during statement assignment

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("eval_set_error(\"undefined variable: \" + name)")).to_equal(true)
expect(src.contains("val old_val = env_lookup(name)")).to_equal(true)
```

</details>

#### should keep the public undefined-name diagnostic helper exported

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_src = read_source("src/compiler/10.frontend/core/error.spl")
val init_src = read_source("src/compiler/10.frontend/core/__init__.spl")
expect(error_src.contains("fn error_undefined_name(line: i64, col: i64, name: text)")).to_equal(true)
expect(error_src.contains("undefined name `")).to_equal(true)
expect(init_src.contains("export error_undefined_name")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/tmp_test_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tmp test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
