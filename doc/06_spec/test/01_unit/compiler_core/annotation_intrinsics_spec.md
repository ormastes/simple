# Annotation Intrinsics Specification

> <details>

<!-- sdn-diagram:id=annotation_intrinsics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=annotation_intrinsics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

annotation_intrinsics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=annotation_intrinsics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Annotation Intrinsics Specification

## Scenarios

### Annotation Intrinsics

#### should parse source location annotation identifiers

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser_src = read_source("src/compiler/10.frontend/core/parser_primary_part2.spl")
expect(parser_src.contains("@file")).to_equal(true)
expect(parser_src.contains("@line")).to_equal(true)
expect(parser_src.contains("@function")).to_equal(true)
expect(parser_src.contains("__builtin_file")).to_equal(true)
```

</details>

#### should evaluate source location annotation identifiers

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eval_src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(eval_src.contains("if name == \"@file\"")).to_equal(true)
expect(eval_src.contains("if name == \"@line\"")).to_equal(true)
expect(eval_src.contains("if name == \"@function\"")).to_equal(true)
expect(eval_src.contains("module_get_path()")).to_equal(true)
```

</details>

#### should reject failing static assertions with a diagnostic

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builtins_src = read_source("src/compiler/10.frontend/core/interpreter/eval_builtins.spl")
expect(builtins_src.contains("if name == \"@static_assert\"")).to_equal(true)
expect(builtins_src.contains("static_assert failed")).to_equal(true)
expect(builtins_src.contains("tr_query == \"static_assert\"")).to_equal(true)
```

</details>

#### should keep must_use scanning available through interpreter exports

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tables_src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
val init_src = read_source("src/compiler/10.frontend/core/interpreter/__init__.spl")
expect(tables_src.contains("fn must_use_scan_source(source: text)")).to_equal(true)
expect(tables_src.contains("@must_use")).to_equal(true)
expect(init_src.contains("export must_use_scan_source")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/annotation_intrinsics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Annotation Intrinsics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
