# Star Export Lint Specification

> <details>

<!-- sdn-diagram:id=star_export_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=star_export_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

star_export_lint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=star_export_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Star Export Lint Specification

## Scenarios

### Star export lint (W0407)

#### star_import.spl contains check_star_export function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("fn check_star_export(")).to_equal(true)
```

</details>

#### detects wildcard via ends_with check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("ends_with(\".*\")")).to_equal(true)
```

</details>

#### emits W0407 code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("\"W0407\"")).to_equal(true)
```

</details>

#### has facade exemption for __init__.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("__init__.spl")).to_equal(true)
```

</details>

#### has facade exemption for mod.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("mod.spl")).to_equal(true)
```

</details>

#### strips .* suffix to get module_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("n.slice(0, n.len() - 2)")).to_equal(true)
```

</details>

#### uses unified StarWildcardWarning struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("struct StarWildcardWarning:")).to_equal(true)
```

</details>

#### has shared _is_facade_file helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("fn _is_facade_file(")).to_equal(true)
```

</details>

#### is registered in __init__.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("export check_star_export, check_star_export_file")).to_equal(true)
```

</details>

#### is integrated in query_lint.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/app/cli/query_lint.spl")
expect(source.contains("check_star_export_file")).to_equal(true)
expect(source.contains("Star wildcard warnings")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/star_export_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Star export lint (W0407)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
