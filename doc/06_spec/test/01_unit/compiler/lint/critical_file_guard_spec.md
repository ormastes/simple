# Critical File Guard Specification

> <details>

<!-- sdn-diagram:id=critical_file_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=critical_file_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

critical_file_guard_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=critical_file_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Critical File Guard Specification

## Scenarios

### Critical file guard lint

#### config/critical_files.sdn exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("config/critical_files.sdn")).to_equal(true)
```

</details>

#### config has entries section

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file("config/critical_files.sdn")
expect(content.contains("entries:")).to_equal(true)
```

</details>

#### config protects star_import.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file("config/critical_files.sdn")
expect(content.contains("src/compiler/35.semantics/lint/star_import.spl")).to_equal(true)
```

</details>

#### config protects error.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file("config/critical_files.sdn")
expect(content.contains("src/compiler/00.common/error.spl")).to_equal(true)
```

</details>

#### config protects itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = read_file("config/critical_files.sdn")
expect(content.contains("config/critical_files.sdn")).to_equal(true)
```

</details>

#### guard module has CFG001 deletion check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/critical_file_guard.spl")
expect(source.contains("\"CFG001\"")).to_equal(true)
expect(source.contains("critical file deleted")).to_equal(true)
```

</details>

#### guard module has CFG002 shrinkage check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/critical_file_guard.spl")
expect(source.contains("\"CFG002\"")).to_equal(true)
expect(source.contains("shrunk below")).to_equal(true)
```

</details>

#### guard is registered in __init__.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("export critical_file_guard.*")).to_equal(true)
```

</details>

#### guard is integrated in query_lint.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/app/cli/query_lint.spl")
expect(source.contains("check_all_critical_files")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/critical_file_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Critical file guard lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
