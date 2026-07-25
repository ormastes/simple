# Treesitter Heuristic Optional Binding Specification

> <details>

<!-- sdn-diagram:id=treesitter_heuristic_optional_binding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=treesitter_heuristic_optional_binding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

treesitter_heuristic_optional_binding_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=treesitter_heuristic_optional_binding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Treesitter Heuristic Optional Binding Specification

## Scenarios

### TreeSitter heuristic colon extraction

#### handles signatures with a trailing colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = treesitter_with_heuristic_mode(true)
expect(parser.heuristic_extract_until_colon("fn main() -> i64:")).to_equal("fn main() -> i64")
```

</details>

#### keeps lines without a colon unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = treesitter_with_heuristic_mode(true)
expect(parser.heuristic_extract_until_colon("class Worker")).to_equal("class Worker")
```

</details>

#### extracts names without omitted-start slicing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = treesitter_with_heuristic_mode(true)
expect(parser.heuristic_extract_name("main()")).to_equal("main")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/treesitter_heuristic_optional_binding_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TreeSitter heuristic colon extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
