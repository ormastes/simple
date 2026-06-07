# Object Resolver Specification

> <details>

<!-- sdn-diagram:id=object_resolver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=object_resolver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

object_resolver_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=object_resolver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Object Resolver Specification

## Scenarios

### Object Resolver

#### generates the expected object file candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val candidates = generate_object_candidates("std/io/mod")
expect(candidates.contains("std/io/mod.o")).to_equal(true)
expect(candidates.contains("std_io_mod.o")).to_equal(true)
expect(candidates.contains("mod.o")).to_equal(true)
expect(candidates.contains("src/std/io/mod.o")).to_equal(true)
```

</details>

#### handles single-component and deep module names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(generate_object_candidates("math").len()).to_be_greater_than(0)
expect(generate_object_candidates("a/b/c/d/e").len()).to_be_greater_than(3)
```

</details>

#### returns standard search paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = default_object_search_paths()
expect(paths.len()).to_be_greater_than(0)
expect(paths.contains("build/obj")).to_equal(true)
expect(paths.contains(".")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/object_resolver_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Object Resolver

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
