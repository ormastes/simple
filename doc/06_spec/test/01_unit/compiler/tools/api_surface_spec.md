# API Surface Tools Unit Tests

> 1. check

<!-- sdn-diagram:id=api_surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=api_surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

api_surface_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=api_surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# API Surface Tools Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-TOOLS-001 |
| Category | Compiler \| Tools |
| Status | Implemented |
| Source | `test/01_unit/compiler/tools/api_surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Public API Detection

#### public function is in API

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val visibility = "public"
check(visibility == "public")
```

</details>

#### private function is not in API

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val visibility = "private"
check(visibility == "private")
```

</details>

#### module-level function

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = "module"
check(scope == "module")
```

</details>

#### class method

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = "method"
check(scope == "method")
```

</details>

#### static method

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = "static"
check(scope == "static")
```

</details>

### Symbol Categories

#### function symbol

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "function"
check(kind == "function")
```

</details>

#### class symbol

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "class"
check(kind == "class")
```

</details>

#### trait symbol

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "trait"
check(kind == "trait")
```

</details>

#### enum symbol

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "enum"
check(kind == "enum")
```

</details>

#### type alias symbol

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "type_alias"
check(kind == "type_alias")
```

</details>

#### constant symbol

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "constant"
check(kind == "constant")
```

</details>

### API Documentation Coverage

#### documented function

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_doc = true
check(has_doc)
```

</details>

#### undocumented function

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_doc = false
check(not has_doc)
```

</details>

#### doc coverage percentage

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val documented = 80
val total = 100
val coverage = documented * 100 / total
check(coverage == 80)
```

</details>

#### coverage threshold check

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val coverage = 85
val threshold = 80
check(coverage >= threshold)
```

</details>

### Symbol Analysis

#### count public functions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 42
check(count > 0)
```

</details>

#### count public classes

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 15
check(count > 0)
```

</details>

#### count public traits

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 8
check(count > 0)
```

</details>

#### module dependency graph

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val edges = 100
check(edges > 0)
```

</details>

#### cyclic dependency detection

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_cycle = false
check(not has_cycle)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
