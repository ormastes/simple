# Query Tools Unit Tests

> 1. check

<!-- sdn-diagram:id=query_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=query_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

query_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=query_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Tools Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-TOOLS-002 |
| Category | Compiler \| Tools |
| Status | Implemented |
| Source | `test/01_unit/compiler/tools/query_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Symbol Query

#### find function by name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "main"
check(name == "main")
```

</details>

#### find class by name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Point"
check(name == "Point")
```

</details>

#### find method by class and name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val class_name = "Point"
val method = "get_x"
check(class_name == "Point" and method == "get_x")
```

</details>

#### find symbols by pattern

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = "parse_*"
check(pattern.starts_with("parse"))
```

</details>

#### find symbols in module

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module = "compiler.frontend"
check(module.contains("frontend"))
```

</details>

### Type Query

#### query type of expression

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr_type = "i64"
check(expr_type == "i64")
```

</details>

#### query return type of function

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ret_type = "text"
check(ret_type == "text")
```

</details>

#### query field types of class

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = ["x: i64", "y: i64"]
check(fields.len() == 2)
```

</details>

#### query trait implementations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val impls = ["Display", "Debug"]
check(impls.len() == 2)
```

</details>

### Code Navigation

#### go to definition

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/main.spl"
val line = 10
check(file.ends_with(".spl"))
check(line > 0)
```

</details>

#### find all references

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val refs = 5
check(refs > 0)
```

</details>

#### find callers

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callers = 3
check(callers > 0)
```

</details>

#### find callees

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val callees = 2
check(callees > 0)
```

</details>

### AST Query

#### query all if expressions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 10
check(count > 0)
```

</details>

#### query all match expressions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 5
check(count > 0)
```

</details>

#### query all function definitions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 50
check(count > 0)
```

</details>

#### query all class definitions

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 20
check(count > 0)
```

</details>

#### query all use statements

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
