# Dsl Specification

> 1. expect builder is empty

<!-- sdn-diagram:id=dsl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dsl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dsl_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dsl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dsl Specification

## Scenarios

### Context blocks

#### provides context-aware building

1. expect builder is empty
2. builder set
3. builder set
4. expect builder has
5. expect builder get
6. expect builder size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = ContextBuilder.new()
expect builder.is_empty() == true

builder.set("name", "Alice")
builder.set("age", 30)

expect builder.has("name") == true
expect builder.get("name") == "Alice"
expect builder.size() == 2
```

</details>

### Method missing

#### handles undefined methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var called_name = ""
var called_args = []

val handler = fn(name, args):
    called_name = name
    called_args = args
    42
val proxy = DynamicProxy.new(handler)

val result = proxy.method_missing("test_method", [1, 2, 3])
expect result == 42
expect called_name == "test_method"
```

</details>

#### enables dynamic proxies

1. expect proxy has handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = \name, args: "handled"
val proxy = DynamicProxy.new(handler)

expect proxy.has_handler() == true
val result = proxy.call_handler("any_method", [])
expect result == "handled"
```

</details>

#### supports attribute dictionaries

1. expect obj is empty
2. obj   setattr
3. expect obj has attr


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = AttributeDict.new()
expect obj.is_empty() == true

obj.__setattr__("name", "Alice")
val name = obj.__getattr__("name")
expect name == "Alice"
expect obj.has_attr("name") == true
```

</details>

### Fluent interfaces

#### enables method chaining

1. query select
2. query from table
3. expect query has table
4. expect query field count
5. expect query is valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = QueryBuilder.new()
query.select(["name", "age"])
query.from_table("users")

expect query.has_table() == true
expect query.field_count() == 2
expect query.is_valid() == true
```

</details>

#### supports pipeline transformations

1. expect pipe size
2. pipe filter
3. expect pipe size
4. expect len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pipe = Pipeline.new([1, 2, 3, 4, 5])
expect pipe.size() == 5

pipe.filter(_1 > 2)
expect pipe.size() == 3

val result = pipe.collect()
expect len(result) == 3
expect result[0] == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/core/dsl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Context blocks
- Method missing
- Fluent interfaces

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
