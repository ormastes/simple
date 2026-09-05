# Result Ce Specification

> <details>

<!-- sdn-diagram:id=result_ce_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=result_ce_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

result_ce_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=result_ce_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Result Ce Specification

## Scenarios

### ResultCE builder

### result_ce_zero

#### returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_ce_zero()).to_be_nil()
```

</details>

### result_ce_return

#### returns integer value unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_ce_return(42)).to_equal(42)
```

</details>

#### returns text value unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_ce_return("ok")).to_equal("ok")
```

</details>

#### returns zero unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_ce_return(0)).to_equal(0)
```

</details>

### result_ce_bind

#### calls continuation on non-nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind("hello", fn(v):
    "got: {v}"
)
expect(result).to_equal("got: hello")
```

</details>

#### short-circuits on nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind(nil, fn(v):
    "should not reach"
)
expect(result).to_be_nil()
```

</details>

#### passes integer to continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind(10, fn(n):
    n + 5
)
expect(result).to_equal(15)
```

</details>

#### chains two successful binds

- result ce bind
   - Expected: result equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind("a", fn(x):
    result_ce_bind("b", fn(y):
        "{x}{y}"
    )
)
expect(result).to_equal("ab")
```

</details>

#### chain short-circuits when first is nil

- result ce bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind(nil, fn(x):
    result_ce_bind("b", fn(y):
        "{x}{y}"
    )
)
expect(result).to_be_nil()
```

</details>

#### chain short-circuits when second is nil

- result ce bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind("a", fn(x):
    result_ce_bind(nil, fn(y):
        "{x}{y}"
    )
)
expect(result).to_be_nil()
```

</details>

#### chains three levels successfully

- result ce bind
- result ce bind
   - Expected: result equals `xyz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind("x", fn(a):
    result_ce_bind("y", fn(b):
        result_ce_bind("z", fn(c):
            "{a}{b}{c}"
        )
    )
)
expect(result).to_equal("xyz")
```

</details>

#### chain short-circuits at middle nil

- result ce bind
- result ce bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_bind("x", fn(a):
    result_ce_bind(nil, fn(b):
        result_ce_bind("z", fn(c):
            "{a}{b}{c}"
        )
    )
)
expect(result).to_be_nil()
```

</details>

### result_ce_map

#### transforms a non-nil text value

- v len
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_map("hello", fn(v):
    v.len()
)
expect(result).to_equal(5)
```

</details>

#### transforms a non-nil integer value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_map(7, fn(n):
    n * 3
)
expect(result).to_equal(21)
```

</details>

#### passes through nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_map(nil, fn(v):
    "transformed"
)
expect(result).to_be_nil()
```

</details>

#### can be chained with bind

- v len
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bound = result_ce_bind("hello", fn(v): v)
val result = result_ce_map(bound, fn(v):
    v.len()
)
expect(result).to_equal(5)
```

</details>

### result_ce_combine

#### returns result of second when first succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_combine("first", fn():
    "second"
)
expect(result).to_equal("second")
```

</details>

#### short-circuits when first is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_combine(nil, fn():
    "second"
)
expect(result).to_be_nil()
```

</details>

#### returns integer second when first succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_combine("ok", fn():
    42
)
expect(result).to_equal(42)
```

</details>

#### returns nil when second thunk returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_combine("first", fn():
    nil
)
expect(result).to_be_nil()
```

</details>

### result_ce_for

#### returns nil after iterating empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_for([], fn(item):
    item
)
expect(result).to_be_nil()
```

</details>

#### returns nil after iterating array where body returns non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_for(["a", "b", "c"], fn(item):
    item
)
expect(result).to_be_nil()
```

</details>

#### short-circuits when body returns nil on first element

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_for(["a", "b", "c"], fn(item):
    nil
)
expect(result).to_be_nil()
```

</details>

#### returns nil when body never returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_ce_for(["x", "y"], fn(item):
    "processed: {item}"
)
expect(result).to_be_nil()
```

</details>

### composition patterns

#### bind then map succeeds

- v len
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bound = result_ce_bind("hello", fn(v): v)
val result = result_ce_map(bound, fn(v):
    v.len()
)
expect(result).to_equal(5)
```

</details>

#### map after nil bind returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bound = result_ce_bind(nil, fn(v): v)
val result = result_ce_map(bound, fn(v):
    "should not reach"
)
expect(result).to_be_nil()
```

</details>

#### combine after successful bind executes second

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bound = result_ce_bind("first", fn(v): v)
val result = result_ce_combine(bound, fn():
    "combined"
)
expect(result).to_equal("combined")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/result_ce_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ResultCE builder
- result_ce_zero
- result_ce_return
- result_ce_bind
- result_ce_map
- result_ce_combine
- result_ce_for
- composition patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
