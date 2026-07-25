# Option Ce Specification

> <details>

<!-- sdn-diagram:id=option_ce_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=option_ce_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

option_ce_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=option_ce_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Ce Specification

## Scenarios

### OptionCE builder

### option_ce_zero

#### returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_ce_zero()).to_be_nil()
```

</details>

### option_ce_return

#### returns integer value unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_ce_return(99)).to_equal(99)
```

</details>

#### returns text value unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_ce_return("hello")).to_equal("hello")
```

</details>

#### returns zero unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_ce_return(0)).to_equal(0)
```

</details>

### option_ce_bind

#### calls continuation on non-nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_bind("value", fn(v):
    "wrapped: {v}"
)
expect(result).to_equal("wrapped: value")
```

</details>

#### short-circuits on nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_bind(nil, fn(v):
    "should not reach"
)
expect(result).to_be_nil()
```

</details>

#### passes integer through to continuation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_bind(42, fn(n):
    n * 2
)
expect(result).to_equal(84)
```

</details>

#### chains two binds successfully

- option ce bind
   - Expected: result equals `user:profile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_bind("user", fn(u):
    option_ce_bind("profile", fn(p):
        "{u}:{p}"
    )
)
expect(result).to_equal("user:profile")
```

</details>

#### chain short-circuits when inner bind is nil

- option ce bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_bind("user", fn(u):
    option_ce_bind(nil, fn(p):
        "{u}:{p}"
    )
)
expect(result).to_be_nil()
```

</details>

#### chain short-circuits on first nil

- option ce bind


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_bind(nil, fn(u):
    option_ce_bind("profile", fn(p):
        "{u}:{p}"
    )
)
expect(result).to_be_nil()
```

</details>

#### chains three levels successfully

- option ce bind
- option ce bind
   - Expected: result equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_bind("a", fn(x):
    option_ce_bind("b", fn(y):
        option_ce_bind("c", fn(z):
            "{x}{y}{z}"
        )
    )
)
expect(result).to_equal("abc")
```

</details>

### option_ce_or_else

#### returns value when non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_or_else("found", fn():
    "default"
)
expect(result).to_equal("found")
```

</details>

#### calls alternative when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_or_else(nil, fn():
    "default"
)
expect(result).to_equal("default")
```

</details>

#### returns integer value when non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_or_else(5, fn():
    0
)
expect(result).to_equal(5)
```

</details>

#### calls alternative returning integer when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_or_else(nil, fn():
    42
)
expect(result).to_equal(42)
```

</details>

### option_ce_map

#### transforms a non-nil text value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_map("hello", fn(v):
    "mapped: {v}"
)
expect(result).to_equal("mapped: hello")
```

</details>

#### transforms a non-nil integer value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_map(5, fn(v):
    v * 3
)
expect(result).to_equal(15)
```

</details>

#### returns nil for nil input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_map(nil, fn(v):
    "should not reach"
)
expect(result).to_be_nil()
```

</details>

#### can chain map operations via bind

- v len
   - Expected: step2 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val step1 = option_ce_map("hello", fn(v):
    v.len()
)
val step2 = option_ce_map(step1, fn(n):
    n * 2
)
expect(step2).to_equal(10)
```

</details>

### option_ce_filter

#### keeps value when predicate is true

- v len
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_filter("hello", fn(v):
    v.len() > 0
)
expect(result).to_equal("hello")
```

</details>

#### returns nil when predicate is false

- v len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_filter("hi", fn(v):
    v.len() > 10
)
expect(result).to_be_nil()
```

</details>

#### passes through nil input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_filter(nil, fn(v):
    true
)
expect(result).to_be_nil()
```

</details>

#### works with integer predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_filter(42, fn(n):
    n > 10
)
expect(result).to_equal(42)
```

</details>

#### filters out integer when predicate fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_ce_filter(3, fn(n):
    n > 10
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
val bound = option_ce_bind("hello", fn(v): v)
val result = option_ce_map(bound, fn(v):
    v.len()
)
expect(result).to_equal(5)
```

</details>

#### bind then filter on matching predicate

- v len
   - Expected: result equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bound = option_ce_bind("hello", fn(v): v)
val result = option_ce_filter(bound, fn(v):
    v.len() > 3
)
expect(result).to_equal("hello")
```

</details>

#### or_else after nil bind returns alternative

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bound = option_ce_bind(nil, fn(v): v)
val result = option_ce_or_else(bound, fn():
    "fallback"
)
expect(result).to_equal("fallback")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/option_ce_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OptionCE builder
- option_ce_zero
- option_ce_return
- option_ce_bind
- option_ce_or_else
- option_ce_map
- option_ce_filter
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
