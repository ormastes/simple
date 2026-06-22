# Method Alias Forwarding Specification

> Tests that `alias fn` and `alias me` in class bodies desugar into correct forwarding methods. The desugar transforms: `alias fn len = inner.len`       -> `fn len(): self.inner.len()` `alias fn push(item) = inner.push` -> `fn push(item): self.inner.push(item)` `alias me increment = inner.increment` -> `me increment(): self.inner.increment()`

<!-- sdn-diagram:id=method_alias_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=method_alias_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

method_alias_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=method_alias_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Alias Forwarding Specification

Tests that `alias fn` and `alias me` in class bodies desugar into correct forwarding methods. The desugar transforms: `alias fn len = inner.len`       -> `fn len(): self.inner.len()` `alias fn push(item) = inner.push` -> `fn push(item): self.inner.push(item)` `alias me increment = inner.increment` -> `me increment(): self.inner.increment()`

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #FWD-002 |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/method_alias_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that `alias fn` and `alias me` in class bodies desugar into
correct forwarding methods. The desugar transforms:
`alias fn len = inner.len`       -> `fn len(): self.inner.len()`
`alias fn push(item) = inner.push` -> `fn push(item): self.inner.push(item)`
`alias me increment = inner.increment` -> `me increment(): self.inner.increment()`

These tests verify the generated delegation patterns work correctly
by writing the equivalent hand-expanded code.

## Scenarios

### method alias forwarding

#### immutable forwarding (alias fn)

#### forwards no-arg method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = make_wrapper(42)
expect(w.get_count()).to_equal(42)
```

</details>

#### forwards method with argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = make_wrapper(10)
expect(w.get_count_plus(5)).to_equal(15)
```

</details>

#### forwards zero value correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = make_wrapper(0)
expect(w.get_count()).to_equal(0)
```

</details>

#### mutable forwarding (alias me)

#### forwards no-arg mutable method

1. var w = make wrapper
2. w increment
   - Expected: w.get_count() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = make_wrapper(5)
w.increment()
expect(w.get_count()).to_equal(6)
```

</details>

#### forwards mutable method with argument

1. var w = make wrapper
2. w add
   - Expected: w.get_count() equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = make_wrapper(10)
w.add(7)
expect(w.get_count()).to_equal(17)
```

</details>

#### chains multiple mutable forwards

1. var w = make wrapper
2. w increment
3. w increment
4. w add
   - Expected: w.get_count() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = make_wrapper(0)
w.increment()
w.increment()
w.add(10)
expect(w.get_count()).to_equal(12)
```

</details>

#### forwarding preserves inner state

#### reads after mutation reflect changes

1. var w = make wrapper
2. w add
   - Expected: result equals `75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = make_wrapper(100)
w.add(-50)
val result = w.get_count_plus(25)
expect(result).to_equal(75)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
