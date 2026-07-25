# spec_matchers_spec

> Tests for BDD matchers in the SPipe framework.

<!-- sdn-diagram:id=spec_matchers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spec_matchers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spec_matchers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spec_matchers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_matchers_spec

Tests for BDD matchers in the SPipe framework.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/spec_matchers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for BDD matchers in the SPipe framework.
Validates core matchers, comparison matchers, string matchers,
collection matchers, and negated assertions.

## Scenarios

### BDD Matchers

#### core matchers

#### eq matcher tests equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 to eq 5
expect "hello" to eq "hello"
expect true to eq true
```

</details>

#### be matcher tests identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
expect x to be 5
```

</details>

#### be_nil matcher tests None

1. expect nothing to be nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nothing = nil
expect nothing to be_nil()
```

</details>

#### comparison matchers (numbers)

#### gt (greater than) matcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 to gt 5
expect 100 to gt 50
```

</details>

#### lt (less than) matcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 to lt 10
expect 1 to lt 100
```

</details>

#### gte (greater than or equal) matcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 to gte 5
expect 5 to gte 5
```

</details>

#### lte (less than or equal) matcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 3 to lte 10
expect 5 to lte 5
```

</details>

#### multiple comparisons in one test

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 to gt 0
expect 5 to gte 5
expect 5 to lt 10
expect 5 to lte 5
```

</details>

#### string matchers

#### include matcher for strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello world" to include "world"
expect "hello world" to include "hello"
```

</details>

#### start_with matcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello world" to start_with "hello"
```

</details>

#### end_with matcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello world" to end_with "world"
```

</details>

#### collection matchers

#### include matcher for arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr to include 3
expect arr to include 1
```

</details>

#### negated assertions

#### not_to with eq

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 not_to eq 6
expect "hello" not_to eq "world"
```

</details>

#### not_to with comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 5 not_to gt 10
expect 5 not_to lt 1
```

</details>

#### not_to with include

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "hello" not_to include "xyz"
```

</details>

#### complex matcher chains

#### chains multiple matchers on same value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10 to gt 5
expect 10 to gte 10
expect 10 to lt 20
expect 10 to lte 10
```

</details>

#### matchers with computed values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 3
val result = x + y
expect result to eq 8
expect result to gt 7
expect result to lt 10
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
