# MIR Optimization - Inlining Tests

> <details>

<!-- sdn-diagram:id=inlining_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inlining_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inlining_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inlining_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR Optimization - Inlining Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-MIROPT-003 |
| Category | Compiler \| MIR Optimization |
| Status | Implemented |
| Source | `test/01_unit/compiler/mir_opt/inlining_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Simple Function Inlining

#### inline identity function

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(identity(42) == 42)
```

</details>

#### inline add_one function

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(add_one(41) == 42)
```

</details>

#### inline with zero

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(add_one(0) == 1)
```

</details>

#### inline with negative

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(add_one(-1) == 0)
```

</details>

### Branching Function Inlining

#### inline max - first larger

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(max_val(10, 5) == 10)
```

</details>

#### inline max - second larger

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(max_val(5, 10) == 10)
```

</details>

#### inline max - equal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(max_val(5, 5) == 5)
```

</details>

#### inline min - first smaller

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(min_val(3, 7) == 3)
```

</details>

#### inline min - second smaller

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(min_val(7, 3) == 3)
```

</details>

#### inline abs - positive

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(abs_val(5) == 5)
```

</details>

#### inline abs - negative

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(abs_val(-5) == 5)
```

</details>

#### inline abs - zero

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(abs_val(0) == 0)
```

</details>

### Multi-branch Inlining

#### clamp within range

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(clamp(5, 0, 10) == 5)
```

</details>

#### clamp below minimum

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(clamp(-5, 0, 10) == 0)
```

</details>

#### clamp above maximum

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(clamp(15, 0, 10) == 10)
```

</details>

#### clamp at minimum

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(clamp(0, 0, 10) == 0)
```

</details>

#### clamp at maximum

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(clamp(10, 0, 10) == 10)
```

</details>

### Nested Call Inlining

#### inline nested calls

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(add_one(add_one(40)) == 42)
```

</details>

#### inline max of add_one

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(max_val(add_one(5), add_one(3)) == 6)
```

</details>

#### inline chained operations

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = abs_val(min_val(-3, -5))
check(result == 5)
```

</details>

#### deeply nested inlining

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(add_one(add_one(add_one(add_one(0)))) == 4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
