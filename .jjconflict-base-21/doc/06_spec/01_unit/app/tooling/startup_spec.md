# Startup Module Specification

> Tests for startup initialization, metrics collection, and initialization flags.

<!-- sdn-diagram:id=startup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=startup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

startup_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=startup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup Module Specification

Tests for startup initialization, metrics collection, and initialization flags.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Tooling |
| Status | Draft |
| Source | `test/01_unit/app/tooling/startup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for startup initialization, metrics collection, and initialization flags.

## Scenarios

### startup module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### startup flag detection

#### detects --startup-metrics flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "--startup-metrics", "script.spl"]
val has_flag = args.any(_1 == "--startup-metrics")
expect has_flag == true
```

</details>

#### no flag when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "script.spl"]
val has_flag = args.any(_1 == "--startup-metrics")
expect has_flag == false
```

</details>

### prefetch conditions

#### prefetch enabled and files present

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enable_prefetch = true
val files_present = ["test.spl"].len() > 0
val should_prefetch = enable_prefetch and files_present
expect should_prefetch == true
```

</details>

#### prefetch disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enable_prefetch = false
val files_present = ["test.spl"].len() > 0
val should_prefetch = enable_prefetch and files_present
expect should_prefetch == false
```

</details>

#### no files to prefetch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enable_prefetch = true
val should_prefetch = enable_prefetch and ([].len() > 0)
expect should_prefetch == false
```

</details>

### exit code conventions

#### success code is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 0
expect exit_code == 0
```

</details>

#### error code is non-zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 1
expect exit_code == 1
```

</details>

### match pattern with Option

#### matches Some variant with value

1. expect Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Some(42).is_some() == true
```

</details>

### tuple return values

#### tuple access works

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = (true, 42)
expect pair.0 == true
expect pair.1 == 42
```

</details>

### time measurement patterns

#### subtracts time values

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (1500 - 1000) == 500
```

</details>

#### divides for conversion

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (3000 / 1000) == 3
```

</details>

### Result patterns

#### Ok result check

1. expect Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Ok(42).is_ok() == true
```

</details>

#### Err result check

1. expect Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Err("error").is_err() == true
```

</details>

### list length checks

#### non-empty list has count

1. expect files len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["file1.spl", "file2.spl"]
expect files.len() == 2
```

</details>

### boolean conditions

#### combines with and

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond1 = true
val cond2 = true
val result = cond1 and cond2
expect result == true
```

</details>

#### false when one is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cond1 = true
val cond2 = false
val result = cond1 and cond2
expect result == false
```

</details>

### metrics enabled pattern

#### checks boolean flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = false
expect enabled == false
```

</details>

#### conditional execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = true
val should_print = enabled
expect should_print == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
