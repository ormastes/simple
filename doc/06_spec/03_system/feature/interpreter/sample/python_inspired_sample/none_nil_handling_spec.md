# None/Nil Handling (Interpreter)

> Tests nil/none value handling in the interpreter including optional chaining, nil coalescing, and nil checks. Verifies that nil values propagate correctly and that nil-safety features work as expected in interpreted mode.

<!-- sdn-diagram:id=none_nil_handling_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=none_nil_handling_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

none_nil_handling_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=none_nil_handling_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# None/Nil Handling (Interpreter)

Tests nil/none value handling in the interpreter including optional chaining, nil coalescing, and nil checks. Verifies that nil values propagate correctly and that nil-safety features work as expected in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/none_nil_handling_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests nil/none value handling in the interpreter including optional chaining,
nil coalescing, and nil checks. Verifies that nil values propagate correctly
and that nil-safety features work as expected in interpreted mode.

## Scenarios

### None and Nil Handling

#### Option type basics

#### represents present value with Some

1. expect opt is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = Some(42)
expect opt.is_some() == true
```

</details>

#### represents absent value with None

1. expect opt is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = nil
expect opt.is_none() == true
```

</details>

#### unwrapping values

#### unwraps Some value

1. expect opt unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(100)
expect opt.unwrap() == 100
```

</details>

#### provides default for None

1. expect opt unwrap or


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<i64> = nil
expect opt.unwrap_or(0) == 0
```

</details>

#### null coalescing

#### returns value when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some("hello")
val result = opt ?? "default"
expect result == "hello"
```

</details>

#### returns default when None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: Option<text> = nil
val result = opt ?? "default"
expect result == "default"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
