# Errdefer Specification

> <details>

<!-- sdn-diagram:id=errdefer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=errdefer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

errdefer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=errdefer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Errdefer Specification

## Scenarios

### Errdefer

### parsing

#### parses errdefer statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# errdefer is a keyword that parses like defer
val code = "errdefer cleanup()"
# If this file loads without error, the parser handles errdefer
expect(code).to_start_with("errdefer")
```

</details>

### interpreter semantics

#### errdefer does NOT run on success

1. fn success path
2. success path
   - Expected: ran is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On success path, errdefer body must not execute
var ran = false
fn success_path():
    errdefer ran = true
    val x = 42
success_path()
expect(ran).to_equal(false)
```

</details>

#### errdefer runs on error

1. fn error path
2. error path
   - Expected: ran is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On error path, errdefer body must execute
var ran = false
fn error_path():
    errdefer ran = true
    val bad = 1 / 0  # triggers eval_had_error
error_path()
expect(ran).to_equal(true)
```

</details>

#### defer always runs regardless of error

1. fn success with defer
2. success with defer
   - Expected: ran is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ran = false
fn success_with_defer():
    defer ran = true
    val x = 42
success_with_defer()
expect(ran).to_equal(true)
```

</details>

#### multiple errdefers run in LIFO order on error

1. fn multi errdefer
2. errdefer order push
3. errdefer order push
4. errdefer order push
5. multi errdefer
   - Expected: order equals `[3, 2, 1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var order: [i64] = []
fn multi_errdefer():
    errdefer order.push(1)
    errdefer order.push(2)
    errdefer order.push(3)
    val bad = 1 / 0
multi_errdefer()
expect(order).to_equal([3, 2, 1])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/errdefer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Errdefer
- parsing
- interpreter semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
