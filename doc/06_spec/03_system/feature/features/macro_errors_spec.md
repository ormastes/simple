# macro_errors_spec

> Macro edge cases and error handling specification.

<!-- sdn-diagram:id=macro_errors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_errors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_errors_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_errors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_errors_spec

Macro edge cases and error handling specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_errors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Macro edge cases and error handling specification.

Tests macro system edge cases including empty bodies, deep nesting,
many parameters, variable shadowing, and early return handling.

## Scenarios

### Macro Edge Cases

### Edge case behavior

#### handles empty macro bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = err_empty!()
expect(x).to_equal(0)
```

</details>

#### handles macro with only const-eval

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = err_const_only!(6, 7)
expect(x).to_equal(42)
```

</details>

#### handles macros with many parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = err_many_params!(10, 11, 12, 9)
expect(x).to_equal(42)
```

</details>

#### handles nested scopes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = err_nested_scopes!()
expect(result).to_equal(30)
```

</details>

#### handles nested blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = err_nested_blocks!()
expect(result).to_equal(6)
```

</details>

### Macro hygiene edge cases

#### handles shadowing within macro

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = err_shadow_test!()
# ((10 + 5) * 2) = 30
expect(result).to_equal(30)
```

</details>

#### handles multiple variable bindings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = err_multi_bind!()
expect(result).to_equal(10)
```

</details>

#### handles function parameters hygiene

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = err_func_test!()
expect(result).to_equal(10)
```

</details>

#### handles early return

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = err_early_return!(false)
expect(result).to_equal(42)

val result2 = err_early_return!(true)
expect(result2).to_equal(100)
```

</details>

### Macro Parameter Handling

#### does not capture parameters via hygiene

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
let x = 5
val result = err_use_param!(32)
# 5 + 42 = 47
expect(x + result).to_equal(47)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
