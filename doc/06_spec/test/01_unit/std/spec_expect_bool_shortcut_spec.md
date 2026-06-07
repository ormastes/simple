# spec_expect_bool_shortcut_spec

> Verifies concise boolean assertions:

<!-- sdn-diagram:id=spec_expect_bool_shortcut_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spec_expect_bool_shortcut_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spec_expect_bool_shortcut_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spec_expect_bool_shortcut_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_expect_bool_shortcut_spec

Verifies concise boolean assertions:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/spec_expect_bool_shortcut_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies concise boolean assertions:
    `expect(condition)` asserts true and `expect_not(condition)` asserts false.
    Matcher chains such as `expect(value).to_equal(value)` remain supported for
    non-boolean equality.

## Scenarios

### std.spec boolean expectation shortcuts

#### accepts bare expect for true boolean expressions

1. check
2. check msg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(true)
val condition = 2 + 2 == 4
expect(condition)
check(condition)
check_msg(condition, "condition should be true")
```

</details>

#### accepts expect_not for false boolean expressions

1. expect not
2. expect not
3. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_not(false)
val condition = "abc".contains("z")
expect_not(condition)
expect_not(2 + 2 == 5)
```

</details>

#### keeps matcher equality for non-boolean values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(42).to_equal(42)
expect("simple").to_equal("simple")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
