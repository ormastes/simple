# Numeric Cast Parity Specification

> Confirms that plain numeric casts and interpolation remain valid in the current

<!-- sdn-diagram:id=cast_numeric_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cast_numeric_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cast_numeric_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cast_numeric_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Numeric Cast Parity Specification

Confirms that plain numeric casts and interpolation remain valid in the current

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/cast_numeric_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Confirms that plain numeric casts and interpolation remain valid in the current
runtime, so dashboard assistant failures can be classified as a narrower
data-shape bug rather than a generic `as i64` language bug.

## Scenarios

### numeric cast parity

#### supports plain float to i64 cast

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42.0
expect(n as i64).to_equal(42)
```

</details>

#### supports plain float cast inside interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42.0
expect("{n as i64}").to_equal("42")
```

</details>

#### supports json-derived number to i64 cast

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_parse("[42]")
val raw = json_array_get(arr, 0)
val n = json_to_number(raw)
expect(n as i64).to_equal(42)
```

</details>

#### supports json-derived number cast inside interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = json_parse("[42]")
val raw = json_array_get(arr, 0)
val n = json_to_number(raw)
expect("{n as i64}").to_equal("42")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
