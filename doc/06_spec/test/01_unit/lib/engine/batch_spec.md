# batch_spec

> Engine Batch — sort_commands_by_z Tests

<!-- sdn-diagram:id=batch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=batch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

batch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=batch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# batch_spec

Engine Batch — sort_commands_by_z Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/batch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Batch — sort_commands_by_z Tests

Tests z-order sorting of render commands: empty, single, multiple, and stability.

## Scenarios

### sort_commands_by_z

#### returns empty list for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commands: [RenderCommand] = []
val sorted = sort_commands_by_z(commands)
expect(sorted.len()).to_equal(0)
```

</details>

#### returns single command unchanged

1. rect: Rect2 new
2. color: EngineColor red
3. z order: ZIndex
   - Expected: sorted.len() equals `1`
   - Expected: z equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.red(),
    z_order: ZIndex(value: 5)
)
val commands: [RenderCommand] = [cmd]
val sorted = sort_commands_by_z(commands)
expect(sorted.len()).to_equal(1)
val z = get_z_order(sorted[0]).value
expect(z).to_equal(5)
```

</details>

#### sorts multiple commands by ascending z_order

1. rect: Rect2 new
2. color: EngineColor red
3. z order: ZIndex
4. rect: Rect2 new
5. color: EngineColor blue
6. z order: ZIndex
7. rect: Rect2 new
8. color: EngineColor green
9. z order: ZIndex
   - Expected: sorted.len() equals `3`
   - Expected: z0 equals `1`
   - Expected: z1 equals `5`
   - Expected: z2 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val high = RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.red(),
    z_order: ZIndex(value: 10)
)
val low = RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.blue(),
    z_order: ZIndex(value: 1)
)
val mid = RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.green(),
    z_order: ZIndex(value: 5)
)
val commands: [RenderCommand] = [high, low, mid]
val sorted = sort_commands_by_z(commands)
expect(sorted.len()).to_equal(3)
val z0 = get_z_order(sorted[0]).value
val z1 = get_z_order(sorted[1]).value
val z2 = get_z_order(sorted[2]).value
expect(z0).to_equal(1)
expect(z1).to_equal(5)
expect(z2).to_equal(10)
```

</details>

#### maintains relative order for same z_order (stable sort)

1. rect: Rect2 new
2. color: EngineColor red
3. z order: ZIndex
4. rect: Rect2 new
5. color: EngineColor blue
6. z order: ZIndex
   - Expected: sorted.len() equals `2`
   - Expected: z0 equals `3`
   - Expected: z1 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Two rects with same z_order but different colors
val first = RenderCommand.DrawRect(
    rect: Rect2.new(1.0, 1.0, 10.0, 10.0),
    color: EngineColor.red(),
    z_order: ZIndex(value: 3)
)
val second = RenderCommand.DrawRect(
    rect: Rect2.new(2.0, 2.0, 20.0, 20.0),
    color: EngineColor.blue(),
    z_order: ZIndex(value: 3)
)
val commands: [RenderCommand] = [first, second]
val sorted = sort_commands_by_z(commands)
expect(sorted.len()).to_equal(2)
# Both should still have z_order 3
val z0 = get_z_order(sorted[0]).value
val z1 = get_z_order(sorted[1]).value
expect(z0).to_equal(3)
expect(z1).to_equal(3)
```

</details>

#### places Clear commands first (z_order -1)

1. rect: Rect2 new
2. color: EngineColor red
3. z order: ZIndex
   - Expected: z0 equals `-1`
   - Expected: z1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val draw = RenderCommand.DrawRect(
    rect: Rect2.new(0.0, 0.0, 10.0, 10.0),
    color: EngineColor.red(),
    z_order: ZIndex(value: 0)
)
val clear = RenderCommand.Clear(color: EngineColor.black())
val commands: [RenderCommand] = [draw, clear]
val sorted = sort_commands_by_z(commands)
val z0 = get_z_order(sorted[0]).value
val z1 = get_z_order(sorted[1]).value
expect(z0).to_equal(-1)
expect(z1).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
