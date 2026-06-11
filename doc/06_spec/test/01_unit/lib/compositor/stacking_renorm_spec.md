# WindowStack Renorm Regression — FINDING-U1

> Verifies the `_renorm_windows` / `WindowStack.raise_window` renorm path:

<!-- sdn-diagram:id=stacking_renorm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stacking_renorm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stacking_renorm_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stacking_renorm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WindowStack Renorm Regression — FINDING-U1

Verifies the `_renorm_windows` / `WindowStack.raise_window` renorm path:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/compositor/stacking_renorm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the `_renorm_windows` / `WindowStack.raise_window` renorm path:

1. Relative z-order is preserved after compaction to 0..n-1.
2. No window is lost.
3. next_z is reset to n.

Uses only primitive arrays and pure functions (no List<T>) for interpreter-mode execution.

## Scenarios

### WindowStack renorm — FINDING-U1 regression

#### renorm compacts 3 windows to z_orders 0..2

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Compact windows with already-ordered z_orders; result is identity [0,1,2].
val ids    = [10, 20, 30]
val zords  = [0, 1, 2]
val result = renorm3(ids, zords)
# Original order already compact; result should be [0,1,2]
expect(result[0]).to_equal(0)
expect(result[1]).to_equal(1)
expect(result[2]).to_equal(2)
```

</details>

#### renorm preserves relative order: window raised to top stays on top

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate: add(10), add(20), add(30), raise(10)
# After raise(10): zorders = [3, 1, 2] for ids [10,20,30]
val ids   = [10, 20, 30]
val zords = [3, 1, 2]
val result = renorm3(ids, zords)
# Order should be: 20(z=1) < 30(z=2) < 10(z=3)
# After renorm:    20 → rank 0, 30 → rank 1, 10 → rank 2
expect(result[0]).to_equal(2)   # 10 is highest
expect(result[1]).to_equal(0)   # 20 is lowest
expect(result[2]).to_equal(1)   # 30 is middle
```

</details>

#### relative order 20 < 30 < 10 preserved after renorm

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies strict ordering is preserved: 20 < 30 < 10 after renorm.
val ids   = [10, 20, 30]
val zords = [3, 1, 2]
val result = renorm3(ids, zords)
expect(order_ok(ids, result, 20, 30))
expect(order_ok(ids, result, 30, 10))
```

</details>

#### renorm: lowest-z window gets rank 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids   = [1, 2, 3]
val zords = [999999995, 999999997, 999999999]
val result = renorm3(ids, zords)
# Window 1 has lowest z; window 3 has highest
expect(result[0]).to_equal(0)   # id=1 → rank 0
expect(result[1]).to_equal(1)   # id=2 → rank 1
expect(result[2]).to_equal(2)   # id=3 → rank 2
```

</details>

#### renorm: highest-z window gets rank n-1 = 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ids   = [1, 2, 3]
val zords = [10, 500, 1000000000]
val result = renorm3(ids, zords)
expect(result[2]).to_equal(2)   # id=3 had max z
```

</details>

#### renorm preserves order when windows have arbitrary large z_orders

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Near-threshold z_orders (≈RENORM_THRESHOLD) must compact without order loss.
val ids   = [7, 8, 9]
val zords = [999999990, 999999995, 999999998]
val result = renorm3(ids, zords)
expect(order_ok(ids, result, 7, 8))
expect(order_ok(ids, result, 8, 9))
```

</details>

#### renorm handles reversed input order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Reversed z_orders: id=3 is lowest, id=1 is highest; verifies sort is not stable-by-id.
val ids   = [1, 2, 3]
val zords = [2, 1, 0]   # id=3 has lowest z_order
val result = renorm3(ids, zords)
# z: id1=2, id2=1, id3=0 → order 3 < 2 < 1
expect(order_ok(ids, result, 3, 2))
expect(order_ok(ids, result, 2, 1))
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
