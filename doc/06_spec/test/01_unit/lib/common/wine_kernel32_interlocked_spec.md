# Wine Kernel32 Interlocked Specification

> 1. wine kernel32 interlocked cell new

<!-- sdn-diagram:id=wine_kernel32_interlocked_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_interlocked_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_interlocked_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_interlocked_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Interlocked Specification

## Scenarios

### Wine KERNEL32 interlocked bridge

#### executes a bounded interlocked operation sequence

1. wine kernel32 interlocked cell new
   - Expected: result.ok is true
   - Expected: result.previous equals `41`
   - Expected: result.current equals `43`
   - Expected: result.cell.value equals `43`
   - Expected: result.operations equals `InterlockedIncrement InterlockedDecrement InterlockedExchange InterlockedComp... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_interlocked(
    ["InterlockedIncrement", "InterlockedDecrement", "InterlockedExchange", "InterlockedCompareExchange", "InterlockedExchangeAdd"],
    wine_kernel32_interlocked_cell_new(10),
    40,
    2
)

expect(result.ok).to_equal(true)
expect(result.previous).to_equal(41)
expect(result.current).to_equal(43)
expect(result.cell.value).to_equal(43)
expect(result.operations).to_equal("InterlockedIncrement InterlockedDecrement InterlockedExchange InterlockedCompareExchange InterlockedExchangeAdd")
```

</details>

#### exposes direct interlocked helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val incremented = wine_kernel32_interlocked_increment(wine_kernel32_interlocked_cell_new(1))
val decremented = wine_kernel32_interlocked_decrement(incremented.cell)
val exchanged = wine_kernel32_interlocked_exchange(decremented.cell, 9)
val compared = wine_kernel32_interlocked_compare_exchange(exchanged.cell, 11, 9)
val added = wine_kernel32_interlocked_exchange_add(compared.cell, 4)

expect(incremented.current).to_equal(2)
expect(decremented.current).to_equal(1)
expect(exchanged.previous).to_equal(1)
expect(compared.current).to_equal(11)
expect(added.previous).to_equal(11)
expect(added.current).to_equal(15)
```

</details>

#### preserves compare-exchange value when the comparand does not match

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_interlocked_compare_exchange(wine_kernel32_interlocked_cell_new(7), 12, 6)

expect(result.previous).to_equal(7)
expect(result.current).to_equal(7)
expect(result.cell.value).to_equal(7)
```

</details>

#### keeps interlocked dispatch ordered and bounded

1. wine kernel32 interlocked cell new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-interlocked-sequence-expected:InterlockedIncrement`
2. wine kernel32 interlocked cell new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_interlocked(
    ["InterlockedExchange", "InterlockedIncrement", "InterlockedDecrement", "InterlockedCompareExchange", "InterlockedExchangeAdd"],
    wine_kernel32_interlocked_cell_new(10),
    40,
    2
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-interlocked-sequence-expected:InterlockedIncrement")

val wrong_family = wine_kernel32_execute_interlocked(
    ["InterlockedIncrement", "InterlockedDecrement", "InterlockedExchange", "InterlockedCompareExchange", "HeapAlloc"],
    wine_kernel32_interlocked_cell_new(10),
    40,
    2
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_interlocked_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 interlocked bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
