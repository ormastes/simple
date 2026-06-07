# Wine Kernel32 Fls Specification

> 1. wine kernel32 fls table new

<!-- sdn-diagram:id=wine_kernel32_fls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_fls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_fls_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_fls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Fls Specification

## Scenarios

### Wine KERNEL32 FLS bridge

#### executes a bounded allocate, set, get, and free FLS sequence

1. wine kernel32 fls table new
   - Expected: result.ok is true
   - Expected: result.index equals `0`
   - Expected: result.value equals `fiber-local-startup-state`
   - Expected: result.callback equals `fls-destructor`
   - Expected: result.table.slots.len() equals `0`
   - Expected: result.table.callback_log equals `fls-destructor:fiber-local-startup-state`
   - Expected: result.operations equals `FlsAlloc FlsSetValue FlsGetValue FlsFree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_fls(
    ["FlsAlloc", "FlsSetValue", "FlsGetValue", "FlsFree"],
    wine_kernel32_fls_table_new(),
    "fiber-local-startup-state",
    "fls-destructor"
)

expect(result.ok).to_equal(true)
expect(result.index).to_equal(0)
expect(result.value).to_equal("fiber-local-startup-state")
expect(result.callback).to_equal("fls-destructor")
expect(result.table.slots.len()).to_equal(0)
expect(result.table.callback_log).to_equal("fls-destructor:fiber-local-startup-state")
expect(result.operations).to_equal("FlsAlloc FlsSetValue FlsGetValue FlsFree")
```

</details>

#### exposes direct FLS slot helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allocated = wine_kernel32_fls_alloc(wine_kernel32_fls_table_new(), "fls-destructor")
val set_value = wine_kernel32_fls_set_value(allocated.table, allocated.index, "teb-fiber-slot")
val got_value = wine_kernel32_fls_get_value(set_value.table, allocated.index)
val freed = wine_kernel32_fls_free(got_value.table, got_value.index)

expect(allocated.ok).to_equal(true)
expect(allocated.index).to_equal(0)
expect(got_value.value).to_equal("teb-fiber-slot")
expect(got_value.callback).to_equal("fls-destructor")
expect(freed.ok).to_equal(true)
expect(freed.table.slots.len()).to_equal(0)
expect(freed.table.callback_log).to_equal("fls-destructor:teb-fiber-slot")
```

</details>

#### keeps FLS dispatch ordered and bounded

1. wine kernel32 fls table new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-fls-sequence-expected:FlsAlloc`
2. wine kernel32 fls table new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_fls(
    ["FlsSetValue", "FlsAlloc", "FlsGetValue", "FlsFree"],
    wine_kernel32_fls_table_new(),
    "fiber-local-startup-state",
    "fls-destructor"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-fls-sequence-expected:FlsAlloc")

val wrong_family = wine_kernel32_execute_fls(
    ["FlsAlloc", "FlsSetValue", "FlsGetValue", "HeapAlloc"],
    wine_kernel32_fls_table_new(),
    "fiber-local-startup-state",
    "fls-destructor"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid FLS indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_kernel32_fls_table_new()
expect(wine_kernel32_fls_set_value(table, 0, "missing").error).to_equal("FlsSetValue:invalid-fls-index")
expect(wine_kernel32_fls_get_value(table, 0).error).to_equal("FlsGetValue:invalid-fls-index")
expect(wine_kernel32_fls_free(table, 0).error).to_equal("FlsFree:invalid-fls-index")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_fls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 FLS bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
