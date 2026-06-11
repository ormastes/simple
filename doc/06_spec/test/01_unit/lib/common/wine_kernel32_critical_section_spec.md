# Wine Kernel32 Critical Section Specification

> 1. wine kernel32 critical section table new

<!-- sdn-diagram:id=wine_kernel32_critical_section_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_critical_section_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_critical_section_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_critical_section_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Critical Section Specification

## Scenarios

### Wine KERNEL32 critical-section bridge

#### executes a bounded initialize, enter, leave, and delete sequence

1. wine kernel32 critical section table new
   - Expected: result.ok is true
   - Expected: result.handle equals `0x300`
   - Expected: result.table.sections.len() equals `0`
   - Expected: result.operations equals `InitializeCriticalSection EnterCriticalSection LeaveCriticalSection DeleteCri... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_critical_section(
    ["InitializeCriticalSection", "EnterCriticalSection", "LeaveCriticalSection", "DeleteCriticalSection"],
    wine_kernel32_critical_section_table_new(),
    "loader-lock"
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x300)
expect(result.table.sections.len()).to_equal(0)
expect(result.operations).to_equal("InitializeCriticalSection EnterCriticalSection LeaveCriticalSection DeleteCriticalSection")
```

</details>

#### keeps critical-section dispatch ordered and bounded

1. wine kernel32 critical section table new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-critical-section-sequence-expected:InitializeCriticalSection`
2. wine kernel32 critical section table new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_critical_section(
    ["EnterCriticalSection", "InitializeCriticalSection", "LeaveCriticalSection", "DeleteCriticalSection"],
    wine_kernel32_critical_section_table_new(),
    "loader-lock"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-critical-section-sequence-expected:InitializeCriticalSection")

val wrong_family = wine_kernel32_execute_critical_section(
    ["InitializeCriticalSection", "EnterCriticalSection", "LeaveCriticalSection", "HeapAlloc"],
    wine_kernel32_critical_section_table_new(),
    "loader-lock"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects unnamed critical sections in the bounded startup path

1. wine kernel32 critical section table new
   - Expected: result.ok is false
   - Expected: result.error equals `InitializeCriticalSection:invalid-name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_critical_section(
    ["InitializeCriticalSection", "EnterCriticalSection", "LeaveCriticalSection", "DeleteCriticalSection"],
    wine_kernel32_critical_section_table_new(),
    ""
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("InitializeCriticalSection:invalid-name")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_critical_section_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 critical-section bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
