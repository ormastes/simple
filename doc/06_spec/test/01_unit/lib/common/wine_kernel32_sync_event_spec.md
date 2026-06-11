# Wine Kernel32 Sync Event Specification

> 1. wine kernel32 event table new

<!-- sdn-diagram:id=wine_kernel32_sync_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_sync_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_sync_event_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_sync_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Sync Event Specification

## Scenarios

### Wine KERNEL32 sync event bridge

#### executes a bounded event create, signal, wait, and reset sequence

1. wine kernel32 event table new
   - Expected: result.ok is true
   - Expected: result.handle equals `0x200`
   - Expected: result.wait_status equals `WAIT_OBJECT_0`
   - Expected: result.table.events[0].signaled is false
   - Expected: result.operations equals `CreateEventW SetEvent WaitForSingleObject ResetEvent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_event_sync(
    ["CreateEventW", "SetEvent", "WaitForSingleObject", "ResetEvent"],
    wine_kernel32_event_table_new(),
    "startup-ready",
    true,
    false,
    1000
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x200)
expect(result.wait_status).to_equal("WAIT_OBJECT_0")
expect(result.table.events[0].signaled).to_equal(false)
expect(result.operations).to_equal("CreateEventW SetEvent WaitForSingleObject ResetEvent")
```

</details>

#### keeps event dispatch ordered and bounded

1. wine kernel32 event table new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-sync-event-sequence-expected:CreateEventW`
2. wine kernel32 event table new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_event_sync(
    ["SetEvent", "CreateEventW", "WaitForSingleObject", "ResetEvent"],
    wine_kernel32_event_table_new(),
    "startup-ready",
    true,
    false,
    1000
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-sync-event-sequence-expected:CreateEventW")

val wrong_family = wine_kernel32_execute_event_sync(
    ["CreateEventW", "SetEvent", "WaitForSingleObject", "HeapAlloc"],
    wine_kernel32_event_table_new(),
    "startup-ready",
    true,
    false,
    1000
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects unnamed events in the bounded startup path

1. wine kernel32 event table new
   - Expected: result.ok is false
   - Expected: result.error equals `CreateEventW:invalid-name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_event_sync(
    ["CreateEventW", "SetEvent", "WaitForSingleObject", "ResetEvent"],
    wine_kernel32_event_table_new(),
    "",
    true,
    false,
    1000
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("CreateEventW:invalid-name")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_sync_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 sync event bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
