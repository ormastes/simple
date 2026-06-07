# Wine Ntdll Sync Event Specification

> 1. wine ntdll event table new

<!-- sdn-diagram:id=wine_ntdll_sync_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_ntdll_sync_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_ntdll_sync_event_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_ntdll_sync_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Sync Event Specification

## Scenarios

### Wine NTDLL sync event bridge

#### executes a bounded NtCreateEvent, NtSetEvent, NtWaitForSingleObject, and NtResetEvent sequence

1. wine ntdll event table new
   - Expected: result.ok is true
   - Expected: result.handle equals `0x300`
   - Expected: result.wait_status equals `STATUS_WAIT_0`
   - Expected: result.table.events[0].signaled is false
   - Expected: result.operations equals `NtCreateEvent NtSetEvent NtWaitForSingleObject NtResetEvent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_event_sync(
    ["NtCreateEvent", "NtSetEvent", "NtWaitForSingleObject", "NtResetEvent"],
    wine_ntdll_event_table_new(),
    "startup-ready",
    true,
    false,
    1000
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x300)
expect(result.wait_status).to_equal("STATUS_WAIT_0")
expect(result.table.events[0].signaled).to_equal(false)
expect(result.operations).to_equal("NtCreateEvent NtSetEvent NtWaitForSingleObject NtResetEvent")
```

</details>

#### keeps NTDLL event dispatch ordered and bounded

1. wine ntdll event table new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `ntdll-sync-event-sequence-expected:NtCreateEvent`
2. wine ntdll event table new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_ntdll_execute_event_sync(
    ["NtSetEvent", "NtCreateEvent", "NtWaitForSingleObject", "NtResetEvent"],
    wine_ntdll_event_table_new(),
    "startup-ready",
    true,
    false,
    1000
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("ntdll-sync-event-sequence-expected:NtCreateEvent")

val wrong_family = wine_ntdll_execute_event_sync(
    ["NtCreateEvent", "NtSetEvent", "NtWaitForSingleObject", "NtCreateFile"],
    wine_ntdll_event_table_new(),
    "startup-ready",
    true,
    false,
    1000
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### rejects unnamed NTDLL events in the bounded startup path

1. wine ntdll event table new
   - Expected: result.ok is false
   - Expected: result.error equals `NtCreateEvent:invalid-name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_event_sync(
    ["NtCreateEvent", "NtSetEvent", "NtWaitForSingleObject", "NtResetEvent"],
    wine_ntdll_event_table_new(),
    "",
    true,
    false,
    1000
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("NtCreateEvent:invalid-name")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_sync_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NTDLL sync event bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
