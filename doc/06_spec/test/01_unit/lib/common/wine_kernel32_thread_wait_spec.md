# Wine Kernel32 Thread Wait Specification

> 1. wine nt thread table new

<!-- sdn-diagram:id=wine_kernel32_thread_wait_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_thread_wait_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_thread_wait_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_thread_wait_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Thread Wait Specification

## Scenarios

### Wine KERNEL32 thread/wait bridge

#### executes a bounded CreateThread, WaitForSingleObject, and GetLastError sequence

1. wine nt thread table new
   - Expected: result.ok is true
   - Expected: result.handle equals `0x80`
   - Expected: result.wait_status equals `WAIT_OBJECT_0`
   - Expected: result.exit_code equals `7`
   - Expected: result.last_error equals `OK`
   - Expected: result.operations equals `CreateThread WaitForSingleObject GetLastError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "GetLastError"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "main",
    7,
    1000
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x80)
expect(result.wait_status).to_equal("WAIT_OBJECT_0")
expect(result.exit_code).to_equal(7)
expect(result.last_error).to_equal("OK")
expect(result.operations).to_equal("CreateThread WaitForSingleObject GetLastError")
```

</details>

#### keeps thread/wait dispatch ordered and bounded

1. wine nt thread table new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-thread-wait-sequence-expected:CreateThread`
2. wine nt thread table new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapFree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_thread_wait(
    ["WaitForSingleObject", "CreateThread", "GetLastError"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "main",
    0,
    1000
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-thread-wait-sequence-expected:CreateThread")

val wrong_family = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "HeapFree"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "main",
    0,
    1000
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapFree")
```

</details>

#### propagates thread readiness and CreateThread errors

1. wine nt thread table new
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `CreateThread:missing-api-thread-detach`
2. wine nt thread table new
   - Expected: invalid.ok is false
   - Expected: invalid.error equals `CreateThread:invalid-entrypoint`
   - Expected: invalid.last_error equals `ERROR_INVALID_PARAMETER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocked = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "GetLastError"],
    wine_nt_thread_table_new("thread-create thread-join"),
    "main",
    0,
    1000
)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("CreateThread:missing-api-thread-detach")

val invalid = wine_kernel32_execute_thread_wait(
    ["CreateThread", "WaitForSingleObject", "GetLastError"],
    wine_nt_thread_table_new(_all_thread_apis()),
    "",
    0,
    1000
)
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("CreateThread:invalid-entrypoint")
expect(invalid.last_error).to_equal("ERROR_INVALID_PARAMETER")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_thread_wait_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 thread/wait bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
