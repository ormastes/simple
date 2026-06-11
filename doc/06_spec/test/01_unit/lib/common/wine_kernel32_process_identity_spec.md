# Wine Kernel32 Process Identity Specification

> 1. wine kernel32 process identity default

<!-- sdn-diagram:id=wine_kernel32_process_identity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_process_identity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_process_identity_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_process_identity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Process Identity Specification

## Scenarios

### Wine KERNEL32 process identity bridge

#### executes bounded process and thread identity calls

1. wine kernel32 process identity default
   - Expected: result.ok is true
   - Expected: result.process_id equals `0x40`
   - Expected: result.thread_id equals `0x80`
   - Expected: result.process_handle equals `-1`
   - Expected: result.thread_handle equals `-2`
   - Expected: result.operations equals `GetCurrentProcessId GetCurrentThreadId GetCurrentProcess GetCurrentThread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_process_identity(
    ["GetCurrentProcessId", "GetCurrentThreadId", "GetCurrentProcess", "GetCurrentThread"],
    wine_kernel32_process_identity_default()
)

expect(result.ok).to_equal(true)
expect(result.process_id).to_equal(0x40)
expect(result.thread_id).to_equal(0x80)
expect(result.process_handle).to_equal(-1)
expect(result.thread_handle).to_equal(-2)
expect(result.operations).to_equal("GetCurrentProcessId GetCurrentThreadId GetCurrentProcess GetCurrentThread")
```

</details>

#### keeps identity dispatch ordered and bounded

1. wine kernel32 process identity default
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-process-identity-sequence-expected:GetCurrentProcessId`
2. wine kernel32 process identity default
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_process_identity(
    ["GetCurrentThreadId", "GetCurrentProcessId", "GetCurrentProcess", "GetCurrentThread"],
    wine_kernel32_process_identity_default()
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-process-identity-sequence-expected:GetCurrentProcessId")

val wrong_family = wine_kernel32_execute_process_identity(
    ["GetCurrentProcessId", "GetCurrentThreadId", "GetCurrentProcess", "HeapAlloc"],
    wine_kernel32_process_identity_default()
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid identity values

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val identity = WineKernel32ProcessIdentity(process_id: 0, thread_id: 0x80, process_handle: -1, thread_handle: -2)
val result = wine_kernel32_execute_process_identity(
    ["GetCurrentProcessId", "GetCurrentThreadId", "GetCurrentProcess", "GetCurrentThread"],
    identity
)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("GetCurrentProcessId:invalid-process-id")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_process_identity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 process identity bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
