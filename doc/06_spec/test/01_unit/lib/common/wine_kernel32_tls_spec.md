# Wine Kernel32 Tls Specification

> 1. wine kernel32 tls table new

<!-- sdn-diagram:id=wine_kernel32_tls_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_kernel32_tls_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_kernel32_tls_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_kernel32_tls_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Kernel32 Tls Specification

## Scenarios

### Wine KERNEL32 TLS bridge

#### executes a bounded allocate, set, get, and free TLS sequence

1. wine kernel32 tls table new
   - Expected: result.ok is true
   - Expected: result.index equals `0`
   - Expected: result.value equals `thread-local-startup-state`
   - Expected: result.table.slots.len() equals `0`
   - Expected: result.operations equals `TlsAlloc TlsSetValue TlsGetValue TlsFree`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_kernel32_execute_tls(
    ["TlsAlloc", "TlsSetValue", "TlsGetValue", "TlsFree"],
    wine_kernel32_tls_table_new(),
    "thread-local-startup-state"
)

expect(result.ok).to_equal(true)
expect(result.index).to_equal(0)
expect(result.value).to_equal("thread-local-startup-state")
expect(result.table.slots.len()).to_equal(0)
expect(result.operations).to_equal("TlsAlloc TlsSetValue TlsGetValue TlsFree")
```

</details>

#### exposes direct TLS slot helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val allocated = wine_kernel32_tls_alloc(wine_kernel32_tls_table_new())
val set_value = wine_kernel32_tls_set_value(allocated.table, allocated.index, "teb-slot")
val got_value = wine_kernel32_tls_get_value(set_value.table, allocated.index)
val freed = wine_kernel32_tls_free(got_value.table, got_value.index)

expect(allocated.ok).to_equal(true)
expect(allocated.index).to_equal(0)
expect(set_value.ok).to_equal(true)
expect(got_value.value).to_equal("teb-slot")
expect(freed.ok).to_equal(true)
expect(freed.table.slots.len()).to_equal(0)
```

</details>

#### keeps TLS dispatch ordered and bounded

1. wine kernel32 tls table new
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `kernel32-tls-sequence-expected:TlsAlloc`
2. wine kernel32 tls table new
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:HeapAlloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_kernel32_execute_tls(
    ["TlsSetValue", "TlsAlloc", "TlsGetValue", "TlsFree"],
    wine_kernel32_tls_table_new(),
    "thread-local-startup-state"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("kernel32-tls-sequence-expected:TlsAlloc")

val wrong_family = wine_kernel32_execute_tls(
    ["TlsAlloc", "TlsSetValue", "TlsGetValue", "HeapAlloc"],
    wine_kernel32_tls_table_new(),
    "thread-local-startup-state"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:HeapAlloc")
```

</details>

#### rejects invalid TLS indexes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_kernel32_tls_table_new()
expect(wine_kernel32_tls_set_value(table, 0, "missing").error).to_equal("TlsSetValue:invalid-tls-index")
expect(wine_kernel32_tls_get_value(table, 0).error).to_equal("TlsGetValue:invalid-tls-index")
expect(wine_kernel32_tls_free(table, 0).error).to_equal("TlsFree:invalid-tls-index")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_kernel32_tls_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine KERNEL32 TLS bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
