# Wine Nt Thread Wait Specification

> <details>

<!-- sdn-diagram:id=wine_nt_thread_wait_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_thread_wait_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_thread_wait_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_thread_wait_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Thread Wait Specification

## Scenarios

### Wine NT thread/wait bridge

#### lists the modeled CreateThread, WaitForSingleObject, and GetLastError calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls = wine_nt_thread_wait_required_calls()
expect(calls.len()).to_equal(3)
expect(calls[0]).to_equal("CreateThread")
```

</details>

#### blocks thread table readiness until thread prerequisites pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = wine_nt_thread_table_new("thread-create thread-join")
expect(table.ready).to_equal(false)
expect(table.state).to_equal("missing-api-thread-detach")
expect(wine_nt_get_last_error(table)).to_equal("missing-api-thread-detach")
```

</details>

#### creates a modeled thread handle and waits for completion

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_nt_create_thread(wine_nt_thread_table_new(_all_thread_apis()), "main", 7)
expect(created.ok).to_equal(true)
expect(created.handle).to_equal(0x80)
val waited = wine_nt_wait_for_single_object(created.table, created.handle, 1000)
expect(waited.ok).to_equal(true)
expect(waited.wait_status).to_equal("WAIT_OBJECT_0")
expect(waited.exit_code).to_equal(7)
expect(wine_nt_get_last_error(waited.table)).to_equal("OK")
```

</details>

#### rejects invalid entrypoints and exposes last error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_nt_create_thread(wine_nt_thread_table_new(_all_thread_apis()), "", 0)
expect(created.ok).to_equal(false)
expect(created.state).to_equal("invalid-entrypoint")
expect(wine_nt_get_last_error(created.table)).to_equal("ERROR_INVALID_PARAMETER")
```

</details>

#### rejects invalid wait handles and exposes last error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val waited = wine_nt_wait_for_single_object(wine_nt_thread_table_new(_all_thread_apis()), 0x99, 0)
expect(waited.ok).to_equal(false)
expect(waited.state).to_equal("invalid-handle")
expect(wine_nt_get_last_error(waited.table)).to_equal("ERROR_INVALID_HANDLE")
```

</details>

#### reports timeout for unsignaled modeled handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = wine_nt_create_pending_thread(wine_nt_thread_table_new(_all_thread_apis()), "worker")
expect(created.state).to_equal("created-pending")
val waited = wine_nt_wait_for_single_object(created.table, created.handle, 0)
expect(waited.ok).to_equal(true)
expect(waited.state).to_equal("wait-timeout")
expect(waited.wait_status).to_equal("WAIT_TIMEOUT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_thread_wait_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NT thread/wait bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
