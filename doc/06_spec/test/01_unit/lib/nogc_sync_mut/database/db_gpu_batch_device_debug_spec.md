# Db Gpu Batch Device Debug Specification

> <details>

<!-- sdn-diagram:id=db_gpu_batch_device_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=db_gpu_batch_device_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

db_gpu_batch_device_debug_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=db_gpu_batch_device_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Db Gpu Batch Device Debug Specification

## Scenarios

### debug db gpu batch device

#### native used

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(db_gpu_batch_offload_used_gpu(native_execution().execution)).to_be(true)
```

</details>

#### native rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_execution().execution.result_row_ids.len()).to_equal(3)
```

</details>

#### native cpu auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_execution().execution.cpu_authoritative).to_be(true)
```

</details>

#### native claim

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_execution().device_result.production_device_claim).to_be(true)
```

</details>

#### native target

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_execution().device_result.submission.dispatch_target).to_equal("gpu_db_columnar_scan_batch")
```

</details>

#### native time

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_execution().device_result.evidence.device_time_us).to_equal(43)
```

</details>

#### mock used

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(db_gpu_batch_offload_used_gpu(mock_execution().execution)).to_be(false)
```

</details>

#### mock row

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_execution().execution.result_row_ids[0]).to_equal(4)
```

</details>

#### mock auth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_execution().execution.cpu_authoritative).to_be(true)
```

</details>

#### mock claim

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_execution().device_result.production_device_claim).to_be(false)
```

</details>

#### mock target

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_execution().device_result.submission.dispatch_target).to_equal("cpu_fallback")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/database/db_gpu_batch_device_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- debug db gpu batch device

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
