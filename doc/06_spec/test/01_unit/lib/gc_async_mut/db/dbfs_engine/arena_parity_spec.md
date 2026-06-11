# Arena Parity Specification

> <details>

<!-- sdn-diagram:id=arena_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arena_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arena_parity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arena_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arena Parity Specification

## Scenarios

### gc_async_mut DBFS arena facade

#### re-exports DBFS arena operations from the canonical backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aid = arena_create_impl(0, 128)
expect(aid > 0).to_equal(true)
val data: [u8] = [0x44, 0x42, 0x46, 0x53]
expect(arena_append_impl(aid, data, 0)).to_equal(4)
expect(arena_total_bytes_impl(aid)).to_equal(4)
val rd = arena_readv_impl(aid, 0, 4)
expect(rd.len() as i64).to_equal(4)
expect(rd[0]).to_equal(0x44)
expect(rd[3]).to_equal(0x53)
expect(arena_seal_impl(aid, 1)).to_equal(true)
expect(arena_is_sealed_impl(aid)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/db/dbfs_engine/arena_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut DBFS arena facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
