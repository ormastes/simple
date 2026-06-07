# arena_as_blob_backend_spec

> Arena Core Conformance Specification

<!-- sdn-diagram:id=arena_as_blob_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arena_as_blob_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arena_as_blob_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arena_as_blob_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# arena_as_blob_backend_spec

Arena Core Conformance Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/arena_as_blob_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Arena Core Conformance Specification

Verifies the live NVFS arena core helpers still provide the blob-backend verbs
used by the hosted DBFS/NVFS path:
  - create / append / read / seal / discard / clone_range / preferred_granule

## Scenarios

### Arena core conformance

#### general-mutable arena passes full conformance suite

1. run conformance suite


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
run_conformance_suite(0)
```

</details>

#### clone_range copies data correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = arena_create_impl(0, 4096)
val payload: [u8] = [0xAB, 0xCD]
expect(arena_append_impl(src, payload, 0)).to_equal(2)
val dst = arena_create_impl(0, 4096)
expect(arena_clone_range_impl(src, 0, dst, 0, 2)).to_equal(2)
val out = arena_readv_impl(dst, 0, 2)
expect(out[0]).to_equal(0xAB)
expect(out[1]).to_equal(0xCD)
```

</details>

#### preferred_granule is at least 512

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = arena_create_impl(0, 4096)
expect(arena_preferred_granule_impl(h) >= 512).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
