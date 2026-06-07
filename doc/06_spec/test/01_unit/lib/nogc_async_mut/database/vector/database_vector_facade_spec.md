# Database Vector Facade Specification

> 1. VectorDbError EntryNotFound

<!-- sdn-diagram:id=database_vector_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_vector_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_vector_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_vector_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Vector Facade Specification

## Scenarios

### nogc_async_mut database vector facade

#### re-exports vector types, distance, and codec helpers

1. VectorDbError EntryNotFound
   - Expected: id equals `missing`
2. fail
   - Expected: dot_product([1.0, 2.0], [3.0, 4.0]) equals `11.0`
   - Expected: l2_norm([3.0, 4.0]) equals `5.0`
   - Expected: cosine_similarity([1.0, 0.0], [1.0, 0.0]) equals `1.0`
   - Expected: cosine_distance([1.0, 0.0], [1.0, 0.0]) equals `0.0`
   - Expected: euclidean_distance([0.0, 0.0], [3.0, 4.0]) equals `5.0`
   - Expected: compute_distance([1.0], [1.0], DistanceMetric.Cosine) equals `0.0`
   - Expected: normalize_vector([3.0, 4.0]).len() equals `2`
   - Expected: decoded.len() equals `2`
3. fail
   - Expected: decode_metadata(meta)["a"] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_vector_config(3)
expect(cfg.dimensions).to_equal(3)
expect(cfg.metric).to_equal(DistanceMetric.Cosine)
val entry = VectorEntry(id: "a", vector: [1.0, 0.0], metadata: {"kind": "unit"}, norm: 1.0)
expect(entry.id).to_equal("a")
val result = SearchResult(id: "a", distance: 0.0, metadata: {})
expect(result.distance).to_equal(0.0)
val err = VectorDbError.EntryNotFound(id: "missing")
match err:
    VectorDbError.EntryNotFound(id):
        expect(id).to_equal("missing")
    _:
        fail("VectorDbError.EntryNotFound did not match")

expect(dot_product([1.0, 2.0], [3.0, 4.0])).to_equal(11.0)
expect(l2_norm([3.0, 4.0])).to_equal(5.0)
expect(cosine_similarity([1.0, 0.0], [1.0, 0.0])).to_equal(1.0)
expect(cosine_distance([1.0, 0.0], [1.0, 0.0])).to_equal(0.0)
expect(euclidean_distance([0.0, 0.0], [3.0, 4.0])).to_equal(5.0)
expect(compute_distance([1.0], [1.0], DistanceMetric.Cosine)).to_equal(0.0)
expect(normalize_vector([3.0, 4.0]).len()).to_equal(2)

val encoded = encode_vector([1.0, 2.0])
expect(encoded).to_contain("1")
if val Some(decoded) = decode_vector(encoded):
    expect(decoded.len()).to_equal(2)
else:
    fail("decode_vector returned nil for encoded vector")
val meta = encode_metadata({"a": "b"})
expect(meta).to_contain("a")
expect(decode_metadata(meta)["a"]).to_equal("b")
```

</details>

#### re-exports index and store surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = BruteForceIndex.create(2)
expect(idx.size()).to_equal(0)
val maybe_db: VectorDatabase? = nil
expect(maybe_db).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut database vector facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
