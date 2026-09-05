# Database Vector Facade Specification

> Tests covering nogc_async_mut database vector facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Vector Facade Specification

## Scenarios

### nogc_async_mut database vector facade

#### re-exports vector types, distance, and codec helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports vector types, distance, and codec helpers
   - Expected: cfg.dimensions equals `3`
   - Expected: cfg.metric equals `DistanceMetric.Cosine`
   - Expected: entry.id equals `a`
   - Expected: result.distance equals `0.0`
   - Expected: id equals `missing`
   - Expected: dot_product([1.0, 2.0], [3.0, 4.0]) equals `11.0`
   - Expected: l2_norm([3.0, 4.0]) equals `5.0`
   - Expected: cosine_similarity([1.0, 0.0], [1.0, 0.0]) equals `1.0`
   - Expected: cosine_distance([1.0, 0.0], [1.0, 0.0]) equals `0.0`
   - Expected: euclidean_distance([0.0, 0.0], [3.0, 4.0]) equals `5.0`
   - Expected: compute_distance([1.0], [1.0], DistanceMetric.Cosine) equals `0.0`
   - Expected: normalize_vector([3.0, 4.0]).len() equals `2`
   - Expected: decoded.len() equals `2`
   - Expected: decode_metadata(meta)["a"] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports vector types, distance, and codec helpers")
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

- re-exports index and store surfaces
   - Expected: idx.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports index and store surfaces")
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
| Source | `test/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut database vector facade.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da7873e41358e5ad41ded85e526e816fa410c64e6242c18c051ecfd6f22d62f0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da7873e41358e5ad41ded85e526e816fa410c64e6242c18c051ecfd6f22d62f0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da7873e41358e5ad41ded85e526e816fa410c64e6242c18c051ecfd6f22d62f0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports vector types, distance, and codec helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports index and store surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
