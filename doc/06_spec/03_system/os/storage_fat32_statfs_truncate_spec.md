# storage_fat32_statfs_truncate_spec

> FR-STORAGE-0001 — FAT32 free-space and truncate primitives.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# storage_fat32_statfs_truncate_spec

FR-STORAGE-0001 — FAT32 free-space and truncate primitives.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/storage_fat32_statfs_truncate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

FR-STORAGE-0001 — FAT32 free-space and truncate primitives.

## Scenarios

### FAT32 statfs and truncate primitives

#### counts free FAT entries across mounted data clusters

- counts free FAT entries across mounted data clusters
   - Expected: free.is_ok() is true
   - Expected: free.unwrap() equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts free FAT entries across mounted data clusters")
"""Mounted drivers count free data clusters from FAT entries."""
var driver = statfs_driver()
val free = driver.count_free_clusters()
expect(free.is_ok()).to_equal(true)
expect(free.unwrap()).to_equal(2u32)
```

</details>

#### truncate_chain can free a whole file chain

- truncate_chain can free a whole file chain
   - Expected: truncated.is_ok() is true
   - Expected: truncated.unwrap() equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("truncate_chain can free a whole file chain")
"""Truncating to zero releases the chain and returns an empty first cluster."""
var driver = statfs_driver()
val truncated = driver.truncate_chain(2, 0)
expect(truncated.is_ok()).to_equal(true)
expect(truncated.unwrap()).to_equal(0u32)
```

</details>

#### truncate_chain extends an empty chain by allocating a cluster

- truncate_chain extends an empty chain by allocating a cluster
   - Expected: extended.is_ok() is true
   - Expected: new_cluster >= 2u32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("truncate_chain extends an empty chain by allocating a cluster")
"""Extending from cluster 0 allocates a new cluster and returns it."""
var driver = statfs_driver()
# Start with no chain (first_cluster < 2), ask for 100 bytes
val extended = driver.truncate_chain(0, 100)
expect(extended.is_ok()).to_equal(true)
# Should have allocated one of the free clusters (3 or 4)
val new_cluster = extended.unwrap()
expect(new_cluster >= 2u32).to_equal(true)
```

</details>

#### ftruncate updates in-memory file size via handle

- ftruncate updates in-memory file size via handle
   - Expected: trunc_rc.is_ok() is true
   - Expected: of.is_ok() is true
   - Expected: of.unwrap().size equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ftruncate updates in-memory file size via handle")
"""Handle-based truncate shrinks and correctly updates in-memory size."""
var driver = statfs_driver()
# Manually set up an open file on cluster 2 (which has EOC)
use std.fs_driver.types.{FileHandle}
val fh = driver.alloc_file_handle(2, 512, false).unwrap()
val trunc_rc = driver.truncate(fh, 0)
expect(trunc_rc.is_ok()).to_equal(true)
val of = driver.get_open_file(fh)
expect(of.is_ok()).to_equal(true)
expect(of.unwrap().size).to_equal(0i64)
```

</details>

#### truncate_chain shrinks a multi-cluster chain

- truncate_chain shrinks a multi-cluster chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("truncate_chain shrinks a multi-cluster chain")
"""Shrinking keeps required clusters and frees the tail."""
var driver = statfs_driver()
# cluster 5 has EOC, cluster 2 has EOC -- both are single-cluster chains
# truncate cluster 5 to 256 bytes (< 512 cluster size) should keep cluster 5
val shrunk = driver.truncate_chain(5, 256)
assert_true(shrunk.is_ok())
assert_equal(shrunk.unwrap(), 5u32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `668cc821cbf3d2379636f5eae04843e171074b8f23e199cace27954571d9f33f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `668cc821cbf3d2379636f5eae04843e171074b8f23e199cace27954571d9f33f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `668cc821cbf3d2379636f5eae04843e171074b8f23e199cace27954571d9f33f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/storage_fat32_statfs_truncate_spec.spl
mirror: doc/06_spec/03_system/os/storage_fat32_statfs_truncate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/storage_fat32_statfs_truncate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/storage_fat32_statfs_truncate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/storage_fat32_statfs_truncate_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts free FAT entries across mounted data clusters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/storage_fat32_statfs_truncate_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'truncate_chain can free a whole file chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/storage_fat32_statfs_truncate_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'truncate_chain extends an empty chain by allocating a cluster' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
