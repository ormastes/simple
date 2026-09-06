# Nvfs Facade Specification

> Tests covering gc_async_mut fs nvfs facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Facade Specification

## Scenarios

### gc_async_mut fs nvfs facade

#### re-exports NVFS extent, superblock, and arena contract records

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports NVFS extent, superblock, and arena contract records
   - Expected: handle.id equals `7`
   - Expected: extent.arena_id equals `7`
   - Expected: extent.length equals `8192`
   - Expected: header.version_major equals `1`
   - Expected: header.checkpoint_gen equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports NVFS extent, superblock, and arena contract records")
val handle = ArenaHandle(id: 7)
expect(handle.id).to_equal(7)
val extent = ExtentMapEntry(logical_off: 0, arena_id: handle.id, phys_off: 4096, length: 8192, generation: 3)
expect(extent.arena_id).to_equal(7)
expect(extent.length).to_equal(8192)
val header = SuperblockHeader(
    magic: 0x4e564653,
    version_major: 1,
    version_minor: 0,
    fs_uuid_lo: 11,
    fs_uuid_hi: 22,
    checkpoint_gen: 5,
    created_unix_ns: 123456
)
expect(header.version_major).to_equal(1)
expect(header.checkpoint_gen).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut fs nvfs facade.
- gc_async_mut fs nvfs facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `dfe749b981ddf8c243358781df1d27d0783f50a7b3eb52acaa33bcec3de53759`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dfe749b981ddf8c243358781df1d27d0783f50a7b3eb52acaa33bcec3de53759`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dfe749b981ddf8c243358781df1d27d0783f50a7b3eb52acaa33bcec3de53759`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/fs/nvfs/nvfs_facade_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports NVFS extent, superblock, and arena contract records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
