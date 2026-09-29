# Zz Probe2 Specification

> Tests covering nvme probe.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zz Probe2 Specification

## Scenarios

### nvme probe

#### granule and device

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- build arena over MemBlockDevice, assert granule, I/O, append
   - Expected: dev.sector_size() as i64 equals `512`
   - Expected: arena.arena_preferred_granule(h) equals `512`
   - Expected: ws.is_ok() is true
   - Expected: rs.is_ok() is true
   - Expected: r.bytes_written equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("build arena over MemBlockDevice, assert granule, I/O, append")
val dev = MemBlockDevice.new(1024u64, 512u32)
expect(dev.sector_size() as i64).to_equal(512)
val arena = RawNvmeArena.new(dev, 2, 8)
val h = arena.arena_handle()
expect(arena.arena_preferred_granule(h)).to_equal(512)
val before = nvme_arena_registered_count()
expect(before).to_be_greater_than(0)
val ws = dev.write_sector(3u64, [1u8, 2u8])
expect(ws.is_ok()).to_equal(true)
val rs = dev.read_sector(3u64)
expect(rs.is_ok()).to_equal(true)
val r = arena.arena_append(h, [1u8, 2u8], DurabilityClass.BestEffort)
expect(r.bytes_written).to_equal(2)
expect(r.generation).to_be_greater_than(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nvme probe.
- nvme probe

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `257fa167f29bba08427cc754c1fbac244519add64de96f2a42e8fd8db5ed5d59`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `257fa167f29bba08427cc754c1fbac244519add64de96f2a42e8fd8db5ed5d59`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `257fa167f29bba08427cc754c1fbac244519add64de96f2a42e8fd8db5ed5d59`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'granule and device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
