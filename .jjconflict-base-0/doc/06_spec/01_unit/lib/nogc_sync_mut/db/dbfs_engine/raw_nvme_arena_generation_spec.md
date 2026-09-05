# Raw Nvme Arena Generation Specification

> Tests covering RawNvmeArena generational handles.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raw Nvme Arena Generation Specification

## Scenarios

### RawNvmeArena generational handles

#### current handle appends and reads normally

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- current handle appends and reads normally
   - Expected: r.bytes_written equals `4`
   - Expected: r.generation >= 0 is true
   - Expected: got.len() equals `4`
   - Expected: got[0] as i64 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("current handle appends and reads normally")
val dev = MemBlockDevice.new(1024u64, 512u32)
val arena = RawNvmeArena.new(dev, 2, 8)
val h = arena.arena_handle()
val r = arena.arena_append(h, [1u8, 2u8, 3u8, 4u8], DurabilityClass.BestEffort)
expect(r.bytes_written).to_equal(4)
expect(r.generation >= 0).to_equal(true)
val got = arena.arena_read_bytes(h, 0, 4)
expect(got.len()).to_equal(4)
expect(got[0] as i64).to_equal(1)
```

</details>

#### rejects a stale handle after arena_create reuses the region

- rejects a stale handle after arena_create reuses the region
   - Expected: r0.bytes_written equals `2`
   - Expected: h_new.generation != h_old.generation is true
   - Expected: r1.bytes_written equals `0`
   - Expected: r1.generation equals `-1`
   - Expected: fresh.bytes_written equals `2`
   - Expected: arena.arena_read_bytes(h_old, 0, 2).len() equals `0`
   - Expected: arena.arena_readv(h_old, 0, buf) equals `0`
   - Expected: arena.arena_seal(h_old, 0) is false
   - Expected: arena.arena_discard(h_old) is false
   - Expected: arena.arena_read_bytes(h_new, 0, 2).len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a stale handle after arena_create reuses the region")
val dev = MemBlockDevice.new(1024u64, 512u32)
val arena = RawNvmeArena.new(dev, 20, 8)
val h_old = arena.arena_handle()
val r0 = arena.arena_append(h_old, [9u8, 9u8], DurabilityClass.BestEffort)
expect(r0.bytes_written).to_equal(2)

# Reuse the region: re-provision the arena. Old handle is now stale.
val h_new = arena.arena_create(StorageClass.GENERAL_MUTABLE, 0)
expect(h_new.generation != h_old.generation).to_equal(true)

# Stale append must be refused.
val r1 = arena.arena_append(h_old, [7u8], DurabilityClass.BestEffort)
expect(r1.bytes_written).to_equal(0)
expect(r1.generation).to_equal(-1)

# Stale reads must return nothing.
val fresh = arena.arena_append(h_new, [5u8, 6u8], DurabilityClass.BestEffort)
expect(fresh.bytes_written).to_equal(2)
expect(arena.arena_read_bytes(h_old, 0, 2).len()).to_equal(0)
var buf: [u8] = [0u8, 0u8]
expect(arena.arena_readv(h_old, 0, buf)).to_equal(0)

# Stale seal/discard must be refused.
expect(arena.arena_seal(h_old, 0)).to_equal(false)
expect(arena.arena_discard(h_old)).to_equal(false)

# New handle keeps working.
expect(arena.arena_read_bytes(h_new, 0, 2).len()).to_equal(2)
```

</details>

#### rejects a pre-discard handle after the region is re-registered

- rejects a pre-discard handle after the region is re-registered
   - Expected: arena.arena_discard(h_old) is true
   - Expected: h_new.generation != h_old.generation is true
   - Expected: r.bytes_written equals `0`
   - Expected: r2.bytes_written equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a pre-discard handle after the region is re-registered")
val dev = MemBlockDevice.new(1024u64, 512u32)
val arena = RawNvmeArena.new(dev, 40, 8)
val h_old = arena.arena_handle()
expect(arena.arena_discard(h_old)).to_equal(true)

# Re-register the same base_block (fresh device binding = reuse).
val dev2 = MemBlockDevice.new(1024u64, 512u32)
val arena2 = RawNvmeArena.new(dev2, 40, 8)
val h_new = arena2.arena_handle()
expect(h_new.generation != h_old.generation).to_equal(true)

val r = arena2.arena_append(h_old, [1u8], DurabilityClass.BestEffort)
expect(r.bytes_written).to_equal(0)
val r2 = arena2.arena_append(h_new, [1u8], DurabilityClass.BestEffort)
expect(r2.bytes_written).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RawNvmeArena generational handles.
- RawNvmeArena generational handles

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `67231540f7791f3d12c27c78e94993538aaa53e04cef61250c108d26e7800453`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67231540f7791f3d12c27c78e94993538aaa53e04cef61250c108d26e7800453`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67231540f7791f3d12c27c78e94993538aaa53e04cef61250c108d26e7800453`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'current handle appends and reads normally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a stale handle after arena_create reuses the region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena_generation_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a pre-discard handle after the region is re-registered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
