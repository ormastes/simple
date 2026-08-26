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


- granule and device
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("granule and device")
val dev = MemBlockDevice.new(1024u64, 512u32)
print("direct sector_size={dev.sector_size() as i64}")
val arena = RawNvmeArena.new(dev, 2, 8)
val h = arena.arena_handle()
print("granule={arena.arena_preferred_granule(h)} count={nvme_arena_registered_count()}")
val ws = dev.write_sector(3u64, [1u8, 2u8])
print("write_ok={ws.is_ok()}")
val rs = dev.read_sector(3u64)
print("read_ok={rs.is_ok()}")
val r = arena.arena_append(h, [1u8, 2u8], DurabilityClass.BestEffort)
print("bw={r.bytes_written} rgen={r.generation}")
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl` |
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `560bc6b3a390e1e0e18fc676bff3b66cdeba4e154173f3b3e9719f8afe14ba46`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `560bc6b3a390e1e0e18fc676bff3b66cdeba4e154173f3b3e9719f8afe14ba46`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `560bc6b3a390e1e0e18fc676bff3b66cdeba4e154173f3b3e9719f8afe14ba46`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **75/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=75; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/db/dbfs_engine/zz_probe2_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'granule and device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
