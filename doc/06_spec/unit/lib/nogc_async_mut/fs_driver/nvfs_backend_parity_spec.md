# Nvfs Backend Parity Specification

> Tests covering nogc_async_mut NVFS backend facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Backend Parity Specification

## Scenarios

### nogc_async_mut NVFS backend facade

#### re-exports arena operations from the canonical backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports arena operations from the canonical backend
   - Expected: aid > 0 is true
   - Expected: arena_append_impl(aid, data, 0) equals `3`
   - Expected: rd.len() as i64 equals `3`
   - Expected: rd[0] equals `0x31`
   - Expected: rd[2] equals `0x33`
   - Expected: arena_seal_impl(aid, 1) is true
   - Expected: arena_is_sealed_impl(aid) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports arena operations from the canonical backend")
val aid = arena_create_impl(0, 4096)
expect(aid > 0).to_equal(true)
val data: [u8] = [0x31, 0x32, 0x33]
expect(arena_append_impl(aid, data, 0)).to_equal(3)
val rd = arena_readv_impl(aid, 0, 3)
expect(rd.len() as i64).to_equal(3)
expect(rd[0]).to_equal(0x31)
expect(rd[2]).to_equal(0x33)
expect(arena_seal_impl(aid, 1)).to_equal(true)
expect(arena_is_sealed_impl(aid)).to_equal(true)
```

</details>

#### re-exports superblock and storage constants

- re-exports superblock and storage constants
   - Expected: sb.magic equals `NVFS_MAGIC`
   - Expected: STORAGE_CLASS_DB_WAL > 0 is true
   - Expected: DURABILITY_DATA_DURABLE > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports superblock and storage constants")
val sb = NvfsSuperblock(
    magic: NVFS_MAGIC,
    version: 1,
    uuid_hi: 0,
    uuid_lo: 0,
    feature_bits: 0,
    mount_generation: 1,
    checkpoint_root: 2,
    replica_id: 0u8,
    valid: true,
    checksum: 0,
    compat_v1: false
)
expect(sb.magic).to_equal(NVFS_MAGIC)
expect(STORAGE_CLASS_DB_WAL > 0).to_equal(true)
expect(DURABILITY_DATA_DURABLE > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut NVFS backend facade.
- nogc_async_mut NVFS backend facade

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

- Canonical SPipe generation for source `d6d462863cb8f55c8cc7deadbb6733255311b42902532908a7445b3900c7d6fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d6d462863cb8f55c8cc7deadbb6733255311b42902532908a7445b3900c7d6fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d6d462863cb8f55c8cc7deadbb6733255311b42902532908a7445b3900c7d6fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports arena operations from the canonical backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/fs_driver/nvfs_backend_parity_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports superblock and storage constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
