# Nvfs Posix Nvme Specification

> Tests covering NvfsPosixDriver NVMe-backed open/read/write.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Posix Nvme Specification

## Scenarios

### NvfsPosixDriver NVMe-backed open/read/write

#### write and read round-trip through NVMe backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- write and read round-trip through NVMe backend
   - Expected: nvfs_arena_has_block_device() is true
   - Expected: trip.ok is true
   - Expected: trip.write_n equals `5`
   - Expected: trip.read_n equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write and read round-trip through NVMe backend")
var dev = _make_posix_device()
nvfs_arena_set_block_device(dev)
expect(nvfs_arena_has_block_device()).to_equal(true)
val data: [u8] = [0x48, 0x65, 0x6C, 0x6C, 0x6F]
# _nvme_next_block starts at 64; this test allocates base=64, data LBA=65
val trip = _do_round_trip(data, 65u64)
expect(trip.ok).to_equal(true)
expect(trip.write_n).to_equal(5)
expect(trip.read_n).to_equal(5)
```

</details>

#### data lands on NVMe sectors (raw sector verification)

- data lands on NVMe sectors (raw sector verification)
   - Expected: trip.ok is true
   - Expected: trip.sec0 equals `0xDE`
   - Expected: trip.sec1 equals `0xAD`
   - Expected: trip.sec2 equals `0xBE`
   - Expected: trip.sec3 equals `0xEF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("data lands on NVMe sectors (raw sector verification)")
var dev = _make_posix_device()
nvfs_arena_set_block_device(dev)
val data: [u8] = [0xDE, 0xAD, 0xBE, 0xEF]
# Test 1 consumed base=64; test 2 gets base=96, data LBA=97
val trip = _do_round_trip(data, 97u64)
expect(trip.ok).to_equal(true)
# bytes must appear at the start of the data sector
expect(trip.sec0).to_equal(0xDE)
expect(trip.sec1).to_equal(0xAD)
expect(trip.sec2).to_equal(0xBE)
expect(trip.sec3).to_equal(0xEF)
```

</details>

#### multiple files each get distinct NVMe sector regions

- multiple files each get distinct NVMe sector regions
   - Expected: result.ok is true
   - Expected: result.rn1 equals `3`
   - Expected: result.rn2 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("multiple files each get distinct NVMe sector regions")
var dev = _make_posix_device()
nvfs_arena_set_block_device(dev)
val result = _do_two_files(dev)
expect(result.ok).to_equal(true)
expect(result.rn1).to_equal(3)
expect(result.rn2).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/nvfs/nvfs_posix_nvme_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NvfsPosixDriver NVMe-backed open/read/write.
- NvfsPosixDriver NVMe-backed open/read/write

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07623aaaa6026b97e010535cf936eeaa29176ae10c99a278654012c7601269dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07623aaaa6026b97e010535cf936eeaa29176ae10c99a278654012c7601269dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07623aaaa6026b97e010535cf936eeaa29176ae10c99a278654012c7601269dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/storage/nvfs/nvfs_posix_nvme_spec.spl
mirror: doc/06_spec/integration/storage/nvfs/nvfs_posix_nvme_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/nvfs/nvfs_posix_nvme_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/nvfs/nvfs_posix_nvme_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/nvfs/nvfs_posix_nvme_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/nvfs/nvfs_posix_nvme_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'write and read round-trip through NVMe backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/nvfs/nvfs_posix_nvme_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'data lands on NVMe sectors (raw sector verification)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/nvfs/nvfs_posix_nvme_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple files each get distinct NVMe sector regions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
