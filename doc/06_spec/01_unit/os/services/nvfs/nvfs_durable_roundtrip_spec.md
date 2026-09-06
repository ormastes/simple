# NVFS Durable Round-Trip

> Proves that an NVFS arena write is persisted through a block device and can be read back byte-for-byte, and that `arena_fsync_impl` is a real durability commit (it writes the reserved header sector with the valid length) rather than a silent no-op. The block device is an in-memory mock, so the whole round-trip is host-verifiable via `bin/simple test` with no baremetal externs and no QEMU.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NVFS Durable Round-Trip

Proves that an NVFS arena write is persisted through a block device and can be read back byte-for-byte, and that `arena_fsync_impl` is a real durability commit (it writes the reserved header sector with the valid length) rather than a silent no-op. The block device is an in-memory mock, so the whole round-trip is host-verifiable via `bin/simple test` with no baremetal externs and no QEMU.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVFS-DURABLE |
| Category | Runtime |
| Status | In Progress |
| Source | `test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Proves that an NVFS arena write is persisted through a block device and can be
read back byte-for-byte, and that `arena_fsync_impl` is a real durability commit
(it writes the reserved header sector with the valid length) rather than a silent
no-op. The block device is an in-memory mock, so the whole round-trip is
host-verifiable via `bin/simple test` with no baremetal externs and no QEMU.

## Key Concepts

| Concept | Description |
|---------|-------------|
| nvme-backed arena | Appends write THROUGH the block device sectors (base_block+1..). |
| header sector | LBA=base_block is reserved for metadata; fsync commits the length there. |
| durable length | Recovered from the device header, independent of in-memory metadata. |

## Scenarios

### NVFS durable round-trip (REQ-NVFS-DURABLE-001)

#### persists an arena write through the block device and reads it back

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-NVFS-DURABLE-001
```

</details>

#### fsync is a real durability commit, not a silent no-op

- fsync is a real durability commit, not a silent no-op
   - Expected: n equals `payload.len() as i64`
   - Expected: before equals `-1`
   - Expected: committed is true
   - Expected: after equals `payload.len() as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fsync is a real durability commit, not a silent no-op")
val dev = NvfsMockDevice.new()
nvfs_arena_set_block_device(dev)
val base = 16
val arena = arena_create_nvme_impl(0, 4096, base, 64)
expect(arena).to_be_greater_than(0)

val payload = text_to_bytes_pure("commit-me")
val n = arena_append_impl(arena, payload, 0)
expect(n).to_equal(payload.len() as i64)

# Before fsync the reserved header sector is zeroed: no magic -> unknown length.
val before = arena_durable_len_impl(base)
expect(before).to_equal(-1)

# fsync commits the valid length into the header sector on the device.
val committed = arena_fsync_impl(arena)
expect(committed).to_equal(true)

# After fsync the length is recoverable straight from the device header,
# independent of any in-memory arena metadata.
val after = arena_durable_len_impl(base)
expect(after).to_equal(payload.len() as i64)
```

</details>

#### fsync honestly reports no durability for a volatile in-memory arena

- fsync honestly reports no durability for a volatile in-memory arena
   - Expected: n equals `payload.len() as i64`
   - Expected: committed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fsync honestly reports no durability for a volatile in-memory arena")
val arena = arena_create_impl(0, 4096)
expect(arena).to_be_greater_than(0)
val payload = text_to_bytes_pure("volatile")
val n = arena_append_impl(arena, payload, 0)
expect(n).to_equal(payload.len() as i64)
# No block backing -> fsync must not claim success.
val committed = arena_fsync_impl(arena)
expect(committed).to_equal(false)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-NVFS-DURABLE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d46d13c56f34ec0f6b321d270584c05eed5ddf6dc8730ed511267e86a7ae14b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d46d13c56f34ec0f6b321d270584c05eed5ddf6dc8730ed511267e86a7ae14b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d46d13c56f34ec0f6b321d270584c05eed5ddf6dc8730ed511267e86a7ae14b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl:131:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'persists an arena write through the block device and reads it back' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl:156:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsync is a real durability commit, not a silent no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsync honestly reports no durability for a volatile in-memory arena' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
