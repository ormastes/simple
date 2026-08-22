# NVFS Durable Round-Trip

> Verifies the nvfs durable roundtrip behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NVFS Durable Round-Trip

Verifies the nvfs durable roundtrip behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NVFS-DURABLE |
| Category | Runtime |
| Status | In Progress |
| Source | `test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the nvfs durable roundtrip behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### NVFS durable round-trip (REQ-NVFS-DURABLE-001)

#### persists an arena write through the block device and reads it back

- Verify: persists an arena write through the block device and reads it back
   - Expected: n equals `payload.len() as i64`
   - Expected: readback.len() as i64 equals `payload.len() as i64`
   - Expected: same is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-NVFS-DURABLE-001
step("Verify: persists an arena write through the block device and reads it back")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val dev = NvfsMockDevice.new()
nvfs_arena_set_block_device(dev)
val base = 8
val arena = arena_create_nvme_impl(0, 4096, base, 64)
expect(arena).to_be_greater_than(0)

val payload = text_to_bytes_pure("simpleos durable payload")
val n = arena_append_impl(arena, payload, 0)
expect(n).to_equal(payload.len() as i64)

val readback = arena_readv_impl(arena, 0, payload.len() as i64)
expect(readback.len() as i64).to_equal(payload.len() as i64)
var same = true
var i = 0
while i < payload.len() as i64:
    if readback[i as i32] != payload[i as i32]:
        same = false
    i = i + 1
expect(same).to_equal(true)
```

</details>

#### fsync is a real durability commit, not a silent no-op

- Verify: fsync is a real durability commit, not a silent no-op
   - Expected: n equals `payload.len() as i64`
   - Expected: before equals `-1)  # oracle: pinned constant asserted by this scenario`
   - Expected: committed is true
   - Expected: after equals `payload.len() as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-NVFS-DURABLE-001
step("Verify: fsync is a real durability commit, not a silent no-op")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(before).to_equal(-1)  # oracle: pinned constant asserted by this scenario

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

- Verify: fsync honestly reports no durability for a volatile in-memory arena
   - Expected: n equals `payload.len() as i64`
   - Expected: committed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-NVFS-DURABLE-001
step("Verify: fsync honestly reports no durability for a volatile in-memory arena")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88349701668ddbb142b57fe2b8e321882125baf4faf9a0b553334ecd79f957fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88349701668ddbb142b57fe2b8e321882125baf4faf9a0b553334ecd79f957fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88349701668ddbb142b57fe2b8e321882125baf4faf9a0b553334ecd79f957fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/nvfs/nvfs_durable_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
