# Memory Swap Block Specification

> Tests covering SimpleOS block-backed swap owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Swap Block Specification

## Scenarios

### SimpleOS block-backed swap owner

#### round trips a page through the BlockDevice contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round trips a page through the BlockDevice contract
   - Expected: written.ok is true
   - Expected: restored.ok is true
   - Expected: restored.bytes equals `expected`
   - Expected: store.snapshot().occupied_slots equals `1`
   - Expected: store.release(written.slot_id, 101).ok is true
   - Expected: store.snapshot().occupied_slots equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round trips a page through the BlockDevice contract")
val memory_device = MemBlockDevice.new(32, 512)
val device: BlockDevice = memory_device
val store = memory_swap_block_store_new(true, device, 4, 2, 4096)
var expected: [u8] = []
var i: i64 = 0
while i < 4096:
    expected.push((i % 251) as u8)
    i = i + 1

val written = store.write(101, 3, expected)
expect(written.ok).to_equal(true)
val restored = store.read(written.slot_id, 101, 3)
expect(restored.ok).to_equal(true)
expect(restored.bytes).to_equal(expected)
expect(store.snapshot().occupied_slots).to_equal(1)
expect(store.release(written.slot_id, 101).ok).to_equal(true)
expect(store.snapshot().occupied_slots).to_equal(0)
```

</details>

#### reports full and stale slot failures without releasing data

- reports full and stale slot failures without releasing data
   - Expected: written.ok is true
   - Expected: store.write(8, 0, [5]).reason equals `swap-full`
   - Expected: store.read(written.slot_id, 8, 0).reason equals `stale-mapping`
   - Expected: store.release(written.slot_id, 8).reason equals `not-owner`
   - Expected: store.read(written.slot_id, 7, 0).bytes equals `[1, 2, 3, 4]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports full and stale slot failures without releasing data")
val memory_device = MemBlockDevice.new(16, 512)
val device: BlockDevice = memory_device
val store = memory_swap_block_store_new(true, device, 0, 1, 4096)
val written = store.write(7, 0, [1, 2, 3, 4])
expect(written.ok).to_equal(true)
expect(store.write(8, 0, [5]).reason).to_equal("swap-full")
expect(store.read(written.slot_id, 8, 0).reason).to_equal("stale-mapping")
expect(store.release(written.slot_id, 8).reason).to_equal("not-owner")
expect(store.read(written.slot_id, 7, 0).bytes).to_equal([1, 2, 3, 4])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/memory_swap_block_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS block-backed swap owner.
- SimpleOS block-backed swap owner

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `be6cba7e6e0a6cf639af9d79a9d4151691fbcec16b5ddeb3da2b52749522bcbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be6cba7e6e0a6cf639af9d79a9d4151691fbcec16b5ddeb3da2b52749522bcbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be6cba7e6e0a6cf639af9d79a9d4151691fbcec16b5ddeb3da2b52749522bcbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/memory_swap_block_spec.spl
mirror: doc/06_spec/01_unit/os/memory_swap_block_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/memory_swap_block_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/memory_swap_block_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/memory_swap_block_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/memory_swap_block_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips a page through the BlockDevice contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/memory_swap_block_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports full and stale slot failures without releasing data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
