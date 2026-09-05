# Memory Swap Specification

> Tests covering SimpleOS memory swap owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Swap Specification

## Scenarios

### SimpleOS memory swap owner

#### round trips copied bytes and releases only after restore

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round trips copied bytes and releases only after restore
   - Expected: written.ok is true
   - Expected: written.slot_id equals `1`
   - Expected: restored.ok is true
   - Expected: restored.bytes equals `[17, 34, 51, 68]`
   - Expected: store.snapshot().occupied_slots equals `1`
   - Expected: released.ok is true
   - Expected: store.snapshot().occupied_slots equals `0`
   - Expected: store.read(written.slot_id, 41, 0).reason equals `missing-slot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round trips copied bytes and releases only after restore")
val store = memory_swap_store_new(true, 2)
var source: [u8] = [17, 34, 51, 68]
val written = store.write(41, 0, source)
source[0] = 255

expect(written.ok).to_equal(true)
expect(written.slot_id).to_equal(1)

val restored = store.read(written.slot_id, 41, 0)
expect(restored.ok).to_equal(true)
expect(restored.bytes).to_equal([17, 34, 51, 68])
expect(store.snapshot().occupied_slots).to_equal(1)

val released = store.release(written.slot_id, 41)
expect(released.ok).to_equal(true)
expect(store.snapshot().occupied_slots).to_equal(0)
expect(store.read(written.slot_id, 41, 0).reason).to_equal("missing-slot")
```

</details>

#### reports disabled full stale and checksum failures

- reports disabled full stale and checksum failures
   - Expected: disabled.write(1, 0, [1]).reason equals `swap-disabled`
   - Expected: store.write(2, 0, [4]).reason equals `swap-full`
   - Expected: store.read(written.slot_id, 2, 0).reason equals `stale-mapping`
   - Expected: store.corrupt_for_test(written.slot_id) is true
   - Expected: store.read(written.slot_id, 1, 0).reason equals `swap-checksum`
   - Expected: store.release(written.slot_id, 2).reason equals `not-owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports disabled full stale and checksum failures")
val disabled = memory_swap_store_new(false, 1)
expect(disabled.write(1, 0, [1]).reason).to_equal("swap-disabled")

val store = memory_swap_store_new(true, 1)
val written = store.write(1, 0, [1, 2, 3])
expect(store.write(2, 0, [4]).reason).to_equal("swap-full")
expect(store.read(written.slot_id, 2, 0).reason).to_equal("stale-mapping")
expect(store.corrupt_for_test(written.slot_id)).to_equal(true)
expect(store.read(written.slot_id, 1, 0).reason).to_equal("swap-checksum")
expect(store.release(written.slot_id, 2).reason).to_equal("not-owner")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/memory_swap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS memory swap owner.
- SimpleOS memory swap owner

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

- Canonical SPipe generation for source `feee5f26e96aaf8f57650ce34b5bbe7713fd7eccadba9e73decc9ea284c7f4d0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `feee5f26e96aaf8f57650ce34b5bbe7713fd7eccadba9e73decc9ea284c7f4d0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `feee5f26e96aaf8f57650ce34b5bbe7713fd7eccadba9e73decc9ea284c7f4d0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/memory_swap_spec.spl
mirror: doc/06_spec/01_unit/os/memory_swap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/memory_swap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/memory_swap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/memory_swap_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/memory_swap_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips copied bytes and releases only after restore' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/memory_swap_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports disabled full stale and checksum failures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
