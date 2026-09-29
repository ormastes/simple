# @manual: primary

> Purpose: Prove that FAT32 RecoverableReplaceV1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that FAT32 RecoverableReplaceV1.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that FAT32 RecoverableReplaceV1.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-KERNEL-001
doc/01_research/local/REQ-OS-KERNEL-001.md
doc/03_plan/sys_test/REQ-OS-KERNEL-001.md
doc/04_architecture/REQ-OS-KERNEL-001.md
doc/05_design/REQ-OS-KERNEL-001.md

## Scenarios

### FAT32 RecoverableReplaceV1

### FAR-001: same-sector coalescing

#### should retain one final image and expose new only after commit

- Given a provisioned dual-bank journal
   - Expected: images.len() equals `1`
   - Expected: images[0].bytes[0] equals `2u8`
   - Expected: Then_exactly_generation_is_visible(7, 8, When_replace_crashes_after(4)) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Given a provisioned dual-bank journal")
val a = fat32_replace_image(100u64, _sector(1u8)).unwrap()
val b = fat32_replace_image(100u64, _sector(2u8)).unwrap()
val images = fat32_replace_coalesce_images([a, b]).unwrap()
expect(images.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(images[0].bytes[0]).to_equal(2u8)
expect(Then_exactly_generation_is_visible(7, 8, When_replace_crashes_after(4))).to_equal(8)  # oracle: 8 — named expected value from the requirement
```

</details>

### FAR-002: distinct ordered images

#### should sort complete after-images and keep pre-commit old

- Construct destination and source after-images in reverse LBA order
   - Expected: images.len() equals `2`
   - Expected: images[0].lba equals `100u64`
   - Expected: images[1].lba equals `120u64`
   - Expected: Then_exactly_generation_is_visible(7, 8, When_replace_crashes_after(3)) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Construct destination and source after-images in reverse LBA order")
val hi = fat32_replace_image(120u64, _sector(3u8)).unwrap()
val lo = fat32_replace_image(100u64, _sector(4u8)).unwrap()
val images = fat32_replace_coalesce_images([hi, lo]).unwrap()
expect(images.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(images[0].lba).to_equal(100u64)
expect(images[1].lba).to_equal(120u64)
expect(Then_exactly_generation_is_visible(7, 8, When_replace_crashes_after(3))).to_equal(7)  # oracle: 7 — named expected value from the requirement
```

</details>

### FAR-003: corrupt and torn banks

#### should reject corrupted payload and choose the older valid bank

- Encode a checksummed committed bank
   - Expected: fat32_replace_header_valid(header, payload, 0) is true
   - Expected: fat32_replace_header_valid(header, torn, 0) is false
   - Expected: fat32_replace_choose_bank(true, 9u64, false, 10u64).unwrap() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Encode a checksummed committed bank")
val image = fat32_replace_image(100u64, _sector(5u8)).unwrap()
val images = [image]
val payload = _payload(images)
val header = fat32_replace_encode_header(_record(0, 10u64, images, Fat32ReplaceState.Committed), crc32c(payload)).unwrap()
expect(fat32_replace_header_valid(header, payload, 0)).to_equal(true)
var torn = payload
torn[0] = 9u8
expect(fat32_replace_header_valid(header, torn, 0)).to_equal(false)
expect(fat32_replace_choose_bank(true, 9u64, false, 10u64).unwrap()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should fail closed for two invalid banks and ambiguous generations

- Reject absence of authoritative journal state
   - Expected: fat32_replace_choose_bank(false, 0u64, false, 0u64).is_err() is true
   - Expected: fat32_replace_choose_bank(true, 0u64, true, 0x8000000000000000u64).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Reject absence of authoritative journal state")
expect(fat32_replace_choose_bank(false, 0u64, false, 0u64).is_err()).to_equal(true)
expect(fat32_replace_choose_bank(true, 0u64, true, 0x8000000000000000u64).is_err()).to_equal(true)
```

</details>

### FAR-004: repeated replay and reclamation

#### should make already-free cursor replay advance without double-free

- Resume a durable reclaim cursor after its cluster was freed
   - Expected: fat32_replace_reclaim_transition(20u32, 21u32, 0u32, true, 30u32).unwrap() equals `21u32`
   - Expected: fat32_replace_reclaim_transition(20u32, 21u32, 22u32, false, 30u32).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Resume a durable reclaim cursor after its cluster was freed")
expect(fat32_replace_reclaim_transition(20u32, 21u32, 0u32, true, 30u32).unwrap()).to_equal(21u32)
expect(fat32_replace_reclaim_transition(20u32, 21u32, 22u32, false, 30u32).is_err()).to_equal(true)
```

</details>

#### should repair only saved-next/free FAT-copy divergence

- Classify every FAT copy after an interrupted free
   - Expected: fat32_replace_classify_reclaim_copies([21u32, 0u32], 21u32).unwrap() is false
   - Expected: fat32_replace_classify_reclaim_copies([0u32, 0u32], 21u32).unwrap() is true
   - Expected: fat32_replace_classify_reclaim_copies([21u32, 22u32], 21u32).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Classify every FAT copy after an interrupted free")
expect(fat32_replace_classify_reclaim_copies([21u32, 0u32], 21u32).unwrap()).to_equal(false)
expect(fat32_replace_classify_reclaim_copies([0u32, 0u32], 21u32).unwrap()).to_equal(true)
expect(fat32_replace_classify_reclaim_copies([21u32, 22u32], 21u32).is_err()).to_equal(true)
```

</details>

#### should reject overlap anywhere in complete old and new chains

- Compare full candidate cluster chains before COMMITTED
   - Expected: fat32_replace_chains_are_disjoint([20u32, 21u32, 22u32], [30u32, 31u32]) is true
   - Expected: fat32_replace_chains_are_disjoint([20u32, 21u32, 22u32], [30u32, 21u32]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Compare full candidate cluster chains before COMMITTED")
expect(fat32_replace_chains_are_disjoint([20u32, 21u32, 22u32], [30u32, 31u32])).to_equal(true)
expect(fat32_replace_chains_are_disjoint([20u32, 21u32, 22u32], [30u32, 21u32])).to_equal(false)
```

</details>

### FAR-005: bounded old-chain reclamation

#### should expose exactly sixteen journal sectors and a durable cursor

- Inspect provisioned capability and cursor transitions
   - Expected: caps.journal_bytes equals `8192`
   - Expected: fat32_replace_reclaim_transition(20u32, 0x0FFFFFF8u32, 0x0FFFFFF8u32, false, 30u32).unwrap() equals `0x0FFFFFF8u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Inspect provisioned capability and cursor transitions")
val caps = Given_provisioned_replace_journal()
expect(caps.journal_bytes).to_equal(8192)  # oracle: 8192 — named expected value from the requirement
expect(fat32_replace_reclaim_transition(20u32, 0x0FFFFFF8u32, 0x0FFFFFF8u32, false, 30u32).unwrap()).to_equal(0x0FFFFFF8u32)
```

</details>

### FAR-006: fail-closed policy

#### should reject missing durability, traversal, bad cursors, and oversized image sets

- Exercise every locally decidable fail-closed bound
   - Expected: fat32_atomic_replace_caps_for(true, false, true).level equals `AtomicReplaceRecoveryLevel.Unsupported`
   - Expected: fat32_atomic_replace_path_allowed("/../SERVER.DB") is false
   - Expected: fat32_atomic_replace_path_allowed("/SERVER.DB") is true
   - Expected: fat32_atomic_replace_path_allowed("/SIMPLE.DB") is false
   - Expected: fat32_atomic_replace_route_allowed("/SERVER.TMP", "/SERVER.DB") is true
   - Expected: fat32_atomic_replace_route_allowed("/OTHER.TMP", "/SERVER.DB") is false
   - Expected: fat32_replace_image_lba_allowed(100u64, 100u64, 4u32) is true
   - Expected: fat32_replace_image_lba_allowed(103u64, 100u64, 4u32) is true
   - Expected: fat32_replace_image_lba_allowed(99u64, 100u64, 4u32) is false
   - Expected: fat32_replace_image_lba_allowed(104u64, 100u64, 4u32) is false
   - Expected: fat32_replace_extent_valid(16u32, 16u32, 1000u32, 32u32) is true
   - Expected: fat32_replace_extent_valid(0xFFFFFFF8u32, 16u32, 0xFFFFFFFFu32, 0xFFFFFFFFu32) is false
   - Expected: fat32_replace_reclaim_transition(30u32, 31u32, 31u32, false, 30u32).is_err() is true
   - Expected: fat32_replace_coalesce_images(images).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Exercise every locally decidable fail-closed bound")
expect(fat32_atomic_replace_caps_for(true, false, true).level).to_equal(AtomicReplaceRecoveryLevel.Unsupported)
expect(fat32_atomic_replace_path_allowed("/../SERVER.DB")).to_equal(false)
expect(fat32_atomic_replace_path_allowed("/SERVER.DB")).to_equal(true)
expect(fat32_atomic_replace_path_allowed("/SIMPLE.DB")).to_equal(false)
expect(fat32_atomic_replace_route_allowed("/SERVER.TMP", "/SERVER.DB")).to_equal(true)
expect(fat32_atomic_replace_route_allowed("/OTHER.TMP", "/SERVER.DB")).to_equal(false)
expect(fat32_replace_image_lba_allowed(100u64, 100u64, 4u32)).to_equal(true)
expect(fat32_replace_image_lba_allowed(103u64, 100u64, 4u32)).to_equal(true)
expect(fat32_replace_image_lba_allowed(99u64, 100u64, 4u32)).to_equal(false)
expect(fat32_replace_image_lba_allowed(104u64, 100u64, 4u32)).to_equal(false)
expect(fat32_replace_extent_valid(16u32, 16u32, 1000u32, 32u32)).to_equal(true)
expect(fat32_replace_extent_valid(0xFFFFFFF8u32, 16u32, 0xFFFFFFFFu32, 0xFFFFFFFFu32)).to_equal(false)
expect(fat32_replace_reclaim_transition(30u32, 31u32, 31u32, false, 30u32).is_err()).to_equal(true)
var images: [Fat32ReplaceImage] = []
var i = 0
while i < 5:
    images.push(fat32_replace_image((100 + i).to_u64(), _sector(i.to_u8())).unwrap())
    i = i + 1
expect(fat32_replace_coalesce_images(images).is_err()).to_equal(true)
```

</details>

### FAR-007: DONE tombstone

#### should outrank older committed and require no replay

- Select a newer terminal record
   - Expected: fat32_replace_choose_bank(true, 8u64, true, 9u64).unwrap() equals `1`
   - Expected: When_mount_recovery_runs(Fat32ReplaceState.Done) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Select a newer terminal record")
expect(fat32_replace_choose_bank(true, 8u64, true, 9u64).unwrap()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(When_mount_recovery_runs(Fat32ReplaceState.Done)).to_equal(false)
```

</details>

#### should expose deterministic zero-based crash injection controls

- Arm and clear a frozen journal crash seam
   - Expected: fat32_replace_fault_injection_occurrence() equals `2`
   - Expected: fat32_replace_fault_injection_triggered() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Arm and clear a frozen journal crash seam")
fat32_replace_fault_injection_set(Fat32ReplaceCrashSeam.FatCopyWrite, 2)
expect(fat32_replace_fault_injection_occurrence()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(fat32_replace_fault_injection_triggered()).to_equal(false)
fat32_replace_fault_injection_clear()
```

</details>

#### should make every reclaim and DONE crash seam deterministically reachable

- Seed each owner checkpoint at zero-based occurrence zero
   - Expected: fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.ReclaimHeaderWrite) is true
   - Expected: fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.FatCopiesFlush) is true
   - Expected: fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.FatCopiesReread) is true
   - Expected: fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.DoneHeaderFlush) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Seed each owner checkpoint at zero-based occurrence zero")
fat32_replace_fault_injection_set(Fat32ReplaceCrashSeam.ReclaimHeaderWrite, 0)
expect(fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.ReclaimHeaderWrite)).to_equal(true)
fat32_replace_fault_injection_set(Fat32ReplaceCrashSeam.FatCopiesFlush, 0)
expect(fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.FatCopiesFlush)).to_equal(true)
fat32_replace_fault_injection_set(Fat32ReplaceCrashSeam.FatCopiesReread, 0)
expect(fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.FatCopiesReread)).to_equal(true)
fat32_replace_fault_injection_set(Fat32ReplaceCrashSeam.DoneHeaderFlush, 0)
expect(fat32_replace_fault_injection_checkpoint(Fat32ReplaceCrashSeam.DoneHeaderFlush)).to_equal(true)
fat32_replace_fault_injection_clear()
```

</details>

### FAR-008: mount-before-publish

#### should withhold capability until recovery completes

- Attempt capability publication before mount recovery
   - Expected: fat32_atomic_replace_caps_for(true, true, false).level equals `AtomicReplaceRecoveryLevel.Unsupported`
   - Expected: Given_provisioned_replace_journal().level equals `AtomicReplaceRecoveryLevel.RecoverableReplaceV1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Attempt capability publication before mount recovery")
expect(fat32_atomic_replace_caps_for(true, true, false).level).to_equal(AtomicReplaceRecoveryLevel.Unsupported)
expect(Given_provisioned_replace_journal().level).to_equal(AtomicReplaceRecoveryLevel.RecoverableReplaceV1)
```

</details>

### FAR-009: distinct ordinary rename semantics

#### should keep recoverable replacement as an explicit separate capability

- Inspect the typed replacement level
   - Expected: caps.level equals `AtomicReplaceRecoveryLevel.RecoverableReplaceV1`
   - Expected: caps.same_volume_only is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-KERNEL-001
step("Inspect the typed replacement level")
val caps = Given_provisioned_replace_journal()
expect(caps.level).to_equal(AtomicReplaceRecoveryLevel.RecoverableReplaceV1)
expect(caps.same_volume_only).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-KERNEL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70963ab675d775c0ebe929d03ecca9229c2b051d36c6aaa633a925040d175884`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70963ab675d775c0ebe929d03ecca9229c2b051d36c6aaa633a925040d175884`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70963ab675d775c0ebe929d03ecca9229c2b051d36c6aaa633a925040d175884`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain one final image and expose new only after commit' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain one final image and expose new only after commit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should sort complete after-images and keep pre-commit old' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should sort complete after-images and keep pre-commit old' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject corrupted payload and choose the older valid bank' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject corrupted payload and choose the older valid bank' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:119:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed for two invalid banks and ambiguous generations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:126:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should make already-free cursor replay advance without double-free' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl:132:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should repair only saved-next/free FAT-copy divergence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
