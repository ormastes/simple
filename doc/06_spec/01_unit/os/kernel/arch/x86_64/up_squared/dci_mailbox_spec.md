# Dci Mailbox Specification

> Tests covering UP2 DCI mailbox admission, UP2 DCI mailbox wire v1, UP2 DCI physical ELF plan, UP2 DCI-staged storage admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dci Mailbox Specification

## Scenarios

### UP2 DCI mailbox admission

#### admits a fresh committed exact-digest payload

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits a fresh committed exact-digest payload
   - Expected: result.accepted is true
   - Expected: result.reason equals `admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits a fresh committed exact-digest payload")
val result = dci_admit_mailbox(mailbox(DciCommitState.Committed, 2u64, 77u64), 1u64, 77u64, UP2_IMAGE_SIZE, TEST_HASH)
expect(result.accepted).to_equal(true)
expect(result.reason).to_equal("admitted")
```

</details>

#### rejects partial commit, replay, nonce mismatch, and digest mismatch

- rejects partial commit, replay, nonce mismatch, and digest mismatch
   - Expected: dci_admit_mailbox(mailbox(DciCommitState.PayloadWritten, 2u64, 77u64), 1u64, 77u64, UP2_IMAGE_SIZE, TEST_HASH).reason equals `mailbox-not-committed`
   - Expected: dci_admit_mailbox(mailbox(DciCommitState.Committed, 1u64, 77u64), 1u64, 77u64, UP2_IMAGE_SIZE, TEST_HASH).reason equals `mailbox-generation-replayed`
   - Expected: dci_admit_mailbox(mailbox(DciCommitState.Committed, 2u64, 78u64), 1u64, 77u64, UP2_IMAGE_SIZE, TEST_HASH).reason equals `mailbox-nonce`
   - Expected: dci_admit_mailbox(mailbox(DciCommitState.Committed, 2u64, 77u64), 1u64, 77u64, UP2_IMAGE_SIZE, "a" * 64).reason equals `mailbox-payload-digest-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects partial commit, replay, nonce mismatch, and digest mismatch")
expect(dci_admit_mailbox(mailbox(DciCommitState.PayloadWritten, 2u64, 77u64), 1u64, 77u64, UP2_IMAGE_SIZE, TEST_HASH).reason).to_equal("mailbox-not-committed")
expect(dci_admit_mailbox(mailbox(DciCommitState.Committed, 1u64, 77u64), 1u64, 77u64, UP2_IMAGE_SIZE, TEST_HASH).reason).to_equal("mailbox-generation-replayed")
expect(dci_admit_mailbox(mailbox(DciCommitState.Committed, 2u64, 78u64), 1u64, 77u64, UP2_IMAGE_SIZE, TEST_HASH).reason).to_equal("mailbox-nonce")
expect(dci_admit_mailbox(mailbox(DciCommitState.Committed, 2u64, 77u64), 1u64, 77u64, UP2_IMAGE_SIZE, "a" * 64).reason).to_equal("mailbox-payload-digest-mismatch")
```

</details>

### UP2 DCI mailbox wire v1

#### round-trips the fixed packed record with commit in the final word

- round-trips the fixed packed record with commit in the final word
   - Expected: wire.len() equals `DCI_MAILBOX_WIRE_V1_SIZE`
   - Expected: DCI_MAILBOX_WIRE_V1_COMMIT_OFFSET equals `124`
   - Expected: wire[124] equals `2u8`
   - Expected: wire[125] equals `0u8`
   - Expected: decoded.payload_address equals `0x0c100000u64`
   - Expected: decoded.payload_capacity equals `0x01000000u64`
   - Expected: decoded.descriptor.payload_sha256 equals `TEST_HASH`
   - Expected: decoded.descriptor.state equals `DciCommitState.Committed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips the fixed packed record with commit in the final word")
val wire = dci_mailbox_wire_v1_encode(
    0x0c100000u64, 0x01000000u64,
    mailbox(DciCommitState.Committed, 2u64, 77u64),
    DCI_MAILBOX_WIRE_V1_COMMAND_BOOT, 0u32, 0u32).unwrap()
expect(wire.len()).to_equal(DCI_MAILBOX_WIRE_V1_SIZE)
expect(DCI_MAILBOX_WIRE_V1_COMMIT_OFFSET).to_equal(124)
expect(wire[124]).to_equal(2u8)
expect(wire[125]).to_equal(0u8)
val decoded = dci_mailbox_wire_v1_decode(wire).unwrap()
expect(decoded.payload_address).to_equal(0x0c100000u64)
expect(decoded.payload_capacity).to_equal(0x01000000u64)
expect(decoded.descriptor.payload_sha256).to_equal(TEST_HASH)
expect(decoded.descriptor.state).to_equal(DciCommitState.Committed)
```

</details>

#### rejects torn snapshots and a descriptor not committed last

- rejects torn snapshots and a descriptor not committed last
   - Expected: dci_mailbox_wire_v1_decode_stable(committed, torn).unwrap_err() equals `mailbox-wire-torn`
   - Expected: dci_mailbox_wire_v1_decode_stable(partial, partial).unwrap_err() equals `mailbox-wire-not-committed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects torn snapshots and a descriptor not committed last")
val committed = dci_mailbox_wire_v1_encode(
    0x0c100000u64, 0x01000000u64,
    mailbox(DciCommitState.Committed, 2u64, 77u64),
    DCI_MAILBOX_WIRE_V1_COMMAND_BOOT, 0u32, 0u32).unwrap()
var torn = dci_mailbox_wire_v1_encode(
    0x0c100000u64, 0x01000000u64,
    mailbox(DciCommitState.Committed, 3u64, 77u64),
    DCI_MAILBOX_WIRE_V1_COMMAND_BOOT, 0u32, 0u32).unwrap()
expect(dci_mailbox_wire_v1_decode_stable(committed, torn).unwrap_err()).to_equal("mailbox-wire-torn")

val partial = dci_mailbox_wire_v1_encode(
    0x0c100000u64, 0x01000000u64,
    mailbox(DciCommitState.PayloadWritten, 2u64, 77u64),
    DCI_MAILBOX_WIRE_V1_COMMAND_BOOT, 0u32, 0u32).unwrap()
expect(dci_mailbox_wire_v1_decode_stable(partial, partial).unwrap_err()).to_equal("mailbox-wire-not-committed")
```

</details>

#### rejects bad magic, reserved bytes, command, and payload bounds

- rejects bad magic, reserved bytes, command, and payload bounds
   - Expected: dci_mailbox_wire_v1_decode(bad_magic).unwrap_err() equals `mailbox-wire-magic`
   - Expected: dci_mailbox_wire_v1_decode(bad_reserved).unwrap_err() equals `mailbox-wire-reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects bad magic, reserved bytes, command, and payload bounds")
val good = dci_mailbox_wire_v1_encode(
    0x0c100000u64, 0x01000000u64,
    mailbox(DciCommitState.Committed, 2u64, 77u64),
    DCI_MAILBOX_WIRE_V1_COMMAND_BOOT, 0u32, 0u32).unwrap()
var bad_magic = good
bad_magic[0] = 0u8
expect(dci_mailbox_wire_v1_decode(bad_magic).unwrap_err()).to_equal("mailbox-wire-magic")
var bad_reserved = good
bad_reserved[100] = 1u8
expect(dci_mailbox_wire_v1_decode(bad_reserved).unwrap_err()).to_equal("mailbox-wire-reserved")
expect(dci_mailbox_wire_v1_encode(
    0x0c100001u64, 0x01000000u64,
    mailbox(DciCommitState.Committed, 2u64, 77u64),
    DCI_MAILBOX_WIRE_V1_COMMAND_BOOT, 0u32, 0u32).unwrap_err()).to_equal("mailbox-wire-payload-range")
```

</details>

### UP2 DCI physical ELF plan

#### parses p_paddr and zero-fill size from an x86-64 ELF

- parses p_paddr and zero-fill size from an x86-64 ELF
   - Expected: parsed.is_ok() is true
   - Expected: plan.entry equals `0x08000000u64`
   - Expected: plan.segments[0].physical_address equals `0x08000000u64`
   - Expected: plan.segments[0].file_size equals `1u64`
   - Expected: plan.segments[0].memory_size equals `8u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("parses p_paddr and zero-fill size from an x86-64 ELF")
val parsed = dci_parse_x86_64_elf(minimal_physical_elf())
expect(parsed.is_ok()).to_equal(true)
val plan = parsed.unwrap()
expect(plan.entry).to_equal(0x08000000u64)
expect(plan.segments[0].physical_address).to_equal(0x08000000u64)
expect(plan.segments[0].file_size).to_equal(1u64)
expect(plan.segments[0].memory_size).to_equal(8u64)
```

</details>

#### rejects malformed and truncated ELF input

- rejects malformed and truncated ELF input
   - Expected: dci_parse_x86_64_elf([0u8]).is_err() is true
   - Expected: dci_parse_x86_64_elf(bad).unwrap_err() equals `elf-magic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects malformed and truncated ELF input")
expect(dci_parse_x86_64_elf([0u8]).is_err()).to_equal(true)
var bad = minimal_physical_elf()
bad[0] = 0u8
expect(dci_parse_x86_64_elf(bad).unwrap_err()).to_equal("elf-magic")
```

</details>

#### admits the exact current UP2 three-segment physical plan

- admits the exact current UP2 three-segment physical plan
   - Expected: result.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits the exact current UP2 three-segment physical plan")
val result = dci_admit_load_plan(UP2_IMAGE_SIZE, up2_plan(), allowed_ram())
expect(result.accepted).to_equal(true)
```

</details>

#### rejects W plus X and an entry outside executable file bytes

- rejects W plus X and an entry outside executable file bytes
   - Expected: dci_admit_load_plan(UP2_IMAGE_SIZE, wx, allowed_ram()).reason equals `load-write-execute`
   - Expected: dci_admit_load_plan(UP2_IMAGE_SIZE, bad_entry, allowed_ram()).reason equals `load-entry-not-executable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects W plus X and an entry outside executable file bytes")
var wx = up2_plan()
wx.segments[0].flags = 7u32
expect(dci_admit_load_plan(UP2_IMAGE_SIZE, wx, allowed_ram()).reason).to_equal("load-write-execute")
var bad_entry = up2_plan()
bad_entry.entry = 0x08004fffu64
expect(dci_admit_load_plan(UP2_IMAGE_SIZE, bad_entry, allowed_ram()).reason).to_equal("load-entry-not-executable")
```

</details>

#### rejects file truncation, overlap, and non-allowlisted RAM

- rejects file truncation, overlap, and non-allowlisted RAM
   - Expected: dci_admit_load_plan(UP2_IMAGE_SIZE, truncated, allowed_ram()).reason equals `load-file-range`
   - Expected: dci_admit_load_plan(UP2_IMAGE_SIZE, overlap, allowed_ram()).reason equals `load-segment-overlap`
   - Expected: dci_admit_load_plan(UP2_IMAGE_SIZE, up2_plan(), [DciMemoryRange(start: 0x10000000u64, size: 0x1000u64)]).reason equals `load-memory-not-allowed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects file truncation, overlap, and non-allowlisted RAM")
var truncated = up2_plan()
truncated.segments[2].file_offset = 300000u64
expect(dci_admit_load_plan(UP2_IMAGE_SIZE, truncated, allowed_ram()).reason).to_equal("load-file-range")
var overlap = up2_plan()
overlap.segments[1].physical_address = 0x08004000u64
overlap.segments[1].align = 1u64
expect(dci_admit_load_plan(UP2_IMAGE_SIZE, overlap, allowed_ram()).reason).to_equal("load-segment-overlap")
expect(dci_admit_load_plan(UP2_IMAGE_SIZE, up2_plan(), [DciMemoryRange(start: 0x10000000u64, size: 0x1000u64)]).reason).to_equal("load-memory-not-allowed")
```

</details>

### UP2 DCI-staged storage admission

#### admits an exact idle identity with its bound challenge

- admits an exact idle identity with its bound challenge
   - Expected: result.accepted is true
   - Expected: challenge.starts_with("UP2-STORAGE-WRITE:") is true
   - Expected: challenge.len() < 256 is true
   - Expected: challenge does not contain `disk.serial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits an exact idle identity with its bound challenge")
val disk = identity(false, false, false)
val challenge = dci_storage_confirmation(disk, 1048576u64, 268435456u64, TEST_HASH)
val result = dci_admit_storage_write(storage_write(disk, disk, challenge, true))
expect(result.accepted).to_equal(true)
expect(challenge.starts_with("UP2-STORAGE-WRITE:")).to_equal(true)
expect(challenge.len() < 256).to_equal(true)
expect(challenge.contains(disk.serial)).to_equal(false)
```

</details>

#### rejects missing authorization, system media, busy media, and wrong challenge

- rejects missing authorization, system media, busy media, and wrong challenge
   - Expected: dci_admit_storage_write(storage_write(disk, disk, challenge, false)).reason equals `storage-persistent-not-authorized`
   - Expected: dci_admit_storage_write(storage_write(root, root, "", true)).reason equals `storage-system-device`
   - Expected: dci_admit_storage_write(storage_write(mounted, mounted, "", true)).reason equals `storage-device-busy`
   - Expected: dci_admit_storage_write(storage_write(disk, disk, "wrong", true)).reason equals `storage-confirmation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects missing authorization, system media, busy media, and wrong challenge")
val disk = identity(false, false, false)
val challenge = dci_storage_confirmation(disk, 1048576u64, 268435456u64, TEST_HASH)
expect(dci_admit_storage_write(storage_write(disk, disk, challenge, false)).reason).to_equal("storage-persistent-not-authorized")
val root = identity(true, false, false)
expect(dci_admit_storage_write(storage_write(root, root, "", true)).reason).to_equal("storage-system-device")
val mounted = identity(false, true, false)
expect(dci_admit_storage_write(storage_write(mounted, mounted, "", true)).reason).to_equal("storage-device-busy")
expect(dci_admit_storage_write(storage_write(disk, disk, "wrong", true)).reason).to_equal("storage-confirmation")
```

</details>

#### rejects identity changes and ranges beyond capacity

- rejects identity changes and ranges beyond capacity
   - Expected: dci_admit_storage_write(storage_write(disk, changed, "", true)).reason equals `storage-identity-mismatch`
   - Expected: dci_admit_storage_write(request).reason equals `storage-write-range`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects identity changes and ranges beyond capacity")
val disk = identity(false, false, false)
var changed = identity(false, false, false)
changed.serial = "OTHER"
expect(dci_admit_storage_write(storage_write(disk, changed, "", true)).reason).to_equal("storage-identity-mismatch")
var request = storage_write(disk, disk, "", true)
request.byte_start = disk.capacity - 1u64
request.byte_length = 2u64
request.image_size = 2u64
expect(dci_admit_storage_write(request).reason).to_equal("storage-write-range")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering UP2 DCI mailbox admission, UP2 DCI mailbox wire v1, UP2 DCI physical ELF plan, UP2 DCI-staged storage admission.
- UP2 DCI mailbox admission
- UP2 DCI mailbox wire v1
- UP2 DCI physical ELF plan
- UP2 DCI-staged storage admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `b396be843d7c6d881395dcd8d5754060059a7920132431c229b6b78cb9ac9771`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b396be843d7c6d881395dcd8d5754060059a7920132431c229b6b78cb9ac9771`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b396be843d7c6d881395dcd8d5754060059a7920132431c229b6b78cb9ac9771`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a fresh committed exact-digest payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects partial commit, replay, nonce mismatch, and digest mismatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/arch/x86_64/up_squared/dci_mailbox_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips the fixed packed record with commit in the final word' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
