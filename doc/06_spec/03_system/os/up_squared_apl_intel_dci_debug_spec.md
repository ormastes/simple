# UP Squared Apollo Lake DCI-safe load and storage policy

> Executable contract coverage for REQ-006, REQ-007, REQ-009, and the admission

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UP Squared Apollo Lake DCI-safe load and storage policy

Executable contract coverage for REQ-006, REQ-007, REQ-009, and the admission

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/up_squared_apl_intel_dci_debug_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Executable contract coverage for REQ-006, REQ-007, REQ-009, and the admission
portion of REQ-010, plus REQ-013 free post-boot RAM access. Physical DCI
discovery, boot, and storage readback remain
hardware evidence gates and are not represented as passing assertions here.

## Scenarios

### UP2 DCI RAM boot admission

#### accepts only a final replay-safe mailbox and the reviewed ELF layout

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only a final replay-safe mailbox and the reviewed ELF layout
- Stage payload bytes before publishing the final descriptor.
   - Expected: partial.accepted is false
   - Expected: partial.reason equals `mailbox-not-committed`
- Commit the descriptor with a fresh generation, nonce, and hash.
   - Expected: committed.accepted is true
- Admit all physical ELF segments inside the published RAM window.
   - Expected: admitted.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts only a final replay-safe mailbox and the reviewed ELF layout")
val partial = dci_admit_mailbox(
    descriptor(DciCommitState.PayloadWritten, 2u64),
    1u64, 41u64, IMAGE_SIZE, IMAGE_HASH
)
expect(partial.accepted).to_equal(false)
expect(partial.reason).to_equal("mailbox-not-committed")

val committed = dci_admit_mailbox(
    descriptor(DciCommitState.Committed, 2u64),
    1u64, 41u64, IMAGE_SIZE, IMAGE_HASH
)
expect(committed.accepted).to_equal(true)

val admitted = dci_admit_load_plan(
    IMAGE_SIZE,
    image_plan(),
    [DciMemoryRange(start: 0x08000000u64, size: 0x03000000u64)]
)
expect(admitted.accepted).to_equal(true)
```

</details>

### UP2 target-side storage admission

#### binds authorization to exact idle device identity and byte range

- binds authorization to exact idle device identity and byte range
- Reject a device whose exact serial changed after enumeration.
   - Expected: mismatch.reason equals `storage-identity-mismatch`
- Reject mounted media even when its identity and challenge match.
   - Expected: busy_result.reason equals `storage-device-busy`
- Admit the exact idle device only with persistent authorization.
   - Expected: accepted.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds authorization to exact idle device identity and byte range")
val observed = disk("UP2-TEST-001", false)
val challenge = dci_storage_confirmation(
    observed, 1048576u64, 268435456u64, IMAGE_HASH
)

val changed = disk("OTHER", false)
val mismatch = dci_admit_storage_write(DciStorageWrite(
    observed: observed, expected: changed,
    byte_start: 1048576u64, byte_length: 268435456u64,
    image_size: 268435456u64, image_sha256: IMAGE_HASH,
    confirmation: challenge, persistent_allowed: true
))
expect(mismatch.reason).to_equal("storage-identity-mismatch")

val busy = disk("UP2-TEST-001", true)
val busy_challenge = dci_storage_confirmation(
    busy, 1048576u64, 268435456u64, IMAGE_HASH
)
val busy_result = dci_admit_storage_write(DciStorageWrite(
    observed: busy, expected: busy,
    byte_start: 1048576u64, byte_length: 268435456u64,
    image_size: 268435456u64, image_sha256: IMAGE_HASH,
    confirmation: busy_challenge, persistent_allowed: true
))
expect(busy_result.reason).to_equal("storage-device-busy")

val accepted = dci_admit_storage_write(DciStorageWrite(
    observed: observed, expected: observed,
    byte_start: 1048576u64, byte_length: 268435456u64,
    image_size: 268435456u64, image_sha256: IMAGE_HASH,
    confirmation: challenge, persistent_allowed: true
))
expect(accepted.accepted).to_equal(true)
```

</details>

#### writes ordered image chunks and requires flush plus exact full readback

**Manual warnings:**
- unused step metadata: Cross the durability boundary and hash every byte from a fresh view. (expected a following executable manual step)


- writes ordered image chunks and requires flush plus exact full readback
- Create an isolated device and an aligned hash-bound image plan.
- Commit two ordered, independently hashed staging chunks.
   - Expected: storage_image_flush(device, plan, next_offset).unwrap() is true
- Cross the durability boundary and hash every byte from a fresh view.


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes ordered image chunks and requires flush plus exact full readback")
val memory = MemBlockDevice.new(8u64, 512u32)
val device: BlockDevice = memory
val plan = storage_image_plan(
    512u32, 8u64, 512u64, 1024u64, ZERO_IMAGE_HASH).unwrap()
var next_offset: u64 = 0u64

next_offset = storage_image_write_chunk(
    device, plan, next_offset, zero_sector(), ZERO_SECTOR_HASH).unwrap()
next_offset = storage_image_write_chunk(
    device, plan, next_offset, zero_sector(), ZERO_SECTOR_HASH).unwrap()

expect(storage_image_flush(device, plan, next_offset).unwrap()).to_equal(true)
val fresh_device: BlockDevice = memory
val proof = storage_image_verify_readback(fresh_device, plan).unwrap()
expect(proof).to_contain("sha256=" + ZERO_IMAGE_HASH)
expect(proof).to_contain("flush=pass fresh_readback=pass")
```

</details>

### UP2 free post-boot RAM loading

#### accepts only framed operations inside the loader-owned staging range

- accepts only framed operations inside the loader-owned staging range
- Establish an RSP session without advertising false run control.
   - Expected: supported.response equals `PacketSize=1000`
   - Expected: up2_rsp_plan("g").response equals ``
   - Expected: up2_rsp_plan("c").response equals ``
- Decode one exact write inside the dedicated staging segment.
   - Expected: decoded.is_ok() is true
   - Expected: write.operation equals `Up2RspOperation.WriteMemory`
   - Expected: write.data equals `[0x53u8, 0x49u8, 0x4du8, 0x50u8]`
- Reject the same write outside loader-owned RAM.
   - Expected: outside.operation equals `Up2RspOperation.Reply`
   - Expected: outside.response equals `E02`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts only framed operations inside the loader-owned staging range")
val supported = up2_rsp_plan("qSupported:multiprocess+")
expect(supported.response).to_equal("PacketSize=1000")
expect(up2_rsp_plan("g").response).to_equal("")
expect(up2_rsp_plan("c").response).to_equal("")

val write_frame = up2_rsp_frame("M0a000000,4:53494d50")
val decoded = up2_rsp_decode_frame(write_frame)
expect(decoded.is_ok()).to_equal(true)
val write = up2_rsp_plan(decoded.unwrap())
expect(write.operation).to_equal(Up2RspOperation.WriteMemory)
expect(write.data).to_equal([0x53u8, 0x49u8, 0x4du8, 0x50u8])

val outside = up2_rsp_plan("M09000000,4:53494d50")
expect(outside.operation).to_equal(Up2RspOperation.Reply)
expect(outside.response).to_equal("E02")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-006`
- `REQ-007`
- `REQ-009`
- `REQ-010`
- `REQ-013`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e19ebe130e1f22f4cd2b5b7fa92463ce9eee94e033d618ada4ae5e8f0e708b64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e19ebe130e1f22f4cd2b5b7fa92463ce9eee94e033d618ada4ae5e8f0e708b64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e19ebe130e1f22f4cd2b5b7fa92463ce9eee94e033d618ada4ae5e8f0e708b64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/up_squared_apl_intel_dci_debug_spec.spl
mirror: doc/06_spec/03_system/os/up_squared_apl_intel_dci_debug_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/up_squared_apl_intel_dci_debug_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/up_squared_apl_intel_dci_debug_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/up_squared_apl_intel_dci_debug_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only a final replay-safe mailbox and the reviewed ELF layout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/up_squared_apl_intel_dci_debug_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds authorization to exact idle device identity and byte range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/up_squared_apl_intel_dci_debug_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes ordered image chunks and requires flush plus exact full readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
