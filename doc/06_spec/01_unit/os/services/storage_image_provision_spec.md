# Storage Image Provision Specification

> Tests covering host-neutral block image provision planning, host-neutral block image write and durable readback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Image Provision Specification

## Scenarios

### host-neutral block image provision planning

#### accepts one aligned bounded image and rejects unsafe geometry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts one aligned bounded image and rejects unsafe geometry
   - Expected: plan.is_ok() is true
   - Expected: plan.unwrap().byte_start equals `512u64`
   - Expected: storage_image_plan(0u32, 8u64, 0u64, 512u64, ZERO_512_SHA256).unwrap_err() equals `storage-image-device-geometry`
   - Expected: storage_image_plan(512u32, 8u64, 1u64, 512u64, ZERO_512_SHA256).unwrap_err() equals `storage-image-sector-alignment`
   - Expected: storage_image_plan(512u32, 8u64, 4096u64, 512u64, ZERO_512_SHA256).unwrap_err() equals `storage-image-range`
   - Expected: storage_image_plan(512u32, 8u64, 0u64, 512u64, "bad").unwrap_err() equals `storage-image-digest-format`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts one aligned bounded image and rejects unsafe geometry")
val plan = storage_image_plan(512u32, 8u64, 512u64, 1024u64, ZERO_1024_SHA256)
expect(plan.is_ok()).to_equal(true)
expect(plan.unwrap().byte_start).to_equal(512u64)
expect(storage_image_plan(0u32, 8u64, 0u64, 512u64, ZERO_512_SHA256).unwrap_err()).to_equal("storage-image-device-geometry")
expect(storage_image_plan(512u32, 8u64, 1u64, 512u64, ZERO_512_SHA256).unwrap_err()).to_equal("storage-image-sector-alignment")
expect(storage_image_plan(512u32, 8u64, 4096u64, 512u64, ZERO_512_SHA256).unwrap_err()).to_equal("storage-image-range")
expect(storage_image_plan(512u32, 8u64, 0u64, 512u64, "bad").unwrap_err()).to_equal("storage-image-digest-format")
```

</details>

#### hashes a complete sector with the standard SHA-256 value

- hashes a complete sector with the standard SHA-256 value
   - Expected: storage_sha256_hex(_zero_bytes(512)).unwrap() equals `ZERO_512_SHA256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hashes a complete sector with the standard SHA-256 value")
expect(storage_sha256_hex(_zero_bytes(512)).unwrap()).to_equal(ZERO_512_SHA256)
```

</details>

### host-neutral block image write and durable readback

#### writes ordered chunks, flushes, and hashes exact fresh reads

- writes ordered chunks, flushes, and hashes exact fresh reads
   - Expected: next_offset equals `512u64`
   - Expected: storage_image_flush(dev, plan, next_offset).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes ordered chunks, flushes, and hashes exact fresh reads")
val mem = MemBlockDevice.new(8u64, 512u32)
val dev: BlockDevice = mem
val plan = storage_image_plan(512u32, 8u64, 512u64, 1024u64, ZERO_1024_SHA256).unwrap()
var next_offset = storage_image_write_chunk(
    dev, plan, 0u64, _zero_bytes(512), ZERO_512_SHA256).unwrap()
expect(next_offset).to_equal(512u64)
next_offset = storage_image_write_chunk(
    dev, plan, next_offset, _zero_bytes(512), ZERO_512_SHA256).unwrap()
expect(storage_image_flush(dev, plan, next_offset).unwrap()).to_equal(true)
val fresh_dev: BlockDevice = mem
val proof = storage_image_verify_readback(fresh_dev, plan).unwrap()
expect(proof).to_contain("sha256=" + ZERO_1024_SHA256)
expect(proof).to_contain("flush=pass fresh_readback=pass")
```

</details>

#### rejects a mismatched chunk before writing and incomplete finalization

- rejects a mismatched chunk before writing and incomplete finalization
   - Expected: storage_image_write_chunk(dev, plan, 0u64, _zero_bytes(512), ZERO_1024_SHA256).unwrap_err() equals `storage-image-chunk-digest-mismatch`
   - Expected: storage_image_flush(dev, plan, 0u64).unwrap_err() equals `storage-image-incomplete`
   - Expected: dev.read_sector(0u64).unwrap() equals `_zero_bytes(512)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a mismatched chunk before writing and incomplete finalization")
val mem = MemBlockDevice.new(8u64, 512u32)
val dev: BlockDevice = mem
val plan = storage_image_plan(512u32, 8u64, 0u64, 1024u64, ZERO_1024_SHA256).unwrap()
expect(storage_image_write_chunk(dev, plan, 0u64, _zero_bytes(512), ZERO_1024_SHA256).unwrap_err()).to_equal("storage-image-chunk-digest-mismatch")
expect(storage_image_flush(dev, plan, 0u64).unwrap_err()).to_equal("storage-image-incomplete")
expect(dev.read_sector(0u64).unwrap()).to_equal(_zero_bytes(512))
```

</details>

#### detects media corruption during full readback

- detects media corruption during full readback
   - Expected: storage_image_flush(dev, plan, next_offset).unwrap() is true
   - Expected: storage_image_verify_readback(dev, plan).unwrap_err() equals `storage-image-readback-digest-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects media corruption during full readback")
val mem = MemBlockDevice.new(8u64, 512u32)
val dev: BlockDevice = mem
val plan = storage_image_plan(512u32, 8u64, 0u64, 512u64, ZERO_512_SHA256).unwrap()
val next_offset = storage_image_write_chunk(
    dev, plan, 0u64, _zero_bytes(512), ZERO_512_SHA256).unwrap()
expect(storage_image_flush(dev, plan, next_offset).unwrap()).to_equal(true)
dev.write_sector(0u64, _one_bytes(512))
expect(storage_image_verify_readback(dev, plan).unwrap_err()).to_equal("storage-image-readback-digest-mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/storage_image_provision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host-neutral block image provision planning, host-neutral block image write and durable readback.
- host-neutral block image provision planning
- host-neutral block image write and durable readback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4ae0776219cdb30267a917db7508f6ceb60b6c113cfffff8d0f37c79cc780f53`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ae0776219cdb30267a917db7508f6ceb60b6c113cfffff8d0f37c79cc780f53`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ae0776219cdb30267a917db7508f6ceb60b6c113cfffff8d0f37c79cc780f53`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/services/storage_image_provision_spec.spl
mirror: doc/06_spec/01_unit/os/services/storage_image_provision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/storage_image_provision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/storage_image_provision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/storage_image_provision_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts one aligned bounded image and rejects unsafe geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/storage_image_provision_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hashes a complete sector with the standard SHA-256 value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/storage_image_provision_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes ordered chunks, flushes, and hashes exact fresh reads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
