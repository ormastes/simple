# Virtio Snd Mmio Contract Specification

> Tests covering VirtIO sound MMIO transport contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Virtio Snd Mmio Contract Specification

## Scenarios

### VirtIO sound MMIO transport contracts

#### accepts bounded power-of-two queue memory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts bounded power-of-two queue memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts bounded power-of-two queue memory")
val queue = VirtioSndQueueMemory(desc_cpu: 0x4000u64, avail_cpu: 0x5000u64, used_cpu: 0x6000u64, desc: 0x1000u64, avail: 0x2000u64, used: 0x3000u64, size: 64u16)
expect(virtio_snd_queue_memory_valid(queue)).to_be(true)
```

</details>

#### rejects aliased or non-power-of-two queue layouts

- rejects aliased or non-power-of-two queue layouts


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects aliased or non-power-of-two queue layouts")
val missing = VirtioSndQueueMemory(desc_cpu: 0x4000u64, avail_cpu: 0x5000u64, used_cpu: 0x6000u64, desc: 0u64, avail: 0x2000u64, used: 0x3000u64, size: 64u16)
val odd = VirtioSndQueueMemory(desc_cpu: 0x4000u64, avail_cpu: 0x5000u64, used_cpu: 0x6000u64, desc: 0x1000u64, avail: 0x2000u64, used: 0x3000u64, size: 63u16)
expect(virtio_snd_queue_memory_valid(missing)).to_be(false)
expect(virtio_snd_queue_memory_valid(odd)).to_be(false)
```

</details>

#### bounds descriptors and rejects zero-length DMA

- bounds descriptors and rejects zero-length DMA


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds descriptors and rejects zero-length DMA")
expect(virtio_snd_descriptor_valid(64u16, 63u16, 4096u32)).to_be(true)
expect(virtio_snd_descriptor_valid(64u16, 64u16, 4096u32)).to_be(false)
expect(virtio_snd_descriptor_valid(64u16, 1u16, 0u32)).to_be(false)
```

</details>

#### reserves complete control and PCM descriptor chains

- reserves complete control and PCM descriptor chains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reserves complete control and PCM descriptor chains")
expect(virtio_snd_chain_valid(64u16, 62u16, 2u16)).to_be(true)
expect(virtio_snd_chain_valid(64u16, 62u16, 3u16)).to_be(false)
expect(virtio_snd_chain_valid(64u16, 0u16, 0u16)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VirtIO sound MMIO transport contracts.
- VirtIO sound MMIO transport contracts

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2f08097503df4e9d6f789a0aaebe85796014ac5fd5bd2f9c5c3438fc85d4d697`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f08097503df4e9d6f789a0aaebe85796014ac5fd5bd2f9c5c3438fc85d4d697`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f08097503df4e9d6f789a0aaebe85796014ac5fd5bd2f9c5c3438fc85d4d697`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts bounded power-of-two queue memory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects aliased or non-power-of-two queue layouts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/audio/virtio_snd_mmio_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds descriptors and rejects zero-length DMA' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
