# Qrb2210 Pcm Dma Audio Provider Specification

> Tests covering QRB2210 physical PCM DMA audio provider.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Pcm Dma Audio Provider Specification

## Scenarios

### QRB2210 physical PCM DMA audio provider

#### requires physical boot device owner generation and bounded DMA rings

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires physical boot device owner generation and bounded DMA rings


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires physical boot device owner generation and bounded DMA rings")
expect(qrb2210_pcm_dma_identity_ready(identity())).to_be(true)
var hosted = identity()
hosted.physical_device = false
expect(qrb2210_pcm_dma_identity_ready(hosted)).to_be(false)
var no_owner = identity()
no_owner.kernel_owner_handle = 0u64
expect(qrb2210_pcm_dma_identity_ready(no_owner)).to_be(false)
var no_irq = identity()
no_irq.irq_line = 0
expect(qrb2210_pcm_dma_identity_ready(no_irq)).to_be(false)
var no_ring = identity()
no_ring.completion_ring_handle = 0u64
expect(qrb2210_pcm_dma_identity_ready(no_ring)).to_be(false)
var no_pool = identity()
no_pool.dma_pool_handle = 0u64
expect(qrb2210_pcm_dma_identity_ready(no_pool)).to_be(false)
var bad_generation = identity()
bad_generation.device.driver_generation = 0
expect(qrb2210_pcm_dma_identity_ready(bad_generation)).to_be(false)
var stale_boot = identity()
stale_boot.device.boot_id = ""
expect(qrb2210_pcm_dma_identity_ready(stale_boot)).to_be(false)
```

</details>

#### accepts bounded aligned non-silent s16le and rejects silence or bad geometry

- accepts bounded aligned non-silent s16le and rejects silence or bad geometry


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts bounded aligned non-silent s16le and rejects silence or bad geometry")
val samples: [i64] = [100, -100, 200, -200]
expect(qrb2210_pcm_payload_admissible(identity(), samples, 2, 48000)).to_be(true)
expect(qrb2210_pcm_payload_admissible(identity(), [0, 0, 0, 0], 2, 48000)).to_be(false)
expect(qrb2210_pcm_payload_admissible(identity(), [1, 2, 3], 2, 48000)).to_be(false)
expect(qrb2210_pcm_payload_admissible(identity(), [32768, 0], 2, 48000)).to_be(false)
expect(qrb2210_pcm_payload_admissible(identity(), [-32769, 0], 2, 48000)).to_be(false)
expect(qrb2210_pcm_payload_admissible(
    identity(), [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
    2, 48000)).to_be(false)
expect(qrb2210_pcm_payload_admissible(identity(), samples, 1, 48000)).to_be(false)
expect(qrb2210_pcm_payload_admissible(identity(), samples, 2, 44100)).to_be(false)
var wrong_period = identity()
wrong_period.period_frames = 4
wrong_period.max_frames = 8
expect(qrb2210_pcm_payload_admissible(wrong_period, samples, 2, 48000)).to_be(false)
```

</details>

#### binds submission to exact boot owner ring buffer frame sequence and PCM

- binds submission to exact boot owner ring buffer frame sequence and PCM


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("binds submission to exact boot owner ring buffer frame sequence and PCM")
val samples: [i64] = [100, -100, 200, -200]
val accepted = submit(samples)
expect(qrb2210_pcm_submit_correlates(identity(), accepted, samples, 6)).to_be(true)
expect(qrb2210_pcm_submit_correlates(identity(), accepted, samples, 7)).to_be(false)
var wrong_boot = accepted
wrong_boot.device = device("boot-previous")
expect(qrb2210_pcm_submit_correlates(identity(), wrong_boot, samples, 6)).to_be(false)
var wrong_ring = accepted
wrong_ring.submit_ring_handle = 99u64
expect(qrb2210_pcm_submit_correlates(identity(), wrong_ring, samples, 6)).to_be(false)
var wrong_owner = accepted
wrong_owner.kernel_owner_handle = 99u64
expect(qrb2210_pcm_submit_correlates(identity(), wrong_owner, samples, 6)).to_be(false)
var wrong_pool = accepted
wrong_pool.dma_pool_handle = 99u64
expect(qrb2210_pcm_submit_correlates(identity(), wrong_pool, samples, 6)).to_be(false)
var no_buffer = accepted
no_buffer.dma_buffer_handle = 0u64
expect(qrb2210_pcm_submit_correlates(identity(), no_buffer, samples, 6)).to_be(false)
var wrong_frame = accepted
wrong_frame.first_frame_id = 0
expect(qrb2210_pcm_submit_correlates(identity(), wrong_frame, samples, 6)).to_be(false)
var wrong_frame_count = accepted
wrong_frame_count.frame_count = 4
expect(qrb2210_pcm_submit_correlates(identity(), wrong_frame_count, samples, 6)).to_be(false)
var wrong_sample_count = accepted
wrong_sample_count.sample_count = 2
expect(qrb2210_pcm_submit_correlates(identity(), wrong_sample_count, samples, 6)).to_be(false)
var wrong_pcm = accepted
wrong_pcm.pcm_checksum = wrong_pcm.pcm_checksum + 1
expect(qrb2210_pcm_submit_correlates(identity(), wrong_pcm, samples, 6)).to_be(false)
```

</details>

#### accepts one exact hardware completion and rejects replay or cross-boot evidence

- accepts one exact hardware completion and rejects replay or cross-boot evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts one exact hardware completion and rejects replay or cross-boot evidence")
val samples: [i64] = [100, -100, 200, -200]
val accepted = submit(samples)
val done = completion(samples)
expect(qrb2210_pcm_completion_correlates(identity(), accepted, done, 8, 10)).to_be(true)
expect(qrb2210_pcm_completion_correlates(identity(), accepted, done, 9, 10)).to_be(false)
expect(qrb2210_pcm_completion_correlates(identity(), accepted, done, 8, 11)).to_be(false)
var stale_boot = done
stale_boot.device = device("boot-previous")
expect(qrb2210_pcm_completion_correlates(identity(), accepted, stale_boot, 8, 10)).to_be(false)
var wrong_buffer = done
wrong_buffer.dma_buffer_handle = 99u64
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_buffer, 8, 10)).to_be(false)
var wrong_owner = done
wrong_owner.kernel_owner_handle = 99u64
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_owner, 8, 10)).to_be(false)
var wrong_ring = done
wrong_ring.completion_ring_handle = 99u64
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_ring, 8, 10)).to_be(false)
var wrong_frame = done
wrong_frame.completed_frame_count = 1
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_frame, 8, 10)).to_be(false)
var wrong_first_frame = done
wrong_first_frame.first_frame_id = 102
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_first_frame, 8, 10)).to_be(false)
var wrong_samples = done
wrong_samples.completed_sample_count = 2
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_samples, 8, 10)).to_be(false)
var wrong_checksum = done
wrong_checksum.pcm_checksum = wrong_checksum.pcm_checksum + 1
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_checksum, 8, 10)).to_be(false)
var wrong_submission = done
wrong_submission.submission_id = 62
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_submission, 8, 10)).to_be(false)
var wrong_submit_sequence = done
wrong_submit_sequence.submit_sequence = 8
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_submit_sequence, 8, 10)).to_be(false)
var wrong_irq = done
wrong_irq.irq_line = 42
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_irq, 8, 10)).to_be(false)
var wrong_generation = done
wrong_generation.driver_generation = 4
expect(qrb2210_pcm_completion_correlates(identity(), accepted, wrong_generation, 8, 10)).to_be(false)
var no_irq = done
no_irq.interrupt_timestamp_ns = 0u64
expect(qrb2210_pcm_completion_correlates(identity(), accepted, no_irq, 8, 10)).to_be(false)
var no_completion = done
no_completion.completion_id = 0
expect(qrb2210_pcm_completion_correlates(identity(), accepted, no_completion, 8, 10)).to_be(false)
```

</details>

#### has no hosted QEMU transcript or fabricated completion path

- has no hosted QEMU transcript or fabricated completion path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("has no hosted QEMU transcript or fabricated completion path")
val source = file_read_text(PROVIDER)
expect(source).to_contain("kernel.submit_pcm_dma(samples, channels, sample_rate_hz)")
expect(source).to_contain("kernel.poll_pcm_dma_completion(submission_id)")
expect(source).to_contain("UNO_Q_DESKTOP_STATUS_PORT_UNAVAILABLE")
expect(source).to_contain("self.active_submission_id != 0")
expect(source).to_contain("self.active_submission_id = -1")
expect(source).to_contain("self.active_submission_id = 0")
expect(source.contains("rt_process")).to_be(false)
expect(source.contains("virtio")).to_be(false)
expect(source.contains("qemu")).to_be(false)
expect(source.contains("transcript")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QRB2210 physical PCM DMA audio provider.
- QRB2210 physical PCM DMA audio provider

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
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1adcf0c3129a1b452f3bfa26b7d3a62c405db9f229d65ab55492826905fac4e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1adcf0c3129a1b452f3bfa26b7d3a62c405db9f229d65ab55492826905fac4e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1adcf0c3129a1b452f3bfa26b7d3a62c405db9f229d65ab55492826905fac4e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires physical boot device owner generation and bounded DMA rings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts bounded aligned non-silent s16le and rejects silence or bad geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_pcm_dma_audio_provider_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds submission to exact boot owner ring buffer frame sequence and PCM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
