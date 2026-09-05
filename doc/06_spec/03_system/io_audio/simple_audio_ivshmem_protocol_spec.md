# simple_audio_ivshmem_protocol_spec

> Audio ivshmem wire fails closed and admits only correlated device readback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_ivshmem_protocol_spec

Audio ivshmem wire fails closed and admits only correlated device readback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_ivshmem_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Audio ivshmem wire fails closed and admits only correlated device readback.

## Scenarios

### SimpleOS audio ivshmem protocol

#### validates the exact versioned bounded wire header

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates the exact versioned bounded wire header
   - Expected: simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 8, slot_bytes: 256)) equals `ready`
   - Expected: simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: 0, version: 1, capacity: 8, slot_bytes: 256)) equals `bad-magic`
   - Expected: simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 2, capacity: 8, slot_bytes: 256)) equals `bad-version`
   - Expected: simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 1, slot_bytes: 256)) equals `bad-capacity`
   - Expected: simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 9, slot_bytes: 256)) equals `bad-capacity`
   - Expected: simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 8, slot_bytes: 128)) equals `bad-slot-size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates the exact versioned bounded wire header")
expect(simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 8, slot_bytes: 256))).to_equal("ready")
expect(simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: 0, version: 1, capacity: 8, slot_bytes: 256))).to_equal("bad-magic")
expect(simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 2, capacity: 8, slot_bytes: 256))).to_equal("bad-version")
expect(simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 1, slot_bytes: 256))).to_equal("bad-capacity")
expect(simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 9, slot_bytes: 256))).to_equal("bad-capacity")
expect(simple_audio_ivshmem_header_status(SimpleAudioIvshmemHeader(magic: SIMPLE_AUDIO_IVSHMEM_MAGIC, version: 1, capacity: 8, slot_bytes: 128))).to_equal("bad-slot-size")
```

</details>

#### bounds real Q15 payload and derives the exact convolution output size

- bounds real Q15 payload and derives the exact convolution output size
   - Expected: simple_audio_ivshmem_payload_status(4096, 128, 4223) equals `ready`
   - Expected: simple_audio_ivshmem_payload_status(0, 128, 127) equals `invalid-work`
   - Expected: simple_audio_ivshmem_payload_status(32769, 128, 32896) equals `payload-too-large`
   - Expected: simple_audio_ivshmem_payload_status(4096, 4097, 8192) equals `payload-too-large`
   - Expected: simple_audio_ivshmem_payload_status(4096, 128, 4224) equals `bad-output-size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bounds real Q15 payload and derives the exact convolution output size")
expect(simple_audio_ivshmem_payload_status(4096, 128, 4223)).to_equal("ready")
expect(simple_audio_ivshmem_payload_status(0, 128, 127)).to_equal("invalid-work")
expect(simple_audio_ivshmem_payload_status(32769, 128, 32896)).to_equal("payload-too-large")
expect(simple_audio_ivshmem_payload_status(4096, 4097, 8192)).to_equal("payload-too-large")
expect(simple_audio_ivshmem_payload_status(4096, 128, 4224)).to_equal("bad-output-size")
```

</details>

#### accepts only timely correlated remote host CUDA device readback

- accepts only timely correlated remote host CUDA device readback
   - Expected: simple_audio_ivshmem_completion_status(accepted, 3u64, 9u64, 1550u64, 1600u64) equals `accepted-device-result`
   - Expected: simple_audio_ivshmem_completion_status(accepted, 4u64, 9u64, 1550u64, 1600u64) equals `stale-generation`
   - Expected: simple_audio_ivshmem_completion_status(accepted, 3u64, 8u64, 1550u64, 1600u64) equals `correlation-mismatch`
   - Expected: simple_audio_ivshmem_completion_status(accepted, 3u64, 9u64, 1650u64, 1600u64) equals `late`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts only timely correlated remote host CUDA device readback")
val accepted = SimpleAudioIvshmemCompletion(state: SIMPLE_AUDIO_WIRE_STATE_COMPLETED, generation: 3u64, correlation_id: 9u64, provider: SIMPLE_AUDIO_WIRE_PROVIDER_REMOTE_HOST_CUDA, native_handle: 7, device_identity: 86, readback_checksum: 91, completed_ns: 1500u64, normalized_error_millionths: 5, readback_source: SIMPLE_AUDIO_WIRE_READBACK_DEVICE)
expect(simple_audio_ivshmem_completion_status(accepted, 3u64, 9u64, 1550u64, 1600u64)).to_equal("accepted-device-result")
expect(simple_audio_ivshmem_completion_status(accepted, 4u64, 9u64, 1550u64, 1600u64)).to_equal("stale-generation")
expect(simple_audio_ivshmem_completion_status(accepted, 3u64, 8u64, 1550u64, 1600u64)).to_equal("correlation-mismatch")
expect(simple_audio_ivshmem_completion_status(accepted, 3u64, 9u64, 1650u64, 1600u64)).to_equal("late")
```

</details>

#### rejects missing provenance readback parity and incomplete slots

- rejects missing provenance readback parity and incomplete slots
   - Expected: simple_audio_ivshmem_completion_status(pending, 1u64, 1u64, 50u64, 100u64) equals `pending`
   - Expected: simple_audio_ivshmem_completion_status(wrong_provider, 1u64, 1u64, 50u64, 100u64) equals `bad-provider`
   - Expected: simple_audio_ivshmem_completion_status(bad_parity, 1u64, 1u64, 50u64, 100u64) equals `parity-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects missing provenance readback parity and incomplete slots")
val pending = SimpleAudioIvshmemCompletion(state: SIMPLE_AUDIO_WIRE_STATE_PROCESSING, generation: 1u64, correlation_id: 1u64, provider: 0, native_handle: 0, device_identity: 0, readback_checksum: 0, completed_ns: 0u64, normalized_error_millionths: 0, readback_source: 0)
val wrong_provider = SimpleAudioIvshmemCompletion(state: SIMPLE_AUDIO_WIRE_STATE_COMPLETED, generation: 1u64, correlation_id: 1u64, provider: 2, native_handle: 1, device_identity: 1, readback_checksum: 1, completed_ns: 10u64, normalized_error_millionths: 0, readback_source: 1)
val bad_parity = SimpleAudioIvshmemCompletion(state: SIMPLE_AUDIO_WIRE_STATE_COMPLETED, generation: 1u64, correlation_id: 1u64, provider: 1, native_handle: 1, device_identity: 1, readback_checksum: 1, completed_ns: 10u64, normalized_error_millionths: 11, readback_source: 1)
expect(simple_audio_ivshmem_completion_status(pending, 1u64, 1u64, 50u64, 100u64)).to_equal("pending")
expect(simple_audio_ivshmem_completion_status(wrong_provider, 1u64, 1u64, 50u64, 100u64)).to_equal("bad-provider")
expect(simple_audio_ivshmem_completion_status(bad_parity, 1u64, 1u64, 50u64, 100u64)).to_equal("parity-failed")
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
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `79c59a491006bd0314d5f7a589cb30f661cd42a95937faffc367ec49215cf681`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `79c59a491006bd0314d5f7a589cb30f661cd42a95937faffc367ec49215cf681`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `79c59a491006bd0314d5f7a589cb30f661cd42a95937faffc367ec49215cf681`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_ivshmem_protocol_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_ivshmem_protocol_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_ivshmem_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_ivshmem_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_ivshmem_protocol_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 4 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_ivshmem_protocol_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates the exact versioned bounded wire header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_ivshmem_protocol_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds real Q15 payload and derives the exact convolution output size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_ivshmem_protocol_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only timely correlated remote host CUDA device readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
