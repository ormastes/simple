# simple_audio_remote_driver_spec

> Pure-Simple QEMU audio offload driver admits only timely correlated CUDA readback.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_remote_driver_spec

Pure-Simple QEMU audio offload driver admits only timely correlated CUDA readback.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_remote_driver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pure-Simple QEMU audio offload driver admits only timely correlated CUDA readback.

## Scenarios

### pure-Simple remote CUDA audio driver

#### accepts timely device readback with exact provenance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts timely device readback with exact provenance
   - Expected: ring.publish(0, 41u64, 7u64, 1000u64, 1000u64, 256, 2, 1024, "partitioned-convolution", 91) equals `published`
   - Expected: ring.claim(0, generation) equals `claimed`
   - Expected: ring.complete(0, SimpleAudioRemoteReceipt(generation: generation, correlation_id: 41u64, service_elapsed_ns: 500u64, provider: "remote-host-cuda", native_handle: 8, device_identity: 86, readback_checksum: 92, normalized_error_millionths: 4, status: "device-readback")) equals `completed`
   - Expected: ring.poll(0, generation, 1500u64) equals `accepted-device-result`
   - Expected: ring.release(0, generation) equals `released`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts timely device readback with exact provenance")
var ring = SimpleAudioRemoteRing.create(4)
expect(ring.publish(0, 41u64, 7u64, 1000u64, 1000u64, 256, 2, 1024, "partitioned-convolution", 91)).to_equal("published")
val generation = ring.generations[0]
expect(ring.claim(0, generation)).to_equal("claimed")
expect(ring.complete(0, SimpleAudioRemoteReceipt(generation: generation, correlation_id: 41u64, service_elapsed_ns: 500u64, provider: "remote-host-cuda", native_handle: 8, device_identity: 86, readback_checksum: 92, normalized_error_millionths: 4, status: "device-readback"))).to_equal("completed")
expect(ring.poll(0, generation, 1500u64)).to_equal("accepted-device-result")
expect(ring.release(0, generation)).to_equal("released")
```

</details>

#### falls back without blocking for timeout late parity and provenance faults

- falls back without blocking for timeout late parity and provenance faults
   - Expected: ring.publish(0, 51u64, 8u64, 2000u64, 1000u64, 256, 2, 1024, "hrtf-bank", 101) equals `published`
   - Expected: ring.poll(0, generation, 2700u64) equals `cpu-fallback-timeout`
   - Expected: ring.claim(0, generation) equals `claimed`
   - Expected: ring.complete(0, SimpleAudioRemoteReceipt(generation: generation, correlation_id: 51u64, service_elapsed_ns: 700u64, provider: "host-cuda", native_handle: 8, device_identity: 86, readback_checksum: 102, normalized_error_millionths: 20, status: "device-readback")) equals `completed`
   - Expected: ring.poll(0, generation, 2700u64) equals `cpu-fallback-late`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("falls back without blocking for timeout late parity and provenance faults")
var ring = SimpleAudioRemoteRing.create(2)
expect(ring.publish(0, 51u64, 8u64, 2000u64, 1000u64, 256, 2, 1024, "hrtf-bank", 101)).to_equal("published")
val generation = ring.generations[0]
expect(ring.poll(0, generation, 2700u64)).to_equal("cpu-fallback-timeout")
expect(ring.claim(0, generation)).to_equal("claimed")
expect(ring.complete(0, SimpleAudioRemoteReceipt(generation: generation, correlation_id: 51u64, service_elapsed_ns: 700u64, provider: "host-cuda", native_handle: 8, device_identity: 86, readback_checksum: 102, normalized_error_millionths: 20, status: "device-readback"))).to_equal("completed")
expect(ring.poll(0, generation, 2700u64)).to_equal("cpu-fallback-late")
```

</details>

#### rejects stale correlation unsupported work and cleans every live slot

- rejects stale correlation unsupported work and cleans every live slot
   - Expected: ring.publish(0, 0u64, 1u64, 0u64, 1000u64, 256, 2, 512, "partitioned-convolution", 1) equals `invalid-work`
   - Expected: ring.publish(0, 9u64, 1u64, 0u64, 1000u64, 256, 2, 512, "fft-jit", 1) equals `unsupported-operation`
   - Expected: ring.publish(0, 9u64, 1u64, 0u64, 1000u64, 256, 2, 512, "hrtf-bank", 1) equals `published`
   - Expected: ring.claim(0, generation) equals `claimed`
   - Expected: ring.complete(0, SimpleAudioRemoteReceipt(generation: generation, correlation_id: 10u64, service_elapsed_ns: 100u64, provider: "remote-host-cuda", native_handle: 1, device_identity: 1, readback_checksum: 1, normalized_error_millionths: 0, status: "device-readback")) equals `correlation-mismatch`
   - Expected: ring.shutdown() equals `1`
   - Expected: ring.live_count equals `0`
   - Expected: ring.publish(1, 10u64, 2u64, 0u64, 1000u64, 256, 2, 512, "hrtf-bank", 1) equals `shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects stale correlation unsupported work and cleans every live slot")
var ring = SimpleAudioRemoteRing.create(2)
expect(ring.publish(0, 0u64, 1u64, 0u64, 1000u64, 256, 2, 512, "partitioned-convolution", 1)).to_equal("invalid-work")
expect(ring.publish(0, 9u64, 1u64, 0u64, 1000u64, 256, 2, 512, "fft-jit", 1)).to_equal("unsupported-operation")
expect(ring.publish(0, 9u64, 1u64, 0u64, 1000u64, 256, 2, 512, "hrtf-bank", 1)).to_equal("published")
val generation = ring.generations[0]
expect(ring.claim(0, generation)).to_equal("claimed")
expect(ring.complete(0, SimpleAudioRemoteReceipt(generation: generation, correlation_id: 10u64, service_elapsed_ns: 100u64, provider: "remote-host-cuda", native_handle: 1, device_identity: 1, readback_checksum: 1, normalized_error_millionths: 0, status: "device-readback"))).to_equal("correlation-mismatch")
expect(ring.shutdown()).to_equal(1)
expect(ring.live_count).to_equal(0)
expect(ring.publish(1, 10u64, 2u64, 0u64, 1000u64, 256, 2, 512, "hrtf-bank", 1)).to_equal("shutdown")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6ccc8ef1f5c5c5e6ff748dab48cfd88a371bee39b217ef36aad29076a555c888`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ccc8ef1f5c5c5e6ff748dab48cfd88a371bee39b217ef36aad29076a555c888`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ccc8ef1f5c5c5e6ff748dab48cfd88a371bee39b217ef36aad29076a555c888`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_remote_driver_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_remote_driver_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_remote_driver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_remote_driver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_remote_driver_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/io_audio/simple_audio_remote_driver_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_remote_driver_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts timely device readback with exact provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_remote_driver_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back without blocking for timeout late parity and provenance faults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_remote_driver_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects stale correlation unsupported work and cleans every live slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
