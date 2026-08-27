# SimpleOS Render Evidence Protocol

> Uses the pure-Simple QMP and serial adapters to correlate a live guest render

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Render Evidence Protocol

Uses the pure-Simple QMP and serial adapters to correlate a live guest render

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Uses the pure-Simple QMP and serial adapters to correlate a live guest render
receipt with one captured frame; no inline Python or tolerant baseline exists.

## Scenarios

### SimpleOS QMP and serial render evidence

#### should negotiate QMP and capture a live nonblank guest frame

- should negotiate QMP and capture a live nonblank guest frame
   - Protocol capture: after_step
- Connect and negotiate QMP capabilities
   - Protocol capture: after_step
- Wait for the guest render receipt
   - Protocol capture: after_step
- Request the matching screendump
   - Protocol capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should negotiate QMP and capture a live nonblank guest frame")
step("Connect and negotiate QMP capabilities")
step("Wait for the guest render receipt")
step("Request the matching screendump")
require_live_qemu_receipt_capture()
```

</details>

<details>
<summary>Advanced: should correlate firmware boot run and frame identities</summary>

#### should correlate firmware boot run and frame identities

- should correlate firmware boot run and frame identities
- Join the serial receipt and capture identities
   - Expected: validate_simpleos_render_target_evidence(evidence).code equals `pass`
   - Expected: simpleos_render_target_status(evidence) equals `qemu-verified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should correlate firmware boot run and frame identities")
step("Join the serial receipt and capture identities")
val evidence = simpleos_target_evidence(
    "qemu", "x86_64", "", "", "boot-1", "frame-1",
    SIMPLEOS_EVIDENCE_HASH, 0)
expect(validate_simpleos_render_target_evidence(evidence).code).to_equal("pass")
expect(simpleos_render_target_status(evidence)).to_equal("qemu-verified")
```

</details>


</details>

<details>
<summary>Advanced: should reject corrupt reordered or truncated serial events</summary>

#### should reject corrupt reordered or truncated serial events

- should reject corrupt reordered or truncated serial events
- Submit invalid receipt event streams


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject corrupt reordered or truncated serial events")
step("Submit invalid receipt event streams")
val corrupt = BackendRenderReceiptHeader(
    version: 1u32, arch_code: 1u32, runtime_code: 1u32, backend_code: 1u32,
    firmware_hash_word0: 0u64, firmware_hash_word1: 0u64,
    firmware_hash_word2: 0u64, firmware_hash_word3: 0u64, boot_id: 1u64,
    frame_id: 1u64, surface_handle: 1u64, width: 4u32, height: 4u32,
    stride: 16u32, format_code: 1u32)
val reordered = BackendRenderReceiptEvent(
    sequence: 2u32, operation_code: 1u32, resource_id: 1u64,
    state_before: 0u32, state_after: 1u32, value_hash: 1u64)
val truncated = BackendRenderReceiptTrailer(
    event_count: 1u32, frame_complete: true, pixel_hash_word0: 1u64,
    pixel_hash_word1: 0u64, pixel_hash_word2: 0u64,
    pixel_hash_word3: 0u64, nonblank_pixel_count: 1u64, reason_code: 0u32)
expect(backend_render_receipt_header_valid(corrupt)).to_be(false)
expect(backend_render_receipt_event_valid(reordered, 1u32)).to_be(false)
expect(backend_render_receipt_trailer_valid(truncated, 2u32)).to_be(false)
```

</details>


</details>

<details>
<summary>Advanced: should reject any nonzero framebuffer mismatch</summary>

#### should reject any nonzero framebuffer mismatch

- should reject any nonzero framebuffer mismatch
- Change one captured framebuffer pixel
   - Expected: result.different_pixels equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject any nonzero framebuffer mismatch")
step("Change one captured framebuffer pixel")
val result = compare_exact([0xff112233u32], [0xff112234u32], 1, 1)
expect(result.exact_match).to_be(false)
expect(result.different_pixels).to_equal(1)
```

</details>


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
- `REQ-017`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `89284716c8d1b4672832f4cce791e4c56a16c7bb5c3cb6de4e91f0f3a5183ef5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `89284716c8d1b4672832f4cce791e4c56a16c7bb5c3cb6de4e91f0f3a5183ef5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `89284716c8d1b4672832f4cce791e4c56a16c7bb5c3cb6de4e91f0f3a5183ef5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl
mirror: doc/06_spec/03_system/os/qemu/simpleos_render_evidence_protocol_spec.md (current)
findings: 11 blockers: 1
  narrative=100 structure=80 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/03_system/os/qemu/simpleos_render_evidence_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/simpleos_render_evidence_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should negotiate QMP and capture a live nonblank guest frame' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should negotiate QMP and capture a live nonblank guest frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should correlate firmware boot run and frame identities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject corrupt reordered or truncated serial events' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject corrupt reordered or truncated serial events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject any nonzero framebuffer mismatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/simpleos_render_evidence_protocol_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject any nonzero framebuffer mismatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
