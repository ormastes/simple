# Qrb2210 Evdev Primitive Provider Specification

> Tests covering QRB2210 physical evdev primitive provider.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Evdev Primitive Provider Specification

## Scenarios

### QRB2210 physical evdev primitive provider

#### requires a physical kernel input identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires a physical kernel input identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires a physical kernel input identity")
expect(qrb2210_evdev_identity_ready(identity())).to_be(true)
var no_irq = identity()
no_irq.irq_line = 0
expect(qrb2210_evdev_identity_ready(no_irq)).to_be(false)
var hosted = identity()
hosted.physical_device = false
expect(qrb2210_evdev_identity_ready(hosted)).to_be(false)
var no_owner = identity()
no_owner.kernel_owner_handle = 0u64
expect(qrb2210_evdev_identity_ready(no_owner)).to_be(false)
```

</details>

#### accepts only fresh correlated interrupt receipts

- accepts only fresh correlated interrupt receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts only fresh correlated interrupt receipts")
val bound = identity()
expect(qrb2210_evdev_kernel_receipt_correlates(bound, receipt(8, 12), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_correlates(bound, receipt(7, 12), 7, 11)).to_be(false)
expect(qrb2210_evdev_kernel_receipt_correlates(bound, receipt(8, 11), 7, 11)).to_be(false)
var no_frame = receipt(8, 12)
no_frame.event.frame_id = 0
expect(qrb2210_evdev_kernel_receipt_correlates(bound, no_frame, 7, 11)).to_be(false)
var no_submission = receipt(8, 12)
no_submission.event.submission_id = 0
expect(qrb2210_evdev_kernel_receipt_correlates(
    bound, no_submission, 7, 11)).to_be(false)
var wrong_ring = receipt(8, 12)
wrong_ring.event_ring_handle = 93u64
expect(qrb2210_evdev_kernel_receipt_correlates(bound, wrong_ring, 7, 11)).to_be(false)
var wrong_irq = receipt(8, 12)
wrong_irq.irq_line = 34
expect(qrb2210_evdev_kernel_receipt_correlates(bound, wrong_irq, 7, 11)).to_be(false)
var wrong_owner = receipt(8, 12)
wrong_owner.kernel_owner_handle = 93u64
expect(qrb2210_evdev_kernel_receipt_correlates(bound, wrong_owner, 7, 11)).to_be(false)
var stale_boot = receipt(8, 12)
stale_boot.event.device.boot_id = "boot-20"
expect(qrb2210_evdev_kernel_receipt_correlates(bound, stale_boot, 7, 11)).to_be(false)
```

</details>

#### admits only canonical pointer wheel and left/right modifier payloads

- admits only canonical pointer wheel and left/right modifier payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits only canonical pointer wheel and left/right modifier payloads")
val bound = identity()
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt(8, 12), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_DOWN, HOST_BTN_LEFT, 0, 0, false,
    false, false, false, false), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_DRAG, HOST_BTN_LEFT, 0, 0, false,
    false, false, false, false), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_UP, HOST_BTN_LEFT, 0, 0, false,
    false, false, false, false), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_WHEEL, 0, -2, 0, false,
    false, false, false, false), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_KEY, 0, 0, 30, true,
    true, false, false, true), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_KEY, 0, 0, 97, false,
    false, true, false, false), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_KEY, 0, 0, 100, true,
    false, false, true, false), 7, 11)).to_be(true)
expect(qrb2210_evdev_kernel_receipt_admissible(bound, receipt_kind(
    8, 12, QRB2210_INPUT_WHEEL, 0, 0, 0, false,
    false, false, false, false), 7, 11)).to_be(false)
```

</details>

#### has no hosted input or synthetic-event fallback

- has no hosted input or synthetic-event fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("has no hosted input or synthetic-event fallback")
val source = file_read_text(PROVIDER)
expect(source).to_contain("kernel.poll_interrupt_receipt()")
expect(source).to_contain("UNO_Q_DESKTOP_STATUS_PORT_UNAVAILABLE")
expect(source.contains("rt_process")).to_be(false)
expect(source.contains("virtio")).to_be(false)
expect(source.contains("android")).to_be(false)
expect(source.contains("synthetic")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QRB2210 physical evdev primitive provider.
- QRB2210 physical evdev primitive provider

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48fbbe76eff6cdfa5c3311ae36ef4d79ac6fda7cc584e2ca30d672a1338a4371`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48fbbe76eff6cdfa5c3311ae36ef4d79ac6fda7cc584e2ca30d672a1338a4371`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48fbbe76eff6cdfa5c3311ae36ef4d79ac6fda7cc584e2ca30d672a1338a4371`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a physical kernel input identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only fresh correlated interrupt receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_evdev_primitive_provider_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only canonical pointer wheel and left/right modifier payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
