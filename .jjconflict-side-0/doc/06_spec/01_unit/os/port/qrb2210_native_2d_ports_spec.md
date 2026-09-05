# Qrb2210 Native 2d Ports Specification

> Tests covering QRB2210 board-owned primitive receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qrb2210 Native 2d Ports Specification

## Scenarios

### QRB2210 board-owned primitive receipts

#### rejects identity-free and cross-owner handles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects identity-free and cross-owner handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects identity-free and cross-owner handles")
expect(qrb2210_board_device_handle_ready(
    device(QRB2210_DEVICE_INPUT, "/dev/input/event2", 41u64), QRB2210_DEVICE_INPUT)).to_be(true)
expect(qrb2210_board_device_handle_ready(
    device(QRB2210_DEVICE_INPUT, "/dev/input/event2", 0u64), QRB2210_DEVICE_INPUT)).to_be(false)
expect(qrb2210_board_device_handle_ready(
    device(QRB2210_DEVICE_AUDIO, "/dev/snd/pcmC0D0p", 42u64), QRB2210_DEVICE_INPUT)).to_be(false)
expect(qrb2210_board_device_handle_ready(
    device(QRB2210_DEVICE_INPUT, "/dev/dri/card0", 42u64), QRB2210_DEVICE_INPUT)).to_be(false)
expect(qrb2210_board_device_handle_ready(
    device(QRB2210_DEVICE_GPU, "/dev/dri/renderD128", 45u64), QRB2210_DEVICE_GPU)).to_be(true)
```

</details>

#### correlates only the same live owner instance in one boot and generation

- correlates only the same live owner instance in one boot and generation


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("correlates only the same live owner instance in one boot and generation")
val expected = device(QRB2210_DEVICE_INPUT, "/dev/input/event2", 41u64)
var observed = expected
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(true)
observed.boot_id = "boot-18"
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
observed = expected
observed.native_handle = 42u64
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
observed = expected
observed.driver_generation = 4
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
observed = expected
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_AUDIO)).to_be(false)
observed = expected
observed.owner = QRB2210_DEVICE_AUDIO
observed.device_node = "/dev/snd/pcmC0D0p"
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
observed = expected
observed.board_id = "not-qrb2210"
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
observed = expected
observed.boot_id = ""
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
observed = expected
observed.device_node = "/dev/dri/card0"
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
observed = expected
observed.native_handle = 0u64
expect(qrb2210_board_device_handle_same_instance(
    expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
var stale_expected = expected
stale_expected.driver_generation = 0
observed = expected
expect(qrb2210_board_device_handle_same_instance(
    stale_expected, observed, QRB2210_DEVICE_INPUT)).to_be(false)
```

</details>

#### requires a contiguous receipt sequence from the same physical input handle

- requires a contiguous receipt sequence from the same physical input handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires a contiguous receipt sequence from the same physical input handle")
val previous = input(QRB2210_INPUT_MOVE, 0, 0, 0, false, false, false, false, false)
var current = previous
current.sequence = 10
expect(qrb2210_input_receipt_follows(previous, current)).to_be(true)
current.sequence = 9
expect(qrb2210_input_receipt_follows(previous, current)).to_be(false)
```

</details>

#### normalizes move down drag up and wheel without a private event type

- normalizes move down drag up and wheel without a private event type
   - Expected: pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_MOVE, 0, 0, 0, false, false, false, false, false)).unwrap().event) equals `12:23:0:true:0`
   - Expected: pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_DOWN, HOST_BTN_LEFT, 0, 0, false, false, false, false, false)).unwrap().event) equals `12:23:1:true:0`
   - Expected: pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_DRAG, HOST_BTN_LEFT, 0, 0, false, false, false, false, false)).unwrap().event) equals `12:23:1:true:0`
   - Expected: pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_UP, HOST_BTN_LEFT, 0, 0, false, false, false, false, false)).unwrap().event) equals `12:23:1:false:0`
   - Expected: pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_WHEEL, 0, -2, 0, false, false, false, false, false)).unwrap().event) equals `12:23:0:false:-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("normalizes move down drag up and wheel without a private event type")
expect(pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_MOVE, 0, 0, 0, false, false, false, false, false)).unwrap().event)).to_equal("12:23:0:true:0")
expect(pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_DOWN, HOST_BTN_LEFT, 0, 0, false, false, false, false, false)).unwrap().event)).to_equal("12:23:1:true:0")
expect(pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_DRAG, HOST_BTN_LEFT, 0, 0, false, false, false, false, false)).unwrap().event)).to_equal("12:23:1:true:0")
expect(pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_UP, HOST_BTN_LEFT, 0, 0, false, false, false, false, false)).unwrap().event)).to_equal("12:23:1:false:0")
expect(pointer_shape(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_WHEEL, 0, -2, 0, false, false, false, false, false)).unwrap().event)).to_equal("12:23:0:false:-2")
```

</details>

#### maps evdev keys and preserves left/right Ctrl and Alt evidence

- maps evdev keys and preserves left/right Ctrl and Alt evidence
   - Expected: key_shape(printable.event) equals `{CANON_A}:a:true:{HOST_MOD_CTRL | HOST_MOD_ALT}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps evdev keys and preserves left/right Ctrl and Alt evidence")
val printable = qrb2210_normalize_input_receipt(input(
    QRB2210_INPUT_KEY, 0, 0, 30, true, true, false, false, true)).unwrap()
expect(key_shape(printable.event)).to_equal("{CANON_A}:a:true:{HOST_MOD_CTRL | HOST_MOD_ALT}")
expect(printable.left_ctrl).to_be(true)
expect(printable.right_alt).to_be(true)
expect(key_shape(qrb2210_normalize_input_receipt(input(
    QRB2210_INPUT_KEY, 0, 0, 97, false, false, true, false, false)).unwrap().event)).to_equal("{CANON_CTRL}::false:{HOST_MOD_CTRL}")
expect(key_shape(qrb2210_normalize_input_receipt(input(
    QRB2210_INPUT_KEY, 0, 0, 100, true, false, false, true, false)).unwrap().event)).to_equal("{CANON_ALT}::true:{HOST_MOD_ALT}")
```

</details>

#### fails closed for malformed or unmapped input receipts

- fails closed for malformed or unmapped input receipts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed for malformed or unmapped input receipts")
expect(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_WHEEL, 0, 0, 0, false, false, false, false, false)).is_err()).to_be(true)
expect(qrb2210_normalize_input_receipt(input(QRB2210_INPUT_KEY, 0, 0, 999, false, false, false, false, false)).is_err()).to_be(true)
expect(qrb2210_normalize_input_receipt(input("touch-guess", 0, 0, 0, false, false, false, false, false)).is_err()).to_be(true)
```

</details>

#### correlates display present and capture on physical identity and frame

- correlates display present and capture on physical identity and frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("correlates display present and capture on physical identity and frame")
val display = device(QRB2210_DEVICE_DISPLAY, "/dev/dri/card0", 43u64)
val present = Qrb2210DisplayPresentReceipt(
    device: display, submission_id: 81, frame_id: 71, present_id: 19,
    readback_checksum: 991, presented: true)
val capture = Qrb2210DisplayCaptureReceipt(
    device: display, submission_id: 81, frame_id: 71, present_id: 19, capture_id: 20,
    width: 2, height: 2, byte_count: 16, readback_checksum: 991, completed: true)
expect(qrb2210_display_capture_correlated(present, capture)).to_be(true)
var wrong_frame = capture
wrong_frame.frame_id = 72
expect(qrb2210_display_capture_correlated(present, wrong_frame)).to_be(false)
var wrong_submission = capture
wrong_submission.submission_id = 82
expect(qrb2210_display_capture_correlated(present, wrong_submission)).to_be(false)
```

</details>

#### correlates audio completion with its physical PCM buffer

- correlates audio completion with its physical PCM buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("correlates audio completion with its physical PCM buffer")
val audio = device(QRB2210_DEVICE_AUDIO, "/dev/snd/pcmC0D0p", 44u64)
val submit = Qrb2210AudioSubmitReceipt(
    device: audio, frame_id: 71, submission_id: 81, buffer_handle: 82u64,
    sample_count: 960, accepted: true)
val completion = Qrb2210AudioCompletionReceipt(
    device: audio, frame_id: 71, submission_id: 81, buffer_handle: 82u64,
    completed_sample_count: 960, completion_id: 83, completed: true)
expect(qrb2210_audio_completion_correlated(submit, completion)).to_be(true)
var short = completion
short.completed_sample_count = 959
expect(qrb2210_audio_completion_correlated(submit, short)).to_be(false)
var wrong_frame = completion
wrong_frame.frame_id = 72
expect(qrb2210_audio_completion_correlated(submit, wrong_frame)).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/qrb2210_native_2d_ports_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QRB2210 board-owned primitive receipts.
- QRB2210 board-owned primitive receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `303a0438d38cff5259c9fab91494b4cda793f8627dd0c3e96bc155a09a36171a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `303a0438d38cff5259c9fab91494b4cda793f8627dd0c3e96bc155a09a36171a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `303a0438d38cff5259c9fab91494b4cda793f8627dd0c3e96bc155a09a36171a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/port/qrb2210_native_2d_ports_spec.spl
mirror: doc/06_spec/01_unit/os/port/qrb2210_native_2d_ports_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/qrb2210_native_2d_ports_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/qrb2210_native_2d_ports_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/qrb2210_native_2d_ports_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects identity-free and cross-owner handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_native_2d_ports_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'correlates only the same live owner instance in one boot and generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/qrb2210_native_2d_ports_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a contiguous receipt sequence from the same physical input handle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
