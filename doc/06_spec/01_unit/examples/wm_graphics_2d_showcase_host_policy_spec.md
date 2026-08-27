# Wm Graphics 2d Showcase Host Policy Specification

> Tests covering host WM graphics 2D showcase correctness policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Graphics 2d Showcase Host Policy Specification

## Scenarios

### host WM graphics 2D showcase correctness policy

#### uses the scale-8 default while preserving explicit overrides

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the scale-8 default while preserving explicit overrides


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the scale-8 default while preserving explicit overrides")
val s = source()
expect(s).to_contain("fn wm_graphics_2d_child_frame_scale()")
expect(s).to_contain("if requested_scale != \"\":")
expect(s).to_contain("return requested_scale")
expect(s).to_contain("env[\"SHOWCASE_PPM_SCALE\"] = wm_graphics_2d_child_frame_scale()")
```

</details>

#### forwards backend and opt-in diagnostics to the child

- forwards backend and opt-in diagnostics to the child


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("forwards backend and opt-in diagnostics to the child")
val s = source()
expect(s).to_contain("env[\"SIMPLE_GUI_BACKEND\"] = requested_backend")
expect(s).to_contain("\"SIMPLE_GUI_BACKEND=\{requested_backend\}\"")
expect(s).to_contain("env[\"SIMPLE_DIAG\"] = simple_diag")
expect(s).to_contain("\"SIMPLE_DIAG=\{simple_diag\}\"")
expect(s).to_contain("env[\"SIMPLE_DIAG_FILE\"] = simple_diag_file")
expect(s).to_contain("\"SIMPLE_DIAG_FILE=\{simple_diag_file\}\"")
```

</details>

#### uses native mouse identity and forwards presses across the whole child

- uses native mouse identity and forwards presses across the whole child


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses native mouse identity and forwards presses across the whole child")
val s = source()
expect(s).to_contain("mouse_native_id: i64")
expect(s).to_contain("mouse_native_id = ev.native_id")
expect(s).to_contain("if input.mouse_native_id != 0:")
expect(s.contains("fn child_needs_press_stream(")).to_be(false)
expect(s).to_contain("if loc_down.ok:\n                    child_drag_forwarding = true")
expect(s).to_contain("write_child_pointer_event(event_path, child_seq, \"down\"")
expect(s).to_contain("write_child_pointer_event(event_path, child_seq, \"move\"")
expect(s).to_contain("write_child_pointer_event(event_path, child_seq, \"up\"")
```

</details>

#### preserves and forwards ordered keyboard down and up edges

- preserves and forwards ordered keyboard down and up edges


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves and forwards ordered keyboard down and up edges")
val s = source()
expect(s).to_contain("key_native_ids: [i64]")
expect(s).to_contain("keycodes: [i64]")
expect(s).to_contain("key_pressed: [bool]")
expect(s).to_contain("key_native_ids.push(ev.native_id)")
expect(s).to_contain("keycodes.push(ev.keycode)")
expect(s).to_contain("key_pressed.push(ev.pressed)")
expect(s).to_contain("val ev = wm_fs_key_event(next_seq, keycode, pressed)")
expect(s).to_contain(
    "if file_write(seq_path, encoded) and file_write(event_path, encoded):")
expect(s).to_contain("\"host_key_event\"")
expect(s).to_contain("val key_native_id = input.key_native_ids[ki]")
expect(s).to_contain(
    "native_id=\{key_native_id\} keycode=\{keycode\} pressed=\{pressed\}")
expect(s).to_contain(
    "child_seq = write_child_key_event(\n" +
    "            event_path, child_seq, keycode, pressed)")
expect(s).to_contain(
    "if child_seq > before_key_seq:\n" +
    "            child_refresh_pending = true\n" +
    "            child_refresh_deadline = 0")
```

</details>

#### validates exact receipts and presents only a cached validated frame

- validates exact receipts and presents only a cached validated frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates exact receipts and presents only a cached validated frame")
val s = source()
expect(s).to_contain("fn validate_child_frame_receipt(")
expect(s).to_contain("wm_fs_frame_receipt_correlation(receipt.event_seq")
expect(s).to_contain("wm_fs_frame_receipt_valid(receipt")
expect(s).to_contain("wm_fs_frame_checksum(child.pixels) != receipt.checksum")
expect(s).to_contain("validated_child = validation.frame")
expect(s).to_contain("render_and_present(gui, b, state.comp, frame_w, frame_h, validated_child")
expect(s.contains("load_child_frame(frame_path)\n    write_wm_trace(trace_path, \"render_child_load_done\")")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering host WM graphics 2D showcase correctness policy.
- host WM graphics 2D showcase correctness policy

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

- Canonical SPipe generation for source `f4474019a36845b06b817e6473ec4389d928b570bfc51112d1b0cd87848f930d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4474019a36845b06b817e6473ec4389d928b570bfc51112d1b0cd87848f930d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4474019a36845b06b817e6473ec4389d928b570bfc51112d1b0cd87848f930d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.spl
mirror: doc/06_spec/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the scale-8 default while preserving explicit overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'forwards backend and opt-in diagnostics to the child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/examples/wm_graphics_2d_showcase_host_policy_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses native mouse identity and forwards presses across the whole child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
