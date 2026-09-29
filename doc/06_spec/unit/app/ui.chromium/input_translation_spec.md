# Input Translation Specification

> Tests covering Chromium Event Bridge — stateless translation, Chromium Event Bridge — modifier round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Input Translation Specification

## Scenarios

### Chromium Event Bridge — stateless translation

#### maps escape to NormalMode

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps escape to NormalMode


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps escape to NormalMode")
val ev = translate_key_event(27, 0)
match ev:
    UIEvent.NormalMode =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps Ctrl+Q to Quit via modifier bitmask

- maps Ctrl+Q to Quit via modifier bitmask


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Ctrl+Q to Quit via modifier bitmask")
val ev = translate_key_event(113, 2)
match ev:
    UIEvent.Quit =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps Shift+Tab to FocusPrev

- maps Shift+Tab to FocusPrev


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Shift+Tab to FocusPrev")
val ev = translate_key_event(9, 1)
match ev:
    UIEvent.FocusPrev =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps mouse press(button=0) to TouchPress

- maps mouse press(button=0) to TouchPress


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps mouse press(button=0) to TouchPress")
val ev = translate_mouse_event(120, 240, 0, "press")
match ev:
    UIEvent.TouchPress(x, y) =>
        expect(x == 120).to_be_true()
        expect(y == 240).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### maps positive wheel delta to FocusNext

- maps positive wheel delta to FocusNext


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps positive wheel delta to FocusNext")
val ev = translate_wheel_ui_event(3)
match ev:
    UIEvent.FocusNext =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

#### produces a DOM wheel event with type 'wheel'

- produces a DOM wheel event with type 'wheel'


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a DOM wheel event with type 'wheel'")
val dom = translate_wheel_dom_event(42, 1000)
expect(dom.type_name == "wheel").to_be_true()
expect(dom.target_id == 42).to_be_true()
```

</details>

### Chromium Event Bridge — modifier round-trip

#### round-trips a Shift press through the modifier mask

- round-trips a Shift press through the modifier mask


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a Shift press through the modifier mask")
var bridge = ChromiumEventBridge.new()
bridge.update_modifier(16, true)
expect(bridge.shift_down).to_be_true()
expect(bridge.modifiers_mask() == 1).to_be_true()
bridge.update_modifier(16, false)
expect(not bridge.shift_down).to_be_true()
expect(bridge.modifiers_mask() == 0).to_be_true()
```

</details>

#### tracks Ctrl then produces Ctrl+C Quit on release edge

- tracks Ctrl then produces Ctrl+C Quit on release edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks Ctrl then produces Ctrl+C Quit on release edge")
var bridge = ChromiumEventBridge.new()
bridge.update_modifier(17, true)
expect(bridge.ctrl_down).to_be_true()
val result = bridge.on_key(99, true)
match result:
    UIEvent.Quit =>
        expect(true).to_be_true()
    _ =>
        expect(false).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium/input_translation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chromium Event Bridge — stateless translation, Chromium Event Bridge — modifier round-trip.
- Chromium Event Bridge — stateless translation
- Chromium Event Bridge — modifier round-trip

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45ec8db789e7cb619bd493601a1b4c94f510078980602c5fe5ea6c203496b461`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45ec8db789e7cb619bd493601a1b4c94f510078980602c5fe5ea6c203496b461`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45ec8db789e7cb619bd493601a1b4c94f510078980602c5fe5ea6c203496b461`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium/input_translation_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium/input_translation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium/input_translation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium/input_translation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium/input_translation_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps escape to NormalMode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/input_translation_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps Ctrl+Q to Quit via modifier bitmask' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium/input_translation_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps Shift+Tab to FocusPrev' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
