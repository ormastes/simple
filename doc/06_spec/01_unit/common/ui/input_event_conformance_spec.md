# Input Event Conformance Specification

> Tests covering input event conformance suite (phase 1, in-process).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Input Event Conformance Specification

## Scenarios

### input event conformance suite (phase 1, in-process)

#### canonical encoding round-trips through every UIEvent variant

#### renders KeyPress with key argument

- renders KeyPress with key argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("renders KeyPress with key argument")
val s = render_event(UIEvent.KeyPress(key: "a"))
expect(s == "KeyPress|a").to_be_true()
```

</details>

#### renders Resize with width and height

- renders Resize with width and height


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("renders Resize with width and height")
val s = render_event(UIEvent.Resize(width: 800, height: 600))
expect(s == "Resize|800|600").to_be_true()
```

</details>

#### renders all unit variants

- renders all unit variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("renders all unit variants")
val a = render_event(UIEvent.FileChanged)
val b = render_event(UIEvent.Quit)
val c = render_event(UIEvent.FocusNext)
val d = render_event(UIEvent.FocusPrev)
val e = render_event(UIEvent.CommandMode)
val f = render_event(UIEvent.NormalMode)
val g = render_event(UIEvent.InsertMode)
expect(a == "FileChanged").to_be_true()
expect(b == "Quit").to_be_true()
expect(c == "FocusNext").to_be_true()
expect(d == "FocusPrev").to_be_true()
expect(e == "CommandMode").to_be_true()
expect(f == "NormalMode").to_be_true()
expect(g == "InsertMode").to_be_true()
```

</details>

#### renders pointer/touch variants with coordinates

- renders pointer/touch variants with coordinates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("renders pointer/touch variants with coordinates")
val p = render_event(UIEvent.TouchPress(x: 1, y: 2))
val m = render_event(UIEvent.TouchMove(x: 3, y: 4))
val r = render_event(UIEvent.TouchRelease(x: 5, y: 6))
expect(p == "TouchPress|1|2").to_be_true()
expect(m == "TouchMove|3|4").to_be_true()
expect(r == "TouchRelease|5|6").to_be_true()
```

</details>

#### renders Action with name argument

- renders Action with name argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("renders Action with name argument")
val s = render_event(UIEvent.Action(name: "focus_btn_ok"))
expect(s == "Action|focus_btn_ok").to_be_true()
```

</details>

#### in-process backend queues UIEvents in order

#### starts with an empty queue

- starts with an empty queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("starts with an empty queue")
val backend = InProcessInputBackend.create()
val snap = backend.snapshot()
val n = arr_len_event(snap)
val empty = n == 0
expect(empty).to_be_true()
```

</details>

#### snapshots pushed events in FIFO order

- snapshots pushed events in FIFO order


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("snapshots pushed events in FIFO order")
val backend = InProcessInputBackend.create()
backend.push(UIEvent.KeyPress(key: "a"))
backend.push(UIEvent.KeyPress(key: "b"))
backend.push(UIEvent.Quit)
val drained = backend.snapshot()
val e0 = render_event(drained[0])
val e1 = render_event(drained[1])
val e2 = render_event(drained[2])
val n = arr_len_event(drained)
val len_ok = n == 3
expect(len_ok).to_be_true()
expect(e0 == "KeyPress|a").to_be_true()
expect(e1 == "KeyPress|b").to_be_true()
expect(e2 == "Quit").to_be_true()
```

</details>

#### clear empties the queue

- clear empties the queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("clear empties the queue")
val backend = InProcessInputBackend.create()
backend.push(UIEvent.FileChanged)
backend.clear()
val snap = backend.snapshot()
val n = arr_len_event(snap)
val empty = n == 0
expect(empty).to_be_true()
```

</details>

#### SDN trace loader parses Phase-1 traces

#### loads the key_press_letter trace with one expected event

- loads the key_press_letter trace with one expected event


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("loads the key_press_letter trace with one expected event")
val sc = load_trace(_trace("key_press_letter"))
val name_ok = sc.name == "key_press_letter"
expect(name_ok).to_be_true()
val first = sc.expected[0]
val n = arr_len_text(sc.expected)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(first == "KeyPress|a").to_be_true()
```

</details>

#### loads the touch_drag_sequence trace as a multi-step scenario

- loads the touch_drag_sequence trace as a multi-step scenario


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("loads the touch_drag_sequence trace as a multi-step scenario")
val sc = load_trace(_trace("touch_drag_sequence"))
val first = sc.expected[0]
val last = sc.expected[3]
val n = arr_len_text(sc.expected)
val len_ok = n == 4
expect(len_ok).to_be_true()
expect(first == "TouchPress|10|10").to_be_true()
expect(last == "TouchRelease|40|25").to_be_true()
```

</details>

#### structural conformance: every Phase-1 trace replays cleanly

#### replays key_press_letter (UIEvent.KeyPress letter)

- replays key_press_letter (UIEvent.KeyPress letter)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays key_press_letter (UIEvent.KeyPress letter)")
val sc = load_trace(_trace("key_press_letter"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val expected_n = arr_len_text(sc.expected)
val len_ok = n == expected_n
expect(len_ok).to_be_true()
expect(v == "KeyPress|a").to_be_true()
```

</details>

#### replays key_press_enter (UIEvent.KeyPress named key)

- replays key_press_enter (UIEvent.KeyPress named key)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays key_press_enter (UIEvent.KeyPress named key)")
val sc = load_trace(_trace("key_press_enter"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "KeyPress|enter").to_be_true()
```

</details>

#### replays resize (UIEvent.Resize)

- replays resize (UIEvent.Resize)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays resize (UIEvent.Resize)")
val sc = load_trace(_trace("resize"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "Resize|1920|1080").to_be_true()
```

</details>

#### replays file_changed (UIEvent.FileChanged)

- replays file_changed (UIEvent.FileChanged)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays file_changed (UIEvent.FileChanged)")
val sc = load_trace(_trace("file_changed"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "FileChanged").to_be_true()
```

</details>

#### replays quit (UIEvent.Quit)

- replays quit (UIEvent.Quit)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays quit (UIEvent.Quit)")
val sc = load_trace(_trace("quit"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "Quit").to_be_true()
```

</details>

#### replays action_focus (UIEvent.Action)

- replays action_focus (UIEvent.Action)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays action_focus (UIEvent.Action)")
val sc = load_trace(_trace("action_focus"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "Action|focus_btn_ok").to_be_true()
```

</details>

#### replays focus_next (UIEvent.FocusNext)

- replays focus_next (UIEvent.FocusNext)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays focus_next (UIEvent.FocusNext)")
val sc = load_trace(_trace("focus_next"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "FocusNext").to_be_true()
```

</details>

#### replays focus_prev (UIEvent.FocusPrev)

- replays focus_prev (UIEvent.FocusPrev)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays focus_prev (UIEvent.FocusPrev)")
val sc = load_trace(_trace("focus_prev"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "FocusPrev").to_be_true()
```

</details>

#### replays command_mode (UIEvent.CommandMode)

- replays command_mode (UIEvent.CommandMode)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays command_mode (UIEvent.CommandMode)")
val sc = load_trace(_trace("command_mode"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "CommandMode").to_be_true()
```

</details>

#### replays normal_mode (UIEvent.NormalMode)

- replays normal_mode (UIEvent.NormalMode)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays normal_mode (UIEvent.NormalMode)")
val sc = load_trace(_trace("normal_mode"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "NormalMode").to_be_true()
```

</details>

#### replays insert_mode (UIEvent.InsertMode)

- replays insert_mode (UIEvent.InsertMode)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays insert_mode (UIEvent.InsertMode)")
val sc = load_trace(_trace("insert_mode"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "InsertMode").to_be_true()
```

</details>

#### replays touch_press (UIEvent.TouchPress)

- replays touch_press (UIEvent.TouchPress)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays touch_press (UIEvent.TouchPress)")
val sc = load_trace(_trace("touch_press"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "TouchPress|120|240").to_be_true()
```

</details>

#### replays touch_move (UIEvent.TouchMove, multi-sample)

- replays touch_move (UIEvent.TouchMove, multi-sample)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays touch_move (UIEvent.TouchMove, multi-sample)")
val sc = load_trace(_trace("touch_move"))
val out = run_scenario(sc)
val first = out[0]
val last = out[2]
val n = arr_len_text(out)
val len_ok = n == 3
expect(len_ok).to_be_true()
expect(first == "TouchMove|130|240").to_be_true()
expect(last == "TouchMove|150|250").to_be_true()
```

</details>

#### replays touch_release (UIEvent.TouchRelease)

- replays touch_release (UIEvent.TouchRelease)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays touch_release (UIEvent.TouchRelease)")
val sc = load_trace(_trace("touch_release"))
val out = run_scenario(sc)
val v = out[0]
val n = arr_len_text(out)
val len_ok = n == 1
expect(len_ok).to_be_true()
expect(v == "TouchRelease|150|250").to_be_true()
```

</details>

#### replays touch_drag_sequence (composite press/move/release)

- replays touch_drag_sequence (composite press/move/release)


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("replays touch_drag_sequence (composite press/move/release)")
val sc = load_trace(_trace("touch_drag_sequence"))
val out = run_scenario(sc)
val v0 = out[0]
val v1 = out[1]
val v2 = out[2]
val v3 = out[3]
val n = arr_len_text(out)
val len_ok = n == 4
expect(len_ok).to_be_true()
expect(v0 == "TouchPress|10|10").to_be_true()
expect(v1 == "TouchMove|20|15").to_be_true()
expect(v2 == "TouchMove|30|20").to_be_true()
expect(v3 == "TouchRelease|40|25").to_be_true()
```

</details>

#### deferred Phase-2/3 variants

#### documents KeyDown/KeyUp distinct from KeyPress (phase 2)

- documents KeyDown/KeyUp distinct from KeyPress (phase 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents KeyDown/KeyUp distinct from KeyPress (phase 2)")
# Needs UIEvent reshape — see plan doc §2.1
expect(true).to_be_true()
```

</details>

#### documents Modifier shift/ctrl/alt/meta snapshot (phase 2)

- documents Modifier shift/ctrl/alt/meta snapshot (phase 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents Modifier shift/ctrl/alt/meta snapshot (phase 2)")
# Modifier state lives in InputBackend trait, not UIEvent — plan §2.2
expect(true).to_be_true()
```

</details>

#### documents Scroll/Wheel dx,dy (phase 3)

- documents Scroll/Wheel dx,dy (phase 3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents Scroll/Wheel dx,dy (phase 3)")
# Completely absent from UIEvent today — plan §2.3
expect(true).to_be_true()
```

</details>

#### documents PointerEnter/PointerLeave hover (phase 2)

- documents PointerEnter/PointerLeave hover (phase 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents PointerEnter/PointerLeave hover (phase 2)")
# Plan §2.4
expect(true).to_be_true()
```

</details>

#### documents window-level FocusGained/FocusLost (phase 2)

- documents window-level FocusGained/FocusLost (phase 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents window-level FocusGained/FocusLost (phase 2)")
# Plan §2.5
expect(true).to_be_true()
```

</details>

#### documents IME ImeComposeStart/Update/Commit/Cancel (phase 3)

- documents IME ImeComposeStart/Update/Commit/Cancel (phase 3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents IME ImeComposeStart/Update/Commit/Cancel (phase 3)")
# Plan §2.6
expect(true).to_be_true()
```

</details>

#### documents CloseRequested distinct from Quit (phase 2)

- documents CloseRequested distinct from Quit (phase 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents CloseRequested distinct from Quit (phase 2)")
# Plan §2.7 — currently EVENT_CLOSE is collapsed to KeyPress(Escape)
expect(true).to_be_true()
```

</details>

#### documents DoubleClick/TripleClick click-count (phase 3)

- documents DoubleClick/TripleClick click-count (phase 3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMMON
step("documents DoubleClick/TripleClick click-count (phase 3)")
# Plan §2.8
expect(true).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/common/ui/input_event_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering input event conformance suite (phase 1, in-process).
- input event conformance suite (phase 1, in-process)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMMON`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ecca6ab876f7d0e89ce1ce1655d9912a9920e28398275817fa7025e170ca487`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ecca6ab876f7d0e89ce1ce1655d9912a9920e28398275817fa7025e170ca487`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ecca6ab876f7d0e89ce1ce1655d9912a9920e28398275817fa7025e170ca487`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/common/ui/input_event_conformance_spec.spl
mirror: doc/06_spec/01_unit/common/ui/input_event_conformance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/common/ui/input_event_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/common/ui/input_event_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/common/ui/input_event_conformance_spec.spl:329:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders KeyPress with key argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/ui/input_event_conformance_spec.spl:335:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders Resize with width and height' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/common/ui/input_event_conformance_spec.spl:341:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders all unit variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
