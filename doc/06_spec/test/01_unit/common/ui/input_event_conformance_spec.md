# Input Event Conformance Specification

> <details>

<!-- sdn-diagram:id=input_event_conformance_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=input_event_conformance_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

input_event_conformance_spec -> std
input_event_conformance_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=input_event_conformance_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = render_event(UIEvent.KeyPress(key: "a"))
expect(s == "KeyPress|a").to_be_true()
```

</details>

#### renders Resize with width and height

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = render_event(UIEvent.Resize(width: 800, height: 600))
expect(s == "Resize|800|600").to_be_true()
```

</details>

#### renders all unit variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = render_event(UIEvent.TouchPress(x: 1, y: 2))
val m = render_event(UIEvent.TouchMove(x: 3, y: 4))
val r = render_event(UIEvent.TouchRelease(x: 5, y: 6))
expect(p == "TouchPress|1|2").to_be_true()
expect(m == "TouchMove|3|4").to_be_true()
expect(r == "TouchRelease|5|6").to_be_true()
```

</details>

#### renders Action with name argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = render_event(UIEvent.Action(name: "focus_btn_ok"))
expect(s == "Action|focus_btn_ok").to_be_true()
```

</details>

#### in-process backend queues UIEvents in order

#### starts with an empty queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = InProcessInputBackend.create()
val snap = backend.snapshot()
val n = arr_len_event(snap)
val empty = n == 0
expect(empty).to_be_true()
```

</details>

#### snapshots pushed events in FIFO order

1. backend push
2. backend push
3. backend push


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. backend push
2. backend clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Needs UIEvent reshape — see plan doc §2.1
expect(true).to_be_true()
```

</details>

#### documents Modifier shift/ctrl/alt/meta snapshot (phase 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Modifier state lives in InputBackend trait, not UIEvent — plan §2.2
expect(true).to_be_true()
```

</details>

#### documents Scroll/Wheel dx,dy (phase 3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Completely absent from UIEvent today — plan §2.3
expect(true).to_be_true()
```

</details>

#### documents PointerEnter/PointerLeave hover (phase 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Plan §2.4
expect(true).to_be_true()
```

</details>

#### documents window-level FocusGained/FocusLost (phase 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Plan §2.5
expect(true).to_be_true()
```

</details>

#### documents IME ImeComposeStart/Update/Commit/Cancel (phase 3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Plan §2.6
expect(true).to_be_true()
```

</details>

#### documents CloseRequested distinct from Quit (phase 2)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Plan §2.7 — currently EVENT_CLOSE is collapsed to KeyPress(Escape)
expect(true).to_be_true()
```

</details>

#### documents DoubleClick/TripleClick click-count (phase 3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
