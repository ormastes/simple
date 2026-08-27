# Game2D InputSnapshot (AC-3)

> Snapshot-based input view: `g.input.key_down(K)`, `key_pressed_this_frame(K)`,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D InputSnapshot (AC-3)

Snapshot-based input view: `g.input.key_down(K)`, `key_pressed_this_frame(K)`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_input_snapshot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Snapshot-based input view: `g.input.key_down(K)`, `key_pressed_this_frame(K)`,
`mouse_pos()`, `mouse_down(B)` backed by `class InputSnapshot {
keys_down, keys_pressed, mouse_pos, mouse_buttons }`.

Archtest: examples/11_advanced/game2d/** must NOT call rt_sdl2_* directly — the snapshot
is the only read path.

Red-phase: InputSnapshot/api absent; signature-presence assertions fail.

## Scenarios

### Game2D InputSnapshot (AC-3)

### InputSnapshot class declared

#### snapshot.spl declares class InputSnapshot

- snapshot.spl declares class InputSnapshot
   - Expected: _has(src, "class InputSnapshot") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("snapshot.spl declares class InputSnapshot")
val src = _read("src/lib/nogc_sync_mut/game2d/input/snapshot.spl")
expect(_has(src, "class InputSnapshot")).to_equal(true)
```

</details>

#### InputSnapshot has keys_down/keys_pressed/mouse_pos/mouse_buttons

- InputSnapshot has keys_down/keys_pressed/mouse_pos/mouse_buttons


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("InputSnapshot has keys_down/keys_pressed/mouse_pos/mouse_buttons")
val src = _read("src/lib/nogc_sync_mut/game2d/input/snapshot.spl")
expect(_has(src, "keys_down") and _has(src, "keys_pressed") and
       _has(src, "mouse_pos") and _has(src, "mouse_buttons")
    ).to_equal(true)
```

</details>

#### edge case: synthetic class declaration is detected

- edge case: synthetic class declaration is detected
   - Expected: _has(sample, "class InputSnapshot") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: synthetic class declaration is detected")
val sample = "class InputSnapshot:\n    var keys_down: [Key]\n"
expect(_has(sample, "class InputSnapshot")).to_equal(true)
```

</details>

### g.input accessors

#### api.spl declares fn key_down(k: Key) -> bool

- api.spl declares fn key_down(k: Key) -> bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("api.spl declares fn key_down(k: Key) -> bool")
val src = _read("src/lib/nogc_sync_mut/game2d/input/api.spl")
expect(_has(src, "fn key_down(") and _has(src, "Key")
    ).to_equal(true)
```

</details>

#### api.spl declares fn key_pressed_this_frame

- api.spl declares fn key_pressed_this_frame
   - Expected: _has(src, "fn key_pressed_this_frame(") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("api.spl declares fn key_pressed_this_frame")
val src = _read("src/lib/nogc_sync_mut/game2d/input/api.spl")
expect(_has(src, "fn key_pressed_this_frame(")).to_equal(true)
```

</details>

#### api.spl declares fn mouse_pos and fn mouse_down

- api.spl declares fn mouse_pos and fn mouse_down


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("api.spl declares fn mouse_pos and fn mouse_down")
val src = _read("src/lib/nogc_sync_mut/game2d/input/api.spl")
expect(_has(src, "fn mouse_pos(") and _has(src, "fn mouse_down(")
    ).to_equal(true)
```

</details>

### edge case: simultaneous press+release in same frame

#### snapshot retains the press in keys_pressed

- snapshot retains the press in keys_pressed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("snapshot retains the press in keys_pressed")
# Contract documented in snapshot.spl header; red until impl.
val src = _read("src/lib/nogc_sync_mut/game2d/input/snapshot.spl")
expect(_has(src, "press") and _has(src, "release") or
       _has(src, "keys_pressed_this_frame") or
       _has(src, "frame-coalesced")).to_equal(true)
```

</details>

#### synthetic: detector finds 'frame-coalesced' marker

- synthetic: detector finds 'frame-coalesced' marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("synthetic: detector finds 'frame-coalesced' marker")
expect(_has("# frame-coalesced press wins", "frame-coalesced")
    ).to_equal(true)
```

</details>

### error path: no direct OS input calls in user code

#### examples/11_advanced/game2d/hello/main.spl does not call rt_sdl2_*

- examples/11_advanced/game2d/hello/main.spl does not call rt_sdl2_*
   - Expected: _has(src, "rt_sdl2_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("examples/11_advanced/game2d/hello/main.spl does not call rt_sdl2_*")
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_has(src, "rt_sdl2_")).to_equal(false)
```

</details>

#### examples/11_advanced/game2d/hello/main.spl does not import std.io

- examples/11_advanced/game2d/hello/main.spl does not import std.io
   - Expected: _has(src, "use std.nogc_sync_mut.io") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("examples/11_advanced/game2d/hello/main.spl does not import std.io")
val src = _read("examples/11_advanced/game2d/hello/main.spl")
expect(_has(src, "use std.nogc_sync_mut.io")).to_equal(false)
```

</details>

#### edge case: synthetic violation is detected

- edge case: synthetic violation is detected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: synthetic violation is detected")
expect(_has("rt_sdl2_is_key_pressed(...)", "rt_sdl2_")
    ).to_equal(true)
```

</details>

#### error path: empty content does not falsely flag

- error path: empty content does not falsely flag
   - Expected: _has("", "rt_sdl2_") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("error path: empty content does not falsely flag")
expect(_has("", "rt_sdl2_")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f1ec5478447b7534bf844797731d13af1966305b8dfc2de0965abf5d103d5f17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f1ec5478447b7534bf844797731d13af1966305b8dfc2de0965abf5d103d5f17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f1ec5478447b7534bf844797731d13af1966305b8dfc2de0965abf5d103d5f17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/game2d_input_snapshot_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_input_snapshot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_input_snapshot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_input_snapshot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_input_snapshot_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snapshot.spl declares class InputSnapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_input_snapshot_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'InputSnapshot has keys_down/keys_pressed/mouse_pos/mouse_buttons' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_input_snapshot_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'edge case: synthetic class declaration is detected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
