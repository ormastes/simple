# Editor Wincmd Specification

> Tests covering wincmd dispatch — struct and function, commands — split and resize entries, keybindings — wincmd prefix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Wincmd Specification

## Scenarios

### wincmd dispatch — struct and function

#### defines WincmdResult struct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines WincmdResult struct
   - Expected: src contains `struct WincmdResult:`
   - Expected: src contains `handled: bool`
   - Expected: src contains `message: text`
   - Expected: src contains `quit: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WincmdResult struct")
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("struct WincmdResult:")).to_equal(true)
expect(src.contains("handled: bool")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("quit: bool")).to_equal(true)
```

</details>

#### defines wincmd_dispatch function

- defines wincmd_dispatch function
   - Expected: src contains `fn wincmd_dispatch(session: EditSession, key: text, rects: [SplitRect]) -> Wi... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines wincmd_dispatch function")
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("fn wincmd_dispatch(session: EditSession, key: text, rects: [SplitRect]) -> WincmdResult")).to_equal(true)
```

</details>

#### handles focus direction keys h/j/k/l

- handles focus direction keys h/j/k/l
   - Expected: src contains `focus_direction("left"`
   - Expected: src contains `focus_direction("down"`
   - Expected: src contains `focus_direction("up"`
   - Expected: src contains `focus_direction("right"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles focus direction keys h/j/k/l")
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("focus_direction(\"left\"")).to_equal(true)
expect(src.contains("focus_direction(\"down\"")).to_equal(true)
expect(src.contains("focus_direction(\"up\"")).to_equal(true)
expect(src.contains("focus_direction(\"right\"")).to_equal(true)
```

</details>

#### handles swap keys H/J/K/L

- handles swap keys H/J/K/L
   - Expected: src contains `split_find_neighbor`
   - Expected: src contains `session.layout.tree.swap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles swap keys H/J/K/L")
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("split_find_neighbor")).to_equal(true)
expect(src.contains("session.layout.tree.swap")).to_equal(true)
```

</details>

#### handles split keys v and s

- handles split keys v and s
   - Expected: src contains `session.split_editor()`
   - Expected: src contains `session.split_editor_horizontal()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles split keys v and s")
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("session.split_editor()")).to_equal(true)
expect(src.contains("session.split_editor_horizontal()")).to_equal(true)
```

</details>

#### handles close and only keys c/q/o

- handles close and only keys c/q/o
   - Expected: src contains `session.close_active_group()`
   - Expected: src contains `session.close_other_groups()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles close and only keys c/q/o")
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("session.close_active_group()")).to_equal(true)
expect(src.contains("session.close_other_groups()")).to_equal(true)
```

</details>

#### handles resize keys +/- and equalize =

- handles resize keys +/- and equalize =
   - Expected: src contains `session.layout.tree.resize`
   - Expected: src contains `session.layout.tree.equalize()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles resize keys +/- and equalize =")
val src = read_text("src/lib/editor/view/wincmd.spl")
expect(src.contains("session.layout.tree.resize")).to_equal(true)
expect(src.contains("session.layout.tree.equalize()")).to_equal(true)
```

</details>

### commands — split and resize entries

#### has split-horizontal and split-vertical dispatch

- has split-horizontal and split-vertical dispatch
   - Expected: src contains `"split-horizontal"`
   - Expected: src contains `"split-vertical"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has split-horizontal and split-vertical dispatch")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"split-horizontal\"")).to_equal(true)
expect(src.contains("\"split-vertical\"")).to_equal(true)
```

</details>

#### has close-other-groups command

- has close-other-groups command
   - Expected: src contains `"close-other-groups"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has close-other-groups command")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"close-other-groups\"")).to_equal(true)
```

</details>

#### has resize-grow and resize-shrink commands

- has resize-grow and resize-shrink commands
   - Expected: src contains `"resize-grow"`
   - Expected: src contains `"resize-shrink"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has resize-grow and resize-shrink commands")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"resize-grow\"")).to_equal(true)
expect(src.contains("\"resize-shrink\"")).to_equal(true)
```

</details>

#### parses :sp and :vs commandline aliases

- parses :sp and :vs commandline aliases
   - Expected: src contains `"sp"`
   - Expected: src contains `"vs"`
   - Expected: src contains `"only"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses :sp and :vs commandline aliases")
val src = read_text("src/app/editor/commands.spl")
expect(src.contains("\"sp\"")).to_equal(true)
expect(src.contains("\"vs\"")).to_equal(true)
expect(src.contains("\"only\"")).to_equal(true)
```

</details>

### keybindings — wincmd prefix

#### has ctrl_w binding for wincmd-prefix in normal mode

- has ctrl_w binding for wincmd-prefix in normal mode
   - Expected: src contains `ctrl_w`
   - Expected: src contains `wincmd-prefix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has ctrl_w binding for wincmd-prefix in normal mode")
val src = read_text("src/lib/editor/00.common/keybindings.spl")
expect(src.contains("ctrl_w")).to_equal(true)
expect(src.contains("wincmd-prefix")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_wincmd_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wincmd dispatch — struct and function, commands — split and resize entries, keybindings — wincmd prefix.
- wincmd dispatch — struct and function
- commands — split and resize entries
- keybindings — wincmd prefix

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

- Canonical SPipe generation for source `36bda9e5a3daca53fea7314b5a9bf66b8e2b54201471b37be2afe663bc649fca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36bda9e5a3daca53fea7314b5a9bf66b8e2b54201471b37be2afe663bc649fca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36bda9e5a3daca53fea7314b5a9bf66b8e2b54201471b37be2afe663bc649fca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_wincmd_spec.spl
mirror: doc/06_spec/03_system/gui/editor_wincmd_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_wincmd_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_wincmd_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_wincmd_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines WincmdResult struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_wincmd_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines wincmd_dispatch function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_wincmd_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles focus direction keys h/j/k/l' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
