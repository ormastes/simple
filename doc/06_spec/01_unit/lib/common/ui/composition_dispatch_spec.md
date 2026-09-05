# IME Composition Dispatch Spec

> `UIEvent.CompositionUpdate` / `CompositionCommit` are the IME (input-method editor) composition events used for CJK/accented text input, where a single committed character can be more than one Unicode codepoint and the host shows an in-progress "preedit" string before the user confirms it. This spec drives the full sequence through the public `process_event(state, event) -> state` reducer, mirroring the DragStart/ DragDrop dispatch spec's style: `CompositionUpdate` must show the preedit without mutating the focused input's committed `value`/`caret`, and `CompositionCommit` must insert the committed STRING at the caret (char-indexed, not byte-indexed, so multi-byte UTF-8 like "你好" is not corrupted) and clear the preedit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IME Composition Dispatch Spec

`UIEvent.CompositionUpdate` / `CompositionCommit` are the IME (input-method editor) composition events used for CJK/accented text input, where a single committed character can be more than one Unicode codepoint and the host shows an in-progress "preedit" string before the user confirms it. This spec drives the full sequence through the public `process_event(state, event) -> state` reducer, mirroring the DragStart/ DragDrop dispatch spec's style: `CompositionUpdate` must show the preedit without mutating the focused input's committed `value`/`caret`, and `CompositionCommit` must insert the committed STRING at the caret (char-indexed, not byte-indexed, so multi-byte UTF-8 like "你好" is not corrupted) and clear the preedit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/composition_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`UIEvent.CompositionUpdate` / `CompositionCommit` are the IME (input-method
editor) composition events used for CJK/accented text input, where a single
committed character can be more than one Unicode codepoint and the host
shows an in-progress "preedit" string before the user confirms it. This
spec drives the full sequence through the public
`process_event(state, event) -> state` reducer, mirroring the DragStart/
DragDrop dispatch spec's style: `CompositionUpdate` must show the preedit
without mutating the focused input's committed `value`/`caret`, and
`CompositionCommit` must insert the committed STRING at the caret
(char-indexed, not byte-indexed, so multi-byte UTF-8 like "你好" is not
corrupted) and clear the preedit.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

A tree with a single focused text input: an update shows a preedit without
touching value/caret, then a commit of "你好" inserts both characters at the
caret and clears the preedit.

## Scenarios

### IME composition — process_event reducer path

#### CompositionUpdate sets a preedit prop without touching value or caret

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- CompositionUpdate sets a preedit prop without touching value or caret
- Focus the input, then send an in-progress composition update
   - Expected: WidgetNode(id: "upd_field").get_prop("preedit") equals `n`
   - Expected: WidgetNode(id: "upd_field").get_prop("value") equals `abc`
   - Expected: WidgetNode(id: "upd_field").get_prop("caret") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CompositionUpdate sets a preedit prop without touching value or caret")
step("Focus the input, then send an in-progress composition update")
var state = composition_state("upd")
WidgetNode(id: "upd_field").set_prop("value", "abc")
WidgetNode(id: "upd_field").set_prop("caret", "3")
state = process_event(state, UIEvent.CompositionUpdate(text: "n"))

expect(WidgetNode(id: "upd_field").get_prop("preedit")).to_equal("n")
expect(WidgetNode(id: "upd_field").get_prop("value")).to_equal("abc")
expect(WidgetNode(id: "upd_field").get_prop("caret")).to_equal("3")
```

</details>

#### CompositionCommit inserts a multi-char CJK string at the caret and clears preedit

- CompositionCommit inserts a multi-char CJK string at the caret and clears preedit
- Focus the input, show a preedit, then commit 你好 at caret position 0
- Both CJK characters landed (char-indexed, not byte-corrupted)
   - Expected: WidgetNode(id: "commit_field").get_prop("value") equals `你好`
   - Expected: WidgetNode(id: "commit_field").get_prop("caret") equals `2`
   - Expected: WidgetNode(id: "commit_field").get_prop("preedit") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CompositionCommit inserts a multi-char CJK string at the caret and clears preedit")
step("Focus the input, show a preedit, then commit 你好 at caret position 0")
var state = composition_state("commit")
WidgetNode(id: "commit_field").set_prop("value", "")
state = process_event(state, UIEvent.CompositionUpdate(text: "n"))
state = process_event(state, UIEvent.CompositionCommit(text: "你好"))

step("Both CJK characters landed (char-indexed, not byte-corrupted)")
expect(WidgetNode(id: "commit_field").get_prop("value")).to_equal("你好")
expect(WidgetNode(id: "commit_field").get_prop("caret")).to_equal("2")
expect(WidgetNode(id: "commit_field").get_prop("preedit")).to_equal("")
```

</details>

#### CompositionCommit inserts at the caret, preserving text on both sides

- CompositionCommit inserts at the caret, preserving text on both sides
- Commit into the middle of existing text
   - Expected: WidgetNode(id: "mid_field").get_prop("value") equals `abc`
   - Expected: WidgetNode(id: "mid_field").get_prop("caret") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CompositionCommit inserts at the caret, preserving text on both sides")
step("Commit into the middle of existing text")
var state = composition_state("mid")
WidgetNode(id: "mid_field").set_prop("value", "ac")
WidgetNode(id: "mid_field").set_prop("caret", "1")
state = process_event(state, UIEvent.CompositionCommit(text: "b"))

expect(WidgetNode(id: "mid_field").get_prop("value")).to_equal("abc")
expect(WidgetNode(id: "mid_field").get_prop("caret")).to_equal("2")
```

</details>

#### CompositionUpdate/Commit on no focused widget is a no-op

- CompositionUpdate/Commit on no focused widget is a no-op
- No FocusEvent sent — focused_id is empty
   - Expected: WidgetNode(id: "nofocus_field").get_prop("preedit") equals ``
   - Expected: WidgetNode(id: "nofocus_field").get_prop("value") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CompositionUpdate/Commit on no focused widget is a no-op")
step("No FocusEvent sent — focused_id is empty")
val root = column("nofocus_root", [text_input("nofocus_field", "x")])
var state = UIState.new(build_tree(root))
state = process_event(state, UIEvent.CompositionUpdate(text: "n"))
state = process_event(state, UIEvent.CompositionCommit(text: "n"))

expect(WidgetNode(id: "nofocus_field").get_prop("preedit")).to_equal("")
expect(WidgetNode(id: "nofocus_field").get_prop("value")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b617a6a5086d98e8e526791132495f59ab355bb35912141dc5dedb62c30e5c9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b617a6a5086d98e8e526791132495f59ab355bb35912141dc5dedb62c30e5c9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b617a6a5086d98e8e526791132495f59ab355bb35912141dc5dedb62c30e5c9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/composition_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/composition_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/composition_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/composition_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/composition_dispatch_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CompositionUpdate sets a preedit prop without touching value or caret' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/composition_dispatch_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CompositionCommit inserts a multi-char CJK string at the caret and clears preedit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/composition_dispatch_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CompositionCommit inserts at the caret, preserving text on both sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
