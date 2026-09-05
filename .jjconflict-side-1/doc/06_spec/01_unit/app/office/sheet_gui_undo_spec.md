# Sheet Gui Undo Specification

> Tests covering sheet GUI undo/redo (SheetGuiHistory + undoable session entry points).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sheet Gui Undo Specification

## Scenarios

### sheet GUI undo/redo (SheetGuiHistory + undoable session entry points)

#### starts with an empty history: no undo, no redo

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with an empty history: no undo, no redo
   - Expected: history_can_undo(h) is false
   - Expected: history_can_redo(h) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with an empty history: no undo, no redo")
val h = history_new()
expect(history_can_undo(h)).to_equal(false)
expect(history_can_redo(h)).to_equal(false)
```

</details>

#### history_record enables undo and leaves the cursor at the end (no redo)

- history_record enables undo and leaves the cursor at the end (no redo)
   - Expected: history_can_undo(h) is true
   - Expected: history_can_redo(h) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("history_record enables undo and leaves the cursor at the end (no redo)")
var h = history_new()
h = history_record(h, "B2", "10", "40")
expect(history_can_undo(h)).to_equal(true)
expect(history_can_redo(h)).to_equal(false)
```

</details>

#### commits a valid edit, recalculates dependents, and records history

- commits a valid edit, recalculates dependents, and records history
   - Expected: out.last_error equals ``
   - Expected: _cell(out.session, "B2") equals `40`
   - Expected: _cell(out.session, "D2") equals `80`
   - Expected: history_can_undo(out.history) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("commits a valid edit, recalculates dependents, and records history")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val out = session_edit_undoable(session, history_new(), "B2", "40", vrules)
expect(out.last_error).to_equal("")
expect(_cell(out.session, "B2")).to_equal("40")
expect(_cell(out.session, "D2")).to_equal("80")
expect(history_can_undo(out.history)).to_equal(true)
```

</details>

#### undo restores the previous value AND recalculates dependents

- undo restores the previous value AND recalculates dependents
   - Expected: out.last_error equals ``
   - Expected: _cell(out.session, "B2") equals `10`
   - Expected: _cell(out.session, "D2") equals `20`
   - Expected: history_can_redo(out.history) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undo restores the previous value AND recalculates dependents")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val edited = session_edit_undoable(session, history_new(), "B2", "40", vrules)
val out = session_undo(edited.session, edited.history)
expect(out.last_error).to_equal("")
expect(_cell(out.session, "B2")).to_equal("10")
expect(_cell(out.session, "D2")).to_equal("20")
expect(history_can_redo(out.history)).to_equal(true)
```

</details>

#### redo re-applies the undone edit with recalculation

- redo re-applies the undone edit with recalculation
   - Expected: out.last_error equals ``
   - Expected: _cell(out.session, "B2") equals `40`
   - Expected: _cell(out.session, "D2") equals `80`
   - Expected: history_can_redo(out.history) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("redo re-applies the undone edit with recalculation")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val edited = session_edit_undoable(session, history_new(), "B2", "40", vrules)
val undone = session_undo(edited.session, edited.history)
val out = session_redo(undone.session, undone.history)
expect(out.last_error).to_equal("")
expect(_cell(out.session, "B2")).to_equal("40")
expect(_cell(out.session, "D2")).to_equal("80")
expect(history_can_redo(out.history)).to_equal(false)
```

</details>

#### undoing a formula-cell overwrite restores the formula TEXT, not the cached value

- undoing a formula-cell overwrite restores the formula TEXT, not the cached value
   - Expected: _cell(edited.session, "D2") equals `99`
   - Expected: out.last_error equals ``
   - Expected: _cell(out.session, "D2") equals `20`
   - Expected: _cell(after_b2, "D2") equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undoing a formula-cell overwrite restores the formula TEXT, not the cached value")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "D2")
val vrules = empty_validation_rules()
# overwrite the =B2*C2 formula (displaying 20) with a literal 99
val edited = session_edit_undoable(session, history_new(), "D2", "99", vrules)
expect(_cell(edited.session, "D2")).to_equal("99")
val out = session_undo(edited.session, edited.history)
expect(out.last_error).to_equal("")
expect(_cell(out.session, "D2")).to_equal("20")
# PROOF it came back as a LIVE formula: a later B2 edit re-recalcs D2.
# A cached-value restore ("20" literal) would leave D2 stuck at 20.
val after_b2 = session_edit(out.session, "B2", "40")
expect(_cell(after_b2, "D2")).to_equal("80")
```

</details>

#### undo at the beginning of history fails closed with nothing-to-undo

- undo at the beginning of history fails closed with nothing-to-undo
   - Expected: out.last_error equals `nothing-to-undo`
   - Expected: _cell(out.session, "B2") equals `10`
   - Expected: _cell(out.session, "D2") equals `20`
   - Expected: history_can_undo(out.history) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undo at the beginning of history fails closed with nothing-to-undo")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val out = session_undo(session, history_new())
expect(out.last_error).to_equal("nothing-to-undo")
expect(_cell(out.session, "B2")).to_equal("10")
expect(_cell(out.session, "D2")).to_equal("20")
expect(history_can_undo(out.history)).to_equal(false)
```

</details>

#### redo at the end of history fails closed with nothing-to-redo

- redo at the end of history fails closed with nothing-to-redo
   - Expected: out.last_error equals `nothing-to-redo`
   - Expected: _cell(out.session, "B2") equals `40`
   - Expected: _cell(out.session, "D2") equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("redo at the end of history fails closed with nothing-to-redo")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val edited = session_edit_undoable(session, history_new(), "B2", "40", vrules)
val out = session_redo(edited.session, edited.history)
expect(out.last_error).to_equal("nothing-to-redo")
expect(_cell(out.session, "B2")).to_equal("40")
expect(_cell(out.session, "D2")).to_equal("80")
```

</details>

#### a new edit after undo truncates the redo tail

- a new edit after undo truncates the redo tail
   - Expected: history_can_redo(undone.history) is true
   - Expected: fresh.last_error equals ``
   - Expected: history_can_redo(fresh.history) is false
   - Expected: out.last_error equals `nothing-to-redo`
   - Expected: _cell(out.session, "B2") equals `60`
   - Expected: _cell(out.session, "D2") equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a new edit after undo truncates the redo tail")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val edited = session_edit_undoable(session, history_new(), "B2", "40", vrules)
val undone = session_undo(edited.session, edited.history)
expect(history_can_redo(undone.history)).to_equal(true)
val fresh = session_edit_undoable(undone.session, undone.history, "B2", "60", vrules)
expect(fresh.last_error).to_equal("")
expect(history_can_redo(fresh.history)).to_equal(false)
val out = session_redo(fresh.session, fresh.history)
expect(out.last_error).to_equal("nothing-to-redo")
expect(_cell(out.session, "B2")).to_equal("60")
expect(_cell(out.session, "D2")).to_equal("120")
```

</details>

#### a validation-rejected edit records NOTHING and leaves the session unchanged

- a validation-rejected edit records NOTHING and leaves the session unchanged
   - Expected: out.last_error equals `Price must be a whole number between 1 and 100`
   - Expected: _cell(out.session, "B2") equals `10`
   - Expected: _cell(out.session, "D2") equals `20`
   - Expected: history_can_undo(out.history) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a validation-rejected edit records NOTHING and leaves the session unchanged")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
val out = session_edit_undoable(session, history_new(), "B2", "999", vrules)
expect(out.last_error).to_equal("Price must be a whole number between 1 and 100")
expect(_cell(out.session, "B2")).to_equal("10")
expect(_cell(out.session, "D2")).to_equal("20")
expect(history_can_undo(out.history)).to_equal(false)
```

</details>

#### walks a multi-edit sequence back and forward: undo x2 then redo x1

- walks a multi-edit sequence back and forward: undo x2 then redo x1
   - Expected: _cell(e2.session, "D2") equals `100`
   - Expected: _cell(u1.session, "B2") equals `40`
   - Expected: _cell(u1.session, "D2") equals `80`
   - Expected: _cell(u2.session, "B2") equals `10`
   - Expected: _cell(u2.session, "D2") equals `20`
   - Expected: r1.last_error equals ``
   - Expected: _cell(r1.session, "B2") equals `40`
   - Expected: _cell(r1.session, "D2") equals `80`
   - Expected: history_can_redo(r1.history) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("walks a multi-edit sequence back and forward: undo x2 then redo x1")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val e1 = session_edit_undoable(session, history_new(), "B2", "40", vrules)
val e2 = session_edit_undoable(e1.session, e1.history, "B2", "50", vrules)
expect(_cell(e2.session, "D2")).to_equal("100")
val u1 = session_undo(e2.session, e2.history)
expect(_cell(u1.session, "B2")).to_equal("40")
expect(_cell(u1.session, "D2")).to_equal("80")
val u2 = session_undo(u1.session, u1.history)
expect(_cell(u2.session, "B2")).to_equal("10")
expect(_cell(u2.session, "D2")).to_equal("20")
val r1 = session_redo(u2.session, u2.history)
expect(r1.last_error).to_equal("")
expect(_cell(r1.session, "B2")).to_equal("40")
expect(_cell(r1.session, "D2")).to_equal("80")
expect(history_can_redo(r1.history)).to_equal(true)
```

</details>

#### commit-on-enter through session_key_undoable records history and ctrl_z undoes it

- commit-on-enter through session_key_undoable records history and ctrl_z undoes it
   - Expected: history_can_undo(out.history) is false
   - Expected: out.last_error equals ``
   - Expected: _cell(out.session, "B2") equals `40`
   - Expected: _cell(out.session, "D2") equals `80`
   - Expected: history_can_undo(out.history) is true
   - Expected: out.last_error equals ``
   - Expected: _cell(out.session, "B2") equals `10`
   - Expected: _cell(out.session, "D2") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("commit-on-enter through session_key_undoable records history and ctrl_z undoes it")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
var out = session_key_undoable(session, history_new(), "4", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "0", 5, 4, 5, 4, vrules)
expect(history_can_undo(out.history)).to_equal(false)
out = session_key_undoable(out.session, out.history, "enter", 5, 4, 5, 4, vrules)
expect(out.last_error).to_equal("")
expect(_cell(out.session, "B2")).to_equal("40")
expect(_cell(out.session, "D2")).to_equal("80")
expect(history_can_undo(out.history)).to_equal(true)
out = session_key_undoable(out.session, out.history, "ctrl_z", 5, 4, 5, 4, vrules)
expect(out.last_error).to_equal("")
expect(_cell(out.session, "B2")).to_equal("10")
expect(_cell(out.session, "D2")).to_equal("20")
```

</details>

#### ctrl_y through session_key_undoable re-applies an undone commit

- ctrl_y through session_key_undoable re-applies an undone commit
   - Expected: out.last_error equals ``
   - Expected: _cell(out.session, "B2") equals `40`
   - Expected: _cell(out.session, "D2") equals `80`
   - Expected: out.last_error equals `nothing-to-redo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ctrl_y through session_key_undoable re-applies an undone commit")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
var out = session_key_undoable(session, history_new(), "4", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "0", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "enter", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "ctrl_z", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "ctrl_y", 5, 4, 5, 4, vrules)
expect(out.last_error).to_equal("")
expect(_cell(out.session, "B2")).to_equal("40")
expect(_cell(out.session, "D2")).to_equal("80")
out = session_key_undoable(out.session, out.history, "ctrl_y", 5, 4, 5, 4, vrules)
expect(out.last_error).to_equal("nothing-to-redo")
```

</details>

#### ctrl_z with empty history fails closed through the key path

- ctrl_z with empty history fails closed through the key path
   - Expected: out.last_error equals `nothing-to-undo`
   - Expected: _cell(out.session, "B2") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ctrl_z with empty history fails closed through the key path")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val out = session_key_undoable(session, history_new(), "ctrl_z", 5, 4, 5, 4, vrules)
expect(out.last_error).to_equal("nothing-to-undo")
expect(_cell(out.session, "B2")).to_equal("10")
```

</details>

#### a validation-rejected enter keeps the buffer and records NOTHING

- a validation-rejected enter keeps the buffer and records NOTHING
   - Expected: out.last_error equals `Price must be a whole number between 1 and 100`
   - Expected: kept.pending_input equals `999`
   - Expected: _cell(out.session, "B2") equals `10`
   - Expected: history_can_undo(out.history) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a validation-rejected enter keeps the buffer and records NOTHING")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
var vrules = empty_validation_rules()
vrules = validation_add(vrules, "B", "whole_number", "", 1.0, 100.0, "", "Price must be a whole number between 1 and 100")
var out = session_key_undoable(session, history_new(), "9", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "9", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "9", 5, 4, 5, 4, vrules)
out = session_key_undoable(out.session, out.history, "enter", 5, 4, 5, 4, vrules)
expect(out.last_error).to_equal("Price must be a whole number between 1 and 100")
val kept = out.session
expect(kept.pending_input).to_equal("999")
expect(_cell(out.session, "B2")).to_equal("10")
expect(history_can_undo(out.history)).to_equal(false)
```

</details>

#### non-committing keys pass through with the history untouched

- non-committing keys pass through with the history untouched
   - Expected: out.last_error equals ``
   - Expected: moved.selected_ref equals `B3`
   - Expected: history_can_undo(out.history) is true
   - Expected: history_can_redo(out.history) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-committing keys pass through with the history untouched")
val sheet = _undo_demo_sheet()
val session = session_new(sheet, "B2")
val vrules = empty_validation_rules()
val edited = session_edit_undoable(session, history_new(), "B2", "40", vrules)
val out = session_key_undoable(edited.session, edited.history, "down", 5, 4, 5, 4, vrules)
expect(out.last_error).to_equal("")
val moved = out.session
expect(moved.selected_ref).to_equal("B3")
expect(history_can_undo(out.history)).to_equal(true)
expect(history_can_redo(out.history)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheet_gui_undo_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sheet GUI undo/redo (SheetGuiHistory + undoable session entry points).
- sheet GUI undo/redo (SheetGuiHistory + undoable session entry points)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `7b2f26c7e4d4aa5a932508e4f03264ed12e770cd0979d8581d0b188b0aa1ea33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b2f26c7e4d4aa5a932508e4f03264ed12e770cd0979d8581d0b188b0aa1ea33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b2f26c7e4d4aa5a932508e4f03264ed12e770cd0979d8581d0b188b0aa1ea33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheet_gui_undo_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheet_gui_undo_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheet_gui_undo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheet_gui_undo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheet_gui_undo_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with an empty history: no undo, no redo' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheet_gui_undo_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'history_record enables undo and leaves the cursor at the end (no redo)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheet_gui_undo_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'commits a valid edit, recalculates dependents, and records history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
