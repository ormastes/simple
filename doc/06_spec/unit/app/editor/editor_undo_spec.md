# Editor Undo Specification

> Verifies that the TextEditor undo stack correctly captures line snapshots before each mutating operation and restores them on undo, bounded at 50 entries (oldest dropped when full).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Undo Specification

Verifies that the TextEditor undo stack correctly captures line snapshots before each mutating operation and restores them on undo, bounded at 50 entries (oldest dropped when full).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B2 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/app/editor/editor_undo_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the TextEditor undo stack correctly captures line snapshots
before each mutating operation and restores them on undo, bounded at 50
entries (oldest dropped when full).

## Scenarios

### TextEditor undo

#### insert then undo restores original state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- insert then undo restores original state
   - Expected: ed.lines[0] equals `before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("insert then undo restores original state")
var ed = TextEditor.new()
# initial state: one empty line
val before = ed.lines[0]
ed.insert_char("a")
ed.insert_char("b")
ed.undo()
ed.undo()
expect(ed.lines[0]).to_equal(before)
```

</details>

#### undo on empty stack shows message

- undo on empty stack shows message
   - Expected: ed.status_message equals `Already at oldest change`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undo on empty stack shows message")
var ed = TextEditor.new()
ed.undo()
expect(ed.status_message).to_equal("Already at oldest change")
```

</details>

#### undo stack bounded at 50 entries

- undo stack bounded at 50 entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undo stack bounded at 50 entries")
var ed = TextEditor.new()
var i = 0
while i < 60:
    ed.insert_char("x")
    i = i + 1
# Stack must not exceed 50
expect(ed.undo_stack.len()).to_be_less_than(51)
```

</details>

#### undo after delete_char restores line

- undo after delete_char restores line
   - Expected: ed.lines[0] equals `before_delete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undo after delete_char restores line")
var ed = TextEditor.new()
ed.insert_char("h")
ed.insert_char("i")
# move cursor back and delete
ed.cursor_col = 1
val before_delete = ed.lines[0]
ed.delete_char()
ed.undo()
expect(ed.lines[0]).to_equal(before_delete)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3baed6a0bcaa03f096b70a2abe0823ea01d17344eb546fe88f8e96ef7b670b4a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3baed6a0bcaa03f096b70a2abe0823ea01d17344eb546fe88f8e96ef7b670b4a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3baed6a0bcaa03f096b70a2abe0823ea01d17344eb546fe88f8e96ef7b670b4a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/editor/editor_undo_spec.spl
mirror: doc/06_spec/unit/app/editor/editor_undo_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/editor/editor_undo_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/editor/editor_undo_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/editor/editor_undo_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'insert then undo restores original state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/editor/editor_undo_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'undo on empty stack shows message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/editor/editor_undo_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'undo stack bounded at 50 entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
