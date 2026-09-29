# coauthor_spec

> Office sheets live co-authoring spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coauthor_spec

Office sheets live co-authoring spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/coauthor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office sheets live co-authoring spec.

CoauthorSession over app.office.sheets.sync: session construction at
revision 0, local edits bumping revision by 1, broadcast producing
sync.spl wire-format op lines vs a shared base, merge_incoming parsing and
replaying those lines with revision advancing by the number of ops applied,
THE co-authoring convergence law (two peers who exchange disjoint edits end
up with identical sheets), and last-writer-wins semantics on a cell both
peers edited (the side merged LAST wins).

## Scenarios

### coauthor: session basics

#### starts a new session at revision 0

- starts a new session at revision 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts a new session at revision 0")
val session = coauthor_new(coauthor_fixture(), "alice")
assert_equal(coauthor_revision(session), 0)
```

</details>

#### bumps the revision by 1 per local edit

- bumps the revision by 1 per local edit


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bumps the revision by 1 per local edit")
var session = coauthor_new(coauthor_fixture(), "alice")
session = coauthor_local_edit(session, "C1", "first")
assert_equal(coauthor_revision(session), 1)
session = coauthor_local_edit(session, "D1", "second")
assert_equal(coauthor_revision(session), 2)
assert_equal(cell_display_text(session.sheet.get_cell("C1")), "first")
assert_equal(cell_display_text(session.sheet.get_cell("D1")), "second")
```

</details>

### coauthor: broadcast and merge

#### broadcasts only the local edits as ops vs the shared base

- broadcasts only the local edits as ops vs the shared base


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("broadcasts only the local edits as ops vs the shared base")
val base = coauthor_fixture()
var session = coauthor_new(coauthor_fixture(), "alice")
session = coauthor_local_edit(session, "C1", "alice-edit")
val lines = coauthor_broadcast(session, base)
assert_equal(lines.len(), 1)
assert_equal(lines[0], "op|set|C1|alice-edit")
```

</details>

#### advances the revision by the number of ops merged

- advances the revision by the number of ops merged


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances the revision by the number of ops merged")
val base = coauthor_fixture()
var alice = coauthor_new(coauthor_fixture(), "alice")
var bob = coauthor_new(coauthor_fixture(), "bob")
bob = coauthor_local_edit(bob, "C1", "bob-c1")
bob = coauthor_local_edit(bob, "D1", "bob-d1")
val bob_lines = coauthor_broadcast(bob, base)
assert_equal(bob_lines.len(), 2)
alice = coauthor_merge_incoming(alice, bob_lines)
assert_equal(coauthor_revision(alice), 2)
```

</details>

### coauthor: convergence law

#### two peers exchanging disjoint edits converge to identical sheets

- two peers exchanging disjoint edits converge to identical sheets


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two peers exchanging disjoint edits converge to identical sheets")
val base = coauthor_fixture()
var alice = coauthor_new(coauthor_fixture(), "alice")
var bob = coauthor_new(coauthor_fixture(), "bob")

alice = coauthor_local_edit(alice, "C1", "alice-edit")
bob = coauthor_local_edit(bob, "D1", "bob-edit")

val alice_lines = coauthor_broadcast(alice, base)
val bob_lines = coauthor_broadcast(bob, base)

alice = coauthor_merge_incoming(alice, bob_lines)
bob = coauthor_merge_incoming(bob, alice_lines)

# Both peers now hold both edits.
assert_equal(cell_display_text(alice.sheet.get_cell("C1")), "alice-edit")
assert_equal(cell_display_text(alice.sheet.get_cell("D1")), "bob-edit")
assert_equal(cell_display_text(bob.sheet.get_cell("C1")), "alice-edit")
assert_equal(cell_display_text(bob.sheet.get_cell("D1")), "bob-edit")

# Ground truth: the convergence law itself — every touched cell
# matches between the two independently-derived sheets.
assert_equal(
    cell_display_text(alice.sheet.get_cell("A1")),
    cell_display_text(bob.sheet.get_cell("A1")))
assert_equal(
    cell_display_text(alice.sheet.get_cell("B1")),
    cell_display_text(bob.sheet.get_cell("B1")))
assert_equal(
    cell_display_text(alice.sheet.get_cell("C1")),
    cell_display_text(bob.sheet.get_cell("C1")))
assert_equal(
    cell_display_text(alice.sheet.get_cell("D1")),
    cell_display_text(bob.sheet.get_cell("D1")))

assert_equal(coauthor_revision(alice), 2)
assert_equal(coauthor_revision(bob), 2)
```

</details>

### coauthor: last-writer-wins

#### the side merged LAST wins on a cell both peers edited

- the side merged LAST wins on a cell both peers edited


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the side merged LAST wins on a cell both peers edited")
val base = coauthor_fixture()
var alice = coauthor_new(coauthor_fixture(), "alice")
var bob = coauthor_new(coauthor_fixture(), "bob")

# Both edit the SAME cell, A1.
alice = coauthor_local_edit(alice, "A1", "alice-A1")
bob = coauthor_local_edit(bob, "A1", "bob-A1")

val bob_lines = coauthor_broadcast(bob, base)

# Alice merges Bob's ops in AFTER her own local edit — Bob's
# incoming "set" replays via Sheet.set_value and overwrites
# Alice's local value. The side merged LAST (Bob, here) wins.
alice = coauthor_merge_incoming(alice, bob_lines)
assert_equal(cell_display_text(alice.sheet.get_cell("A1")), "bob-A1")
assert_equal(coauthor_revision(alice), 2)
```

</details>

#### probe: merging zero ops leaves the cell and revision alone (deliberate check)

- probe: merging zero ops leaves the cell and revision alone (deliberate check)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe: merging zero ops leaves the cell and revision alone (deliberate check)")
val base = coauthor_fixture()
var alice = coauthor_new(coauthor_fixture(), "alice")
alice = coauthor_local_edit(alice, "A1", "alice-only")
alice = coauthor_merge_incoming(alice, [])
assert_equal(cell_display_text(alice.sheet.get_cell("A1")), "alice-only")
assert_equal(coauthor_revision(alice), 1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `486e0fa21c0c17dbcc05ba8a76a7563f04c0cc42f09f05c59d794bb9ab5a4b26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `486e0fa21c0c17dbcc05ba8a76a7563f04c0cc42f09f05c59d794bb9ab5a4b26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `486e0fa21c0c17dbcc05ba8a76a7563f04c0cc42f09f05c59d794bb9ab5a4b26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/app/office/sheets/coauthor_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/coauthor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/coauthor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/coauthor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/coauthor_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/office/sheets/coauthor_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts a new session at revision 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/coauthor_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bumps the revision by 1 per local edit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/coauthor_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'broadcasts only the local edits as ops vs the shared base' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
