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
| Updated | 2026-08-18 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = coauthor_new(coauthor_fixture(), "alice")
assert_equal(coauthor_revision(session), 0)
```

</details>

#### bumps the revision by 1 per local edit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = coauthor_fixture()
var session = coauthor_new(coauthor_fixture(), "alice")
session = coauthor_local_edit(session, "C1", "alice-edit")
val lines = coauthor_broadcast(session, base)
assert_equal(lines.len(), 1)
assert_equal(lines[0], "op|set|C1|alice-edit")
```

</details>

#### advances the revision by the number of ops merged

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
