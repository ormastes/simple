# notes_tags_spec

> Notes tags (OneNote pillar) spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# notes_tags_spec

Notes tags (OneNote pillar) spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/notes_tags_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Notes tags (OneNote pillar) spec.

OneNote-style note tags: apply a tag (name + kind) to a note item
identified by (section, title, line); mark a "to_do" tag done/undone;
remove a tag; list the tags on one note item; and a tag rollup/search
("Find Tags") that scans the whole store for every note item carrying a
given tag kind. Pure data-structure logic, no I/O.

## Scenarios

### notes tags: apply
_apply_tag adds a (section, title, line, kind) row, defaulting done to false._

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = tag_store_new()
expect(store.entry_sections.len()).to_equal(0)
```

</details>

#### applies a tag to a note item

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = tag_store_new()
store = apply_tag(store, "Work", "Standup", 0, "Follow up with design", "to_do")
val tags = tags_on(store, "Work", "Standup", 0)
expect(tags.len()).to_equal(1)
expect(tags[0].name).to_equal("Follow up with design")
expect(tags[0].kind).to_equal("to_do")
assert_false(tags[0].done)
```

</details>

#### allows two different tag kinds on the same note item

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = tag_store_new()
store = apply_tag(store, "Work", "Standup", 0, "Ping design", "to_do")
store = apply_tag(store, "Work", "Standup", 0, "Owner unclear", "important")
val tags = tags_on(store, "Work", "Standup", 0)
expect(tags.len()).to_equal(2)
expect(tags[0].kind).to_equal("to_do")
expect(tags[1].kind).to_equal("important")
```

</details>

#### re-applying the same kind to the same note item is idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = tag_store_new()
store = apply_tag(store, "Work", "Standup", 0, "Ping design", "to_do")
store = mark_tag_done(store, "Work", "Standup", 0, true)
store = apply_tag(store, "Work", "Standup", 0, "Ping design again", "to_do")
val tags = tags_on(store, "Work", "Standup", 0)
expect(tags.len()).to_equal(1)
expect(tags[0].name).to_equal("Ping design")
assert_true(tags[0].done)
```

</details>

### notes tags: done/undone
_mark_tag_done toggles the "to_do" row for one note item._

#### marks a to_do tag done

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = _demo_store()
store = mark_tag_done(store, "Work", "Standup", 0, true)
val tags = tags_on(store, "Work", "Standup", 0)
assert_true(tags[0].done)
```

</details>

#### marks a done to_do tag undone again

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = _demo_store()
store = mark_tag_done(store, "Work", "Standup", 0, true)
store = mark_tag_done(store, "Work", "Standup", 0, false)
val tags = tags_on(store, "Work", "Standup", 0)
assert_false(tags[0].done)
```

</details>

#### does not disturb a different note item's done state

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = _demo_store()
store = mark_tag_done(store, "Work", "Standup", 0, true)
val other = tags_on(store, "Work", "Standup", 2)
assert_false(other[0].done)
```

</details>

#### is a no-op when the note item has no to_do tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = _demo_store()
store = mark_tag_done(store, "Work", "Roadmap", 1, true)
val tags = tags_on(store, "Work", "Roadmap", 1)
expect(tags.len()).to_equal(1)
assert_false(tags[0].done)
```

</details>

### notes tags: remove and list
_remove_tag deletes one row; tags_on lists a single note item's tags._

#### removes only the targeted tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = _demo_store()
store = remove_tag(store, "Work", "Standup", 0, "to_do")
val tags = tags_on(store, "Work", "Standup", 0)
expect(tags.len()).to_equal(0)
val still_there = tags_on(store, "Work", "Standup", 2)
expect(still_there.len()).to_equal(1)
```

</details>

#### removing an absent tag is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = _demo_store()
store = remove_tag(store, "Work", "Standup", 0, "important")
val tags = tags_on(store, "Work", "Standup", 0)
expect(tags.len()).to_equal(1)
```

</details>

#### lists no tags for a note item that has none

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = _demo_store()
val tags = tags_on(store, "Personal", "Groceries", 5)
expect(tags.len()).to_equal(0)
```

</details>

### notes tags: rollup / find tags
_find_tags scans the whole store for one kind, across every page._

#### finds all to_do tags across the notebook

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = _demo_store()
val hits = find_tags(store, "to_do")
expect(hits.len()).to_equal(3)
expect(hits).to_contain("Work|Standup|0|Follow up with design|false")
expect(hits).to_contain("Work|Standup|2|Confirm ship date|false")
expect(hits).to_contain("Personal|Groceries|0|Buy milk|false")
```

</details>

#### reflects done state in the rollup

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = _demo_store()
store = mark_tag_done(store, "Personal", "Groceries", 0, true)
val hits = find_tags(store, "to_do")
expect(hits).to_contain("Personal|Groceries|0|Buy milk|true")
```

</details>

#### finds tags of a kind that has exactly one hit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = _demo_store()
val hits = find_tags(store, "question")
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal("Work|Roadmap|1|Scope unclear|false")
```

</details>

#### returns no hits for a kind with no applications

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = _demo_store()
val hits = find_tags(store, "contact")
expect(hits.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
