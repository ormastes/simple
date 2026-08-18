# Word Footnotes Specification

> Tests covering insert_footnote: auto-numbering in document order, insert_footnote: renumbering on out-of-order insert (middle), delete_note: renumbering after removal, footnotes vs endnotes: independent numbering sequences, render_footnotes / render_endnotes: notes section rendering, complex workflow: insert, delete, and re-render.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Word Footnotes Specification

## Scenarios

### insert_footnote: auto-numbering in document order

#### assigns number 1 to the first footnote

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val coll = notes_new()
val coll1 = insert_footnote(coll, 0, 5, "first note")
val fns = footnotes(coll1)
expect(fns.len()).to_equal(1)
expect(fns.get(0).number).to_equal(1)
expect(fns.get(0).text).to_equal("first note")
```

</details>

#### numbers footnotes sequentially by insertion at increasing positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 5, "alpha")
coll = insert_footnote(coll, 1, 2, "beta")
coll = insert_footnote(coll, 2, 0, "gamma")
val fns = footnotes(coll)
expect(fns.len()).to_equal(3)
expect(fns.get(0).number).to_equal(1)
expect(fns.get(0).text).to_equal("alpha")
expect(fns.get(1).number).to_equal(2)
expect(fns.get(1).text).to_equal("beta")
expect(fns.get(2).number).to_equal(3)
expect(fns.get(2).text).to_equal("gamma")
```

</details>

### insert_footnote: renumbering on out-of-order insert (middle)

#### renumbers existing footnotes when a new one is inserted in the middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "first")
coll = insert_footnote(coll, 5, 0, "third")
# Insert "second" between the two existing anchors (para 2 < 5)
coll = insert_footnote(coll, 2, 0, "second")
val fns = footnotes(coll)
expect(fns.len()).to_equal(3)
expect(fns.get(0).text).to_equal("first")
expect(fns.get(0).number).to_equal(1)
expect(fns.get(1).text).to_equal("second")
expect(fns.get(1).number).to_equal(2)
expect(fns.get(2).text).to_equal("third")
expect(fns.get(2).number).to_equal(3)
```

</details>

#### renumbers when inserted before the very first footnote

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 3, 0, "was-first")
coll = insert_footnote(coll, 0, 0, "now-first")
val fns = footnotes(coll)
expect(fns.get(0).text).to_equal("now-first")
expect(fns.get(0).number).to_equal(1)
expect(fns.get(1).text).to_equal("was-first")
expect(fns.get(1).number).to_equal(2)
```

</details>

### delete_note: renumbering after removal
_Deleting a footnote closes the numbering gap for the remaining notes._

#### renumbers remaining footnotes after deleting the first one

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "first")
coll = insert_footnote(coll, 1, 0, "second")
coll = insert_footnote(coll, 2, 0, "third")
val to_delete = footnotes(coll).get(0)
coll = delete_note(coll, to_delete.id)
val fns = footnotes(coll)
expect(fns.len()).to_equal(2)
expect(fns.get(0).text).to_equal("second")
expect(fns.get(0).number).to_equal(1)
expect(fns.get(1).text).to_equal("third")
expect(fns.get(1).number).to_equal(2)
```

</details>

#### renumbers remaining footnotes after deleting a middle one

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "first")
coll = insert_footnote(coll, 1, 0, "second")
coll = insert_footnote(coll, 2, 0, "third")
val middle = footnotes(coll).get(1)
coll = delete_note(coll, middle.id)
val fns = footnotes(coll)
expect(fns.len()).to_equal(2)
expect(fns.get(0).text).to_equal("first")
expect(fns.get(0).number).to_equal(1)
expect(fns.get(1).text).to_equal("third")
expect(fns.get(1).number).to_equal(2)
```

</details>

#### leaves the collection unchanged when deleting an unknown id

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "only")
coll = delete_note(coll, 999)
val fns = footnotes(coll)
expect(fns.len()).to_equal(1)
expect(fns.get(0).text).to_equal("only")
expect(fns.get(0).number).to_equal(1)
```

</details>

### footnotes vs endnotes: independent numbering sequences

#### numbers footnotes and endnotes independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "fn-a")
coll = insert_endnote(coll, 0, 5, "en-a")
coll = insert_footnote(coll, 1, 0, "fn-b")
coll = insert_endnote(coll, 1, 5, "en-b")
val fns = footnotes(coll)
val ens = endnotes(coll)
expect(fns.len()).to_equal(2)
expect(ens.len()).to_equal(2)
expect(fns.get(0).number).to_equal(1)
expect(fns.get(1).number).to_equal(2)
expect(ens.get(0).number).to_equal(1)
expect(ens.get(1).number).to_equal(2)
```

</details>

#### does not renumber endnotes when a footnote is inserted or deleted

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_endnote(coll, 0, 0, "end-1")
coll = insert_endnote(coll, 1, 0, "end-2")
coll = insert_footnote(coll, 0, 1, "note-1")
val ens_before = endnotes(coll)
expect(ens_before.get(0).number).to_equal(1)
expect(ens_before.get(1).number).to_equal(2)
val fn_id = footnotes(coll).get(0).id
coll = delete_note(coll, fn_id)
val ens_after = endnotes(coll)
expect(ens_after.len()).to_equal(2)
expect(ens_after.get(0).number).to_equal(1)
expect(ens_after.get(0).text).to_equal("end-1")
expect(ens_after.get(1).number).to_equal(2)
expect(ens_after.get(1).text).to_equal("end-2")
```

</details>

#### reports separate footnote_count and endnote_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "fn-a")
coll = insert_footnote(coll, 1, 0, "fn-b")
coll = insert_endnote(coll, 0, 0, "en-a")
expect(footnote_count(coll)).to_equal(2)
expect(endnote_count(coll)).to_equal(1)
```

</details>

### render_footnotes / render_endnotes: notes section rendering

#### renders an empty collection as an empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val coll = notes_new()
expect(render_footnotes(coll)).to_equal("")
expect(render_endnotes(coll)).to_equal("")
```

</details>

#### renders a single footnote as a numbered line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "hello")
expect(render_footnotes(coll)).to_equal("1. hello")
```

</details>

#### renders multiple footnotes as a numbered block

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "alpha")
coll = insert_footnote(coll, 1, 0, "beta")
coll = insert_footnote(coll, 2, 0, "gamma")
val rendered = render_footnotes(coll)
expect(rendered).to_equal("1. alpha\n2. beta\n3. gamma")
```

</details>

#### renders endnotes separately from footnotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "a footnote")
coll = insert_endnote(coll, 0, 0, "an endnote")
expect(render_footnotes(coll)).to_equal("1. a footnote")
expect(render_endnotes(coll)).to_equal("1. an endnote")
```

</details>

#### renders the notes section in document order after out-of-order insert

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 5, 0, "later")
coll = insert_footnote(coll, 1, 0, "earlier")
val rendered = render_footnotes(coll)
expect(rendered).to_equal("1. earlier\n2. later")
```

</details>

### complex workflow: insert, delete, and re-render

#### reflects renumbering in rendered output after a middle delete

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var coll = notes_new()
coll = insert_footnote(coll, 0, 0, "one")
coll = insert_footnote(coll, 1, 0, "two")
coll = insert_footnote(coll, 2, 0, "three")
val to_delete = footnotes(coll).get(1)
coll = delete_note(coll, to_delete.id)
expect(render_footnotes(coll)).to_equal("1. one\n2. three")
expect(footnote_count(coll)).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/word_footnotes_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering insert_footnote: auto-numbering in document order, insert_footnote: renumbering on out-of-order insert (middle), delete_note: renumbering after removal, footnotes vs endnotes: independent numbering sequences, render_footnotes / render_endnotes: notes section rendering, complex workflow: insert, delete, and re-render.
- insert_footnote: auto-numbering in document order
- insert_footnote: renumbering on out-of-order insert (middle)
- delete_note: renumbering after removal
- footnotes vs endnotes: independent numbering sequences
- render_footnotes / render_endnotes: notes section rendering
- complex workflow: insert, delete, and re-render

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
