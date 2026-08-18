# notes_spec

> Notes (OneNote pillar MVP) spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# notes_spec

Notes (OneNote pillar MVP) spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/notes_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Notes (OneNote pillar MVP) spec.

Hierarchical notebooks (notebook -> sections -> pages on the RichDocument
model), quick capture via markdown, full-text search, and directory
persistence (one markdown file per page + index.md manifest).

Duplicate-title policy under test: a title is unique WITHIN a section —
add_page on an existing (section, title) replaces the body; move_page is a
no-op when the target section already holds the title.

## Scenarios

### notes: notebook structure
_Notebook -> sections -> pages held in flat parallel arrays._

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = notebook_new("Fresh")
expect(nb.name).to_equal("Fresh")
expect(nb.section_names.len()).to_equal(0)
expect(nb.page_titles.len()).to_equal(0)
```

</details>

#### adds sections in order, idempotently

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = notebook_new("N")
nb = add_section(nb, "A")
nb = add_section(nb, "B")
nb = add_section(nb, "A")
expect(nb.section_names.len()).to_equal(2)
expect(nb.section_names[0]).to_equal("A")
expect(nb.section_names[1]).to_equal("B")
```

</details>

#### add_page auto-creates its section

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = notebook_new("N")
nb = add_page(nb, "Inbox", "Quick note", "captured on the go")
expect(nb.section_names.len()).to_equal(1)
expect(nb.section_names[0]).to_equal("Inbox")
expect(nb.page_titles.len()).to_equal(1)
```

</details>

#### parses page markdown into a RichDocument

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = _demo_notebook()
val doc = get_page(nb, "Work", "Standup")
expect(doc.blocks.len()).to_equal(2)
val heading = block_to_plain_text(doc.blocks[0])
expect(heading).to_equal("Standup")
```

</details>

#### lists page titles per section only

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = _demo_notebook()
val work = page_titles_in(nb, "Work")
expect(work.len()).to_equal(2)
expect(work[0]).to_equal("Standup")
expect(work[1]).to_equal("Roadmap")
val personal = page_titles_in(nb, "Personal")
expect(personal.len()).to_equal(1)
expect(personal[0]).to_equal("Groceries")
```

</details>

#### get_page on a missing page returns an empty untitled document

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = _demo_notebook()
val doc = get_page(nb, "Work", "Nope")
expect(doc.title).to_equal("")
expect(doc.blocks.len()).to_equal(0)
```

</details>

#### replaces the body when re-adding an existing (section, title)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = _demo_notebook()
nb = add_page(nb, "Work", "Standup", "updated agenda")
expect(nb.page_titles.len()).to_equal(3)
val doc = get_page(nb, "Work", "Standup")
expect(doc.blocks.len()).to_equal(1)
val body = block_to_plain_text(doc.blocks[0])
expect(body).to_equal("updated agenda")
```

</details>

#### removes only the targeted page

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = _demo_notebook()
nb = remove_page(nb, "Work", "Standup")
expect(nb.page_titles.len()).to_equal(2)
val work = page_titles_in(nb, "Work")
expect(work.len()).to_equal(1)
expect(work[0]).to_equal("Roadmap")
```

</details>

#### moves a page between sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = _demo_notebook()
nb = move_page(nb, "Groceries", "Work")
val work = page_titles_in(nb, "Work")
expect(work.len()).to_equal(3)
val personal = page_titles_in(nb, "Personal")
expect(personal.len()).to_equal(0)
```

</details>

#### move_page auto-creates a fresh target section

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = _demo_notebook()
nb = move_page(nb, "Roadmap", "Archive")
expect(nb.section_names.len()).to_equal(3)
val archived = page_titles_in(nb, "Archive")
expect(archived.len()).to_equal(1)
expect(archived[0]).to_equal("Roadmap")
```

</details>

#### move_page is a no-op when the target holds the same title

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = _demo_notebook()
nb = add_page(nb, "Personal", "Standup", "personal standup notes")
nb = move_page(nb, "Standup", "Personal")
val work = page_titles_in(nb, "Work")
expect(work.len()).to_equal(2)
val personal = page_titles_in(nb, "Personal")
expect(personal.len()).to_equal(2)
```

</details>

### notes: full-text search
_Case-insensitive substring search; one hit per page._

#### returns section|title|line for a body hit

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = _demo_notebook()
val hits = notes_search(nb, "blockers")
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal("Work|Standup|Discuss roadmap and blockers.")
```

</details>

#### counts title matches, using the title as the matching line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = _demo_notebook()
val hits = notes_search(nb, "grocer")
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal("Personal|Groceries|Groceries")
```

</details>

#### matches case-insensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = _demo_notebook()
val hits = notes_search(nb, "ROADMAP")
expect(hits.len()).to_equal(2)
expect(hits[0]).to_equal("Work|Standup|Discuss roadmap and blockers.")
expect(hits[1]).to_equal("Work|Roadmap|Roadmap")
```

</details>

#### returns no hits for an absent term or empty query

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nb = _demo_notebook()
val none = notes_search(nb, "zeppelin")
expect(none.len()).to_equal(0)
val empty = notes_search(nb, "")
expect(empty.len()).to_equal(0)
```

</details>

#### reports only the first matching line of a page

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = notebook_new("N")
nb = add_page(nb, "S", "P", "alpha match one\n\nalpha match two")
val hits = notes_search(nb, "alpha")
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal("S|P|alpha match one")
```

</details>

### notes: persistence
_Save to <dir>/<section>/<title>.md + index.md; load rebuilds._

#### round-trips a notebook through a build/ temp dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mkdir_p("build/tmp")
val dir = "build/tmp/notes_spec_rt"
val nb = _demo_notebook()
val ok = notebook_save(nb, dir)
expect(ok).to_equal(true)
val back = notebook_load(dir)
expect(back.name).to_equal("Demo")
expect(back.page_titles.len()).to_equal(3)
val doc = get_page(back, "Work", "Roadmap")
val body = block_to_plain_text(doc.blocks[1])
expect(body).to_equal("Q3 priorities: search and sync.")
```

</details>

#### preserves empty sections and section membership across save/load

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mkdir_p("build/tmp")
val dir = "build/tmp/notes_spec_rt_empty"
var nb = _demo_notebook()
nb = add_section(nb, "Someday")
notebook_save(nb, dir)
val back = notebook_load(dir)
expect(back.section_names.len()).to_equal(3)
expect(back.section_names[2]).to_equal("Someday")
val personal = page_titles_in(back, "Personal")
expect(personal.len()).to_equal(1)
expect(personal[0]).to_equal("Groceries")
```

</details>

#### loading a missing directory yields an empty notebook

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val back = notebook_load("build/tmp/notes_spec_absent_dir")
expect(back.name).to_equal("")
expect(back.page_titles.len()).to_equal(0)
```

</details>

### notes: macro API
_office_api exposes notes to user macros._

#### builds and searches a notebook through macros

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nb = macro_notes_new("Macro NB")
nb = macro_notes_add_page(nb, "Ideas", "Pitch", "An office suite that is its own macro language.")
nb = macro_notes_add_page(nb, "Ideas", "Names", "Working title: simple notes")
val hits = macro_notes_search(nb, "macro language")
expect(hits.len()).to_equal(1)
expect(hits[0]).to_equal("Ideas|Pitch|An office suite that is its own macro language.")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
