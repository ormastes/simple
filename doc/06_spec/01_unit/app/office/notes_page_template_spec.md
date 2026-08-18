# notes_page_template_spec

> OneNote-style page templates spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# notes_page_template_spec

OneNote-style page templates spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/notes_page_template_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

OneNote-style page templates spec.

A PageTemplate (name + kind) instantiates into a TemplatePage: a title plus
a list of pre-seeded lines/sections appropriate to the kind. Covers the
catalog (list/find), instantiation per kind, and applying a template to an
existing empty page.

## Scenarios

### page templates: catalog
_list_templates exposes every OneNote-style template kind._

#### lists exactly the seven built-in templates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val templates = list_templates()
expect(templates.len()).to_equal(7)
```

</details>

#### names cover every kind in catalog order

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = template_names()
expect(names.len()).to_equal(7)
expect(names).to_contain("Blank Page")
expect(names).to_contain("Lined Page")
expect(names).to_contain("Grid Page")
expect(names).to_contain("To Do List")
expect(names).to_contain("Meeting Notes")
expect(names).to_contain("Lecture Notes")
expect(names).to_contain("Project Overview")
```

</details>

#### kind_name gives a human-readable label per kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(kind_name(PageTemplateKind.MeetingNotes)).to_equal("Meeting Notes")
expect(kind_name(PageTemplateKind.ToDoList)).to_equal("To Do List")
expect(kind_name(PageTemplateKind.GridPaper)).to_equal("Grid")
```

</details>

#### find_template locates a built-in template by exact name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = find_template("Lecture Notes")
expect(found.name).to_equal("Lecture Notes")
expect(kind_name(found.kind)).to_equal("Lecture Notes")
```

</details>

#### find_template falls back to an empty Blank template for an unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = find_template("Does Not Exist")
expect(missing.name).to_equal("")
expect(kind_name(missing.kind)).to_equal("Blank")
```

</details>

### page templates: instantiate seeds content per kind
_instantiate() builds a starter TemplatePage seeded per the kind._

#### blank seeds no lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Blank Page")
val page = instantiate(tpl, "")
expect(page.title).to_equal("Untitled Page")
expect(page.lines.len()).to_equal(0)
```

</details>

#### lined seeds twenty blank ruled lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Lined Page")
val page = instantiate(tpl, "")
expect(page.lines.len()).to_equal(20)
expect(page.lines[0]).to_equal("")
expect(page.lines[19]).to_equal("")
```

</details>

#### grid seeds twelve blank squared rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Grid Page")
val page = instantiate(tpl, "")
expect(page.lines.len()).to_equal(12)
expect(page.lines[0]).to_equal("")
```

</details>

#### to_do_list seeds an empty checklist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("To Do List")
val page = instantiate(tpl, "")
expect(page.lines.len()).to_equal(0)
expect(page.title).to_equal("To Do List")
```

</details>

#### meeting_notes seeds Attendees, Agenda, Action Items in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Meeting Notes")
val page = instantiate(tpl, "")
expect(page.lines.len()).to_equal(3)
expect(page.lines[0]).to_equal("Attendees")
expect(page.lines[1]).to_equal("Agenda")
expect(page.lines[2]).to_equal("Action Items")
```

</details>

#### lecture_notes seeds Topic, Key Points, Summary, Questions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Lecture Notes")
val page = instantiate(tpl, "")
expect(page.lines.len()).to_equal(4)
expect(page.lines[0]).to_equal("Topic")
expect(page.lines[3]).to_equal("Questions")
```

</details>

#### project_overview seeds Objective, Scope, Milestones, Risks, Owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Project Overview")
val page = instantiate(tpl, "")
expect(page.lines.len()).to_equal(5)
expect(page.lines[0]).to_equal("Objective")
expect(page.lines[4]).to_equal("Owner")
```

</details>

#### uses the given title instead of the default when non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Meeting Notes")
val page = instantiate(tpl, "Sprint Planning")
expect(page.title).to_equal("Sprint Planning")
expect(page.lines[0]).to_equal("Attendees")
```

</details>

### page templates: apply to an existing page
_apply_to_empty seeds an existing empty page; leaves content alone._

#### seeds an empty page in place, preserving its title

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tpl = find_template("Project Overview")
val blank_tpl = find_template("Blank Page")
var page = instantiate(blank_tpl, "My Project")
expect(page.lines.len()).to_equal(0)
page = apply_to_empty(tpl, page)
expect(page.title).to_equal("My Project")
expect(page.lines.len()).to_equal(5)
expect(page.lines[0]).to_equal("Objective")
```

</details>

#### is a no-op on a page that already has content

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meeting_tpl = find_template("Meeting Notes")
val todo_tpl = find_template("To Do List")
var page = instantiate(meeting_tpl, "Weekly Sync")
expect(page.lines.len()).to_equal(3)
page = apply_to_empty(todo_tpl, page)
expect(page.lines.len()).to_equal(3)
expect(page.lines[0]).to_equal("Attendees")
```

</details>

#### seed_lines is directly usable without a template wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = seed_lines(PageTemplateKind.ToDoList)
expect(lines.len()).to_equal(0)
val lined = seed_lines(PageTemplateKind.Lined)
expect(lined.len()).to_equal(20)
```

</details>

#### default_title matches kind_name for every non-blank kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_title(PageTemplateKind.MeetingNotes)).to_equal("Meeting Notes")
expect(default_title(PageTemplateKind.LectureNotes)).to_equal("Lecture Notes")
expect(default_title(PageTemplateKind.ProjectOverview)).to_equal("Project Overview")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
