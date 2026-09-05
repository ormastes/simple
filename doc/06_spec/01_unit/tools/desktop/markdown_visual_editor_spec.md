# Markdown Visual Editor Specification

> <details>

<!-- sdn-diagram:id=markdown_visual_editor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=markdown_visual_editor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

markdown_visual_editor_spec -> std
markdown_visual_editor_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=markdown_visual_editor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Visual Editor Specification

## Scenarios

### markdown visual editor model

#### recognizes markdown paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_visual_is_markdown_path("/home/notes/os.md")).to_equal(true)
expect(markdown_visual_is_markdown_path("/home/notes/os.txt")).to_equal(false)
```

</details>

#### uses the first heading as the note title

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_visual_title("/home/notes/os.md", "# SimpleOS\nbody")).to_equal("SimpleOS")
```

</details>

#### falls back to the file basename

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_visual_title("/home/notes/os.md", "body")).to_equal("os")
```

</details>

#### extracts visual blocks and preview lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blocks = markdown_visual_blocks("# Title\n- task")
val rows = markdown_visual_preview_lines("# Title\n- task")

expect(blocks[0].kind).to_equal("heading")
expect(blocks[1].kind).to_equal("bullet")
expect(rows[0]).to_equal("Title")
expect(rows[1]).to_equal("* task")
```

</details>

#### extracts wiki links

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("See [[Kernel]] and [[Packages]].")

expect(links).to_contain("Kernel")
expect(links).to_contain("Packages")
```

</details>

#### creates a complete visual note

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val note = markdown_visual_note("/home/notes/os.md", "# OS\nSee [[Kernel]].")

expect(note.title).to_equal("OS")
expect(note.wiki_links[0]).to_equal("Kernel")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/desktop/markdown_visual_editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown visual editor model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
