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
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Markdown Visual Editor Specification

## Scenarios

### markdown_visual_wiki_links edge cases

#### returns empty for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("")
expect(links.len()).to_equal(0)
```

</details>

#### handles unterminated [[ without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("[[unterminated")
expect(links.len()).to_equal(0)
```

</details>

#### ignores ]] with no opener

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("text]] more")
expect(links.len()).to_equal(0)
```

</details>

#### ignores empty [[]]

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("[[]]")
expect(links.len()).to_equal(0)
```

</details>

#### extracts adjacent links

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("[[Alpha]][[Beta]]")
expect(links.len()).to_equal(2)
expect(links[0]).to_equal("Alpha")
expect(links[1]).to_equal("Beta")
```

</details>

#### extracts multiple links with surrounding text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("See [[Kernel]] and [[Packages]].")
expect(links).to_contain("Kernel")
expect(links).to_contain("Packages")
```

</details>

#### handles single valid link

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val links = markdown_visual_wiki_links("[[MyNote]]")
expect(links.len()).to_equal(1)
expect(links[0]).to_equal("MyNote")
```

</details>

### markdown_visual_title CRLF

#### strips CR from CRLF heading lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_visual_title("/a/note.md", "# Title\r\nbody")).to_equal("Title")
```

</details>

#### falls back to basename when no heading

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(markdown_visual_title("/a/note.md", "just body")).to_equal("note")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/markdown/markdown_visual_editor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown_visual_wiki_links edge cases
- markdown_visual_title CRLF

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
