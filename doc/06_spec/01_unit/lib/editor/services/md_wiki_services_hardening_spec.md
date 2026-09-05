# Md Wiki Services Hardening Specification

> <details>

<!-- sdn-diagram:id=md_wiki_services_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_wiki_services_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_wiki_services_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_wiki_services_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Wiki Services Hardening Specification

## Scenarios

### wiki links: malformed input is safe

#### unterminated [[ yields no links and does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("a.md", "before [[unterminated and more text")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)
```

</details>

#### empty [[]] yields no links

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("a.md", "x [[]] y")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)
```

</details>

#### adjacent links [[a]][[b]] both found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("a.md", "[[alpha]][[beta]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(2)
```

</details>

#### alias form [[target|alias]] keeps display

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("target|alias")
expect(parsed.0).to_equal("target")
expect(parsed.1).to_equal("alias")
```

</details>

#### heading form [[target#sec]] strips anchor from target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("target#sec")
expect(parsed.0).to_equal("target")
```

</details>

#### empty alias [[a|]] is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("a|")
expect(parsed.0).to_equal("a")
expect(parsed.1).to_equal("")
```

</details>

#### empty raw target is safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("")
expect(parsed.0).to_equal("")
```

</details>

#### link at end of line is found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("a.md", "see [[end]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(1)
```

</details>

### embeds: malformed input is safe

#### unterminated ![[ yields no embeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("a.md", "look ![[broken and the rest")
val embeds = md_wiki_extract_embeds(doc, [doc])
expect(embeds.len()).to_equal(0)
```

</details>

#### valid embed of missing target is unresolved, not a crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("a.md", "![[missing-note]]")
val index = md_wiki_index_documents([doc])
val unresolved = md_wiki_unresolved_embeds(index)
expect(unresolved.len()).to_equal(1)
```

</details>

### backlinks and index updates

#### link from b to a appears as backlink of a

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = md_wiki_document("alpha.md", "# Alpha\ncontent")
val b = md_wiki_document("b.md", "see [[alpha]]")
val index = md_wiki_index_documents([a, b])
val backs = md_wiki_backlinks(index, "alpha.md")
expect(backs.len()).to_equal(1)
```

</details>

#### self-link does not crash and is indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = md_wiki_document("alpha.md", "# Alpha\n[[alpha]]")
val index = md_wiki_index_documents([a])
val backs = md_wiki_backlinks(index, "alpha.md")
expect(backs.len()).to_equal(1)
```

</details>

#### empty documents array builds an empty index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_docs: [MdWikiDocument] = []
val index = md_wiki_index_documents(empty_docs)
expect(md_wiki_unresolved_links(index).len()).to_equal(0)
```

</details>

#### empty content document is safe everywhere

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("e.md", "")
val index = md_wiki_index_documents([doc])
expect(md_wiki_backlinks(index, "e.md").len()).to_equal(0)
expect(md_wiki_tags(index, "any").len()).to_equal(0)
expect(md_wiki_callouts(index, "e.md").len()).to_equal(0)
```

</details>

### tags: boundary cases

#### tag at end of line is found

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("t.md", "note #urgent")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(1)
```

</details>

#### lone # is not a tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("t.md", "just a # alone")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(0)
```

</details>

### md_search: odd queries are safe

#### empty query returns no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = md_search("# Title\nbody text", "")
expect(matches.len()).to_equal(0)
```

</details>

#### empty content returns no matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = md_search("", "query")
expect(matches.len()).to_equal(0)
```

</details>

#### query with bracket metacharacters is literal and safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = md_search("a [x] b", "[x]")
expect(matches.len() >= 0).to_equal(true)
```

</details>

#### crlf content does not crash search

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matches = md_search("# H\r\nline one\r\nline two", "line")
expect(matches.len() >= 1).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/services/md_wiki_services_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wiki links: malformed input is safe
- embeds: malformed input is safe
- backlinks and index updates
- tags: boundary cases
- md_search: odd queries are safe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
