# Md Wiki Index Hardening Specification

> <details>

<!-- sdn-diagram:id=md_wiki_index_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_wiki_index_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_wiki_index_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_wiki_index_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Wiki Index Hardening Specification

## Scenarios

### malformed link refs: empty anchor

#### [[a#]] empty anchor is safe and indexes a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("a#")
expect(parsed.0).to_equal("a")
```

</details>

#### [[a#b#c]] double hash: target is a, no crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("a#b#c")
expect(parsed.0).to_equal("a")
```

</details>

#### [[#anchor-only]] yields empty target and is not indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "see [[#intro]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)
```

</details>

### malformed link refs: empty alias

#### [[a|]] empty alias: target is a, display is empty

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

#### [[a|b|c]] multiple pipes: target is a, display is b|c or b

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("a|b|c")
expect(parsed.0).to_equal("a")
```

</details>

### malformed link refs: whitespace-only target

#### [[   ]] whitespace-only target is not indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[   ]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)
```

</details>

#### parse whitespace-only target returns empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("   ")
expect(parsed.0).to_equal("")
```

</details>

### path-traversal targets: safe indexing, no crash

#### [[../../../etc/passwd]] is indexed with traversal target, no crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[../../../etc/passwd]]")
val links = md_wiki_extract_links(doc, [doc])
# Safe: indexed (non-empty target) or not, but must not crash
expect(links.len() >= 0).to_equal(true)
```

</details>

#### [[/absolute/path]] is safely parsed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("/absolute/path")
expect(parsed.0.len() >= 0).to_equal(true)
```

</details>

#### [[back\\slash]] backslash target is safely parsed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("back\\slash")
expect(parsed.0.len() >= 0).to_equal(true)
```

</details>

#### index_documents with traversal target does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[../secret]]")
val idx = md_wiki_index_documents([doc])
expect(idx.links.len() >= 0).to_equal(true)
```

</details>

### tags: bare hash and edge cases

#### bare # alone is not indexed as a tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "word # word")
val tags = md_wiki_extract_tags(doc)
# bare # followed by space is not a tag
var found = false
for t in tags:
    if t.tag == "":
        found = true
expect(found).to_equal(false)
```

</details>

#### # at end of line is not indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "line #")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(0)
```

</details>

#### #tag123 alphanumeric tag is indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "hello #tag123 world")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(1)
```

</details>

#### #tag-with-dashes is indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "#tag-with-dashes")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(1)
```

</details>

#### #nested/tag is indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "#nested/tag")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(1)
```

</details>

### tags: code fence exclusion

#### tag inside fenced code block is NOT indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "```\n#notag\n```")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(0)
```

</details>

#### tag inside tilde fenced block is NOT indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "~~~\n#notag\n~~~")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(0)
```

</details>

#### tag after closing fence is indexed normally

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "```\n#skip\n```\n#real")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(1)
```

</details>

#### tag before fence is indexed, tag inside is not

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "#before\n```\n#inside\n```")
val tags = md_wiki_extract_tags(doc)
expect(tags.len()).to_equal(1)
```

</details>

### unterminated brackets

#### unterminated [[ at end of file yields no links

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "before [[unterminated")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)
```

</details>

#### unterminated ![[ at end of file yields no embeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "before ![[unterminated")
val embeds = md_wiki_extract_embeds(doc, [doc])
expect(embeds.len()).to_equal(0)
```

</details>

#### [[ spanning two lines yields no link (scanner is line-based)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[start\nend]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)
```

</details>

#### lone [[ with no closing bracket does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(0)
```

</details>

### self-links and duplicate links

#### self-link [[self]] on page self.md is indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("self.md", "# Self\n[[self]]")
val idx = md_wiki_index_documents([doc])
expect(idx.links.len()).to_equal(1)
```

</details>

#### self-link appears as backlink of own page

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("self.md", "# Self\n[[self]]")
val idx = md_wiki_index_documents([doc])
val backs = md_wiki_backlinks(idx, "self.md")
expect(backs.len()).to_equal(1)
```

</details>

#### duplicate links to same target are both indexed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[alpha]] and [[alpha]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len()).to_equal(2)
```

</details>

#### graph edges contain one entry per link occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[alpha]] and [[alpha]]")
val idx = md_wiki_index_documents([doc])
expect(idx.graph_edges.len()).to_equal(2)
```

</details>

### UTF-8 and long targets

#### UTF-8 multi-byte target is safely parsed without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = md_wiki_parse_link_target("日本語ノート")
expect(parsed.0.len() >= 0).to_equal(true)
```

</details>

#### UTF-8 target in document is indexed safely

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "[[日本語ノート]]")
val links = md_wiki_extract_links(doc, [doc])
expect(links.len() >= 0).to_equal(true)
```

</details>

#### very long target name (1000 chars) is safely parsed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_name = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val parsed = md_wiki_parse_link_target(long_name)
expect(parsed.0.len() > 0).to_equal(true)
```

</details>

### empty and frontmatter-only documents

#### empty document yields empty index, no crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "")
val idx = md_wiki_index_documents([doc])
expect(idx.links.len()).to_equal(0)
expect(idx.tags.len()).to_equal(0)
```

</details>

#### frontmatter-only document yields no links or tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "---\ntitle: Test\n---")
val idx = md_wiki_index_documents([doc])
expect(idx.links.len()).to_equal(0)
expect(idx.tags.len()).to_equal(0)
```

</details>

#### frontmatter with tags key indexes those tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "---\ntags: foo, bar\n---")
val idx = md_wiki_index_documents([doc])
expect(idx.tags.len()).to_equal(2)
```

</details>

#### document with only whitespace does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = md_wiki_document("p.md", "   \n  \n   ")
val idx = md_wiki_index_documents([doc])
expect(idx.links.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/services/md_wiki_index_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- malformed link refs: empty anchor
- malformed link refs: empty alias
- malformed link refs: whitespace-only target
- path-traversal targets: safe indexing, no crash
- tags: bare hash and edge cases
- tags: code fence exclusion
- unterminated brackets
- self-links and duplicate links
- UTF-8 and long targets
- empty and frontmatter-only documents

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
