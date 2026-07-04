# Md Wiki Transclusion Heading Specification

> <details>

<!-- sdn-diagram:id=md_wiki_transclusion_heading_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_wiki_transclusion_heading_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_wiki_transclusion_heading_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_wiki_transclusion_heading_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Wiki Transclusion Heading Specification

## Scenarios

### heading-scoped transclusion

#### anchored target embeds only the matching heading section

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = [md_wiki_document("notes/target.md", "# Target\nintro\n## Alpha\nalpha body\n## Beta\nbeta body")]
val idx = md_wiki_index_documents(docs)
val sec = md_wiki_transclusion_content(idx, "Target#Alpha")
expect(sec).to_equal("## Alpha\nalpha body")
```

</details>

#### section includes deeper subheadings until a same-level heading

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "## Alpha\nbody\n### Sub\nsub body\n## Beta\nbeta"
val sec = md_wiki_heading_section(body, "Alpha")
expect(sec).to_equal("## Alpha\nbody\n### Sub\nsub body")
```

</details>

#### section of the last heading runs to end of note

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sec = md_wiki_heading_section("# A\nx\n## Last\nfinal body", "Last")
expect(sec).to_equal("## Last\nfinal body")
```

</details>

#### unknown anchor returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = [md_wiki_document("notes/target.md", "# Target\nintro")]
val idx = md_wiki_index_documents(docs)
val sec = md_wiki_transclusion_content(idx, "Target#Nothing")
expect(sec.len()).to_equal(0)
```

</details>

#### plain target still returns the whole note

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = [md_wiki_document("notes/target.md", "# Target\nintro\n## Alpha\nalpha body")]
val idx = md_wiki_index_documents(docs)
val full = md_wiki_transclusion_content(idx, "Target")
expect(full.len() > 0).to_equal(true)
expect(full.index_of("alpha body") >= 0).to_equal(true)
```

</details>

#### anchored target on a missing note returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val docs = [md_wiki_document("notes/other.md", "# Other\nbody")]
val idx = md_wiki_index_documents(docs)
val sec = md_wiki_transclusion_content(idx, "Missing#Alpha")
expect(sec.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/services/md_wiki_transclusion_heading_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- heading-scoped transclusion

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
