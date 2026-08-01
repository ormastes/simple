# BrowserSession HTML section text projection

> Projects the supported section, heading, and address semantics to visible

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML section text projection

Projects the supported section, heading, and address semantics to visible

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_section_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported section, heading, and address semantics to visible
text. This is focused text-projection evidence, not complete HTML rendering.

## Scenarios

### BrowserSession HTML section and heading tag text semantics

#### should separate body headings hgroup and address into readable lines

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Title\nSubtitle\nChapter\nSection\nTopic\nDetail\nLeaf\nContact`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<body><hgroup><h1>Title</h1><p>Subtitle</p></hgroup><h2>Chapter</h2><h3>Section</h3><h4>Topic</h4><h5>Detail</h5><h6>Leaf</h6><address>Contact</address></body>"
expect(html_to_text(html)).to_equal("Title\nSubtitle\nChapter\nSection\nTopic\nDetail\nLeaf\nContact")
```

</details>

#### should keep adjacent headings from collapsing into one token

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `One\nTwo\nThree\nFour\nFive\nSix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<h1>One</h1><h2>Two</h2><h3>Three</h3><h4>Four</h4><h5>Five</h5><h6>Six</h6>"
expect(html_to_text(html)).to_equal("One\nTwo\nThree\nFour\nFive\nSix")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
