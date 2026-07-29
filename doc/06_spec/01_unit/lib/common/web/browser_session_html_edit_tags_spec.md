# BrowserSession HTML edit text projection

> Projects the supported `del` and `ins` semantics to visible text. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML edit text projection

Projects the supported `del` and `ins` semantics to visible text. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_edit_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported `del` and `ins` semantics to visible text. This is
focused text-projection evidence, not complete HTML parsing or rendering.

## Scenarios

### BrowserSession HTML edit tag text semantics

#### should mark inserted and deleted text in plain text extraction

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Before [-old][+new] after`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<p>Before <del cite='/old'>old</del><ins datetime='2026-06-06'>new</ins> after</p>"
expect(html_to_text(html)).to_equal("Before [-old][+new] after")
```

</details>

#### should keep nested inline text inside edit annotations

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `[-removed text][+added text]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<del><strong>removed</strong> text</del><ins><em>added</em> text</ins>"
expect(html_to_text(html)).to_equal("[-removed text][+added text]")
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
