# BrowserSession HTML interactive text projection

> Projects the supported `details` and `dialog` visibility semantics to visible

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML interactive text projection

Projects the supported `details` and `dialog` visibility semantics to visible

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported `details` and `dialog` visibility semantics to visible
text. This is focused text projection, not event or interaction evidence.

## Scenarios

### BrowserSession HTML interactive tag text semantics

#### should show summary text when details is closed and content when open

- Project supported HTML semantics to visible text
   - Expected: html_to_text(closed_html) equals `More`
   - Expected: html_to_text(open_html) equals `MoreVisible detail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val closed_html = "<details><summary>More</summary><p>Hidden detail</p></details>"
val open_html = "<details open><summary>More</summary><p>Visible detail</p></details>"
expect(html_to_text(closed_html)).to_equal("More")
expect(html_to_text(open_html)).to_equal("MoreVisible detail")
```

</details>

#### should hide closed dialog content and expose open dialog fallback text

- Project supported HTML semantics to visible text
   - Expected: html_to_text(closed_html) equals `BeforeAfter`
   - Expected: html_to_text(open_html) equals `BeforeVisible dialogAfter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val closed_html = "<p>Before</p><dialog>Hidden dialog</dialog><p>After</p>"
val open_html = "<p>Before</p><dialog open>Visible dialog</dialog><p>After</p>"
expect(html_to_text(closed_html)).to_equal("BeforeAfter")
expect(html_to_text(open_html)).to_equal("BeforeVisible dialogAfter")
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
