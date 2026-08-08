# BrowserSession HTML ruby text projection

> Projects the supported ruby annotation semantics to visible text. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML ruby text projection

Projects the supported ruby annotation semantics to visible text. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported ruby annotation semantics to visible text. This is
focused text-projection evidence, not ruby layout or typography evidence.

## Scenarios

### BrowserSession HTML ruby tag text semantics

#### should project ruby annotations without duplicating rp fallback markers

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `漢(kan)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<ruby>漢<rp>(</rp><rt>kan</rt><rp>)</rp></ruby>"
expect(html_to_text(html)).to_equal("漢(kan)")
```

</details>

#### should keep adjacent ruby annotations readable without rp fallback tags

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `東(east)京(capital)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<ruby>東<rt>east</rt></ruby><ruby>京<rt>capital</rt></ruby>"
expect(html_to_text(html)).to_equal("東(east)京(capital)")
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
