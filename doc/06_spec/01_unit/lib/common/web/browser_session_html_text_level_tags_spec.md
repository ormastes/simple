# BrowserSession HTML text-level projection

> Projects the supported inline text-level semantics to visible text. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML text-level projection

Projects the supported inline text-level semantics to visible text. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_text_level_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported inline text-level semantics to visible text. This is
focused text-projection evidence, not typography, layout, or pixel evidence.

## Scenarios

### BrowserSession HTML text-level tag semantics

#### should preserve text across common text-level formatting tags

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `emstrongsmallscitequotedfnabbrdatatimecodevarsampkbdsubsupibumarkbdibdospan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<p><em>em</em><strong>strong</strong><small>small</small><s>s</s><cite>cite</cite><q>quote</q><dfn>dfn</dfn><abbr>abbr</abbr><data value='7'>data</data><time datetime='2026-06-06'>time</time><code>code</code><var>var</var><samp>samp</samp><kbd>kbd</kbd><sub>sub</sub><sup>sup</sup><i>i</i><b>b</b><u>u</u><mark>mark</mark><bdi>bdi</bdi><bdo dir='rtl'>bdo</bdo><span>span</span></p>"
expect(html_to_text(html)).to_equal("emstrongsmallscitequotedfnabbrdatatimecodevarsampkbdsubsupibumarkbdibdospan")
```

</details>

#### should map br to a line break and wbr to an optional zero-width break

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `alpha\nbetagamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<p>alpha<br>beta<wbr>gamma</p>"
expect(html_to_text(html)).to_equal("alpha\nbetagamma")
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
