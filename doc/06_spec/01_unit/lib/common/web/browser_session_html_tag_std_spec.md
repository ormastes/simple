# Browser Session Html Tag Std Specification

> 1.  assert visible tag

<!-- sdn-diagram:id=browser_session_html_tag_std_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_html_tag_std_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_html_tag_std_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_html_tag_std_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Html Tag Std Specification

## Scenarios

### BrowserSession HTML standard tag base coverage

#### covers sectioning and landmark tags with visible fallback rendering

1.  assert visible tag

2.  assert visible tag

3.  assert visible tag

4.  assert visible tag

5.  assert visible tag

6.  assert visible tag

7.  assert visible tag

8.  assert visible tag
   - Expected: render.ok is true
   - Expected: render.width equals `320`
   - Expected: render.height equals `160`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_assert_visible_tag("main", "<main>Main content</main>", "Main content")
_assert_visible_tag("section", "<section>Section content</section>", "Section content")
_assert_visible_tag("article", "<article>Article content</article>", "Article content")
_assert_visible_tag("nav", "<nav>Nav content</nav>", "Nav content")
_assert_visible_tag("header", "<header>Header content</header>", "Header content")
_assert_visible_tag("footer", "<footer>Footer content</footer>", "Footer content")
_assert_visible_tag("aside", "<aside>Aside content</aside>", "Aside content")
_assert_visible_tag("search", "<search>Search content</search>", "Search content")
val render = _open_body("<main>Main</main><section>Section</section><article>Article</article><nav>Nav</nav><header>Header</header><footer>Footer</footer><aside>Aside</aside><search>Search</search>").render(320, 160)
expect(render.ok).to_equal(true)
expect(render.width).to_equal(320)
expect(render.height).to_equal(160)
```

</details>

#### keeps template contents inert and out of visible body rendering

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = _open_body("<p>Visible</p><template><section>Hidden template text</section></template>")
expect(session.source_html).to_contain("<template>")
expect(session.source_html).to_contain("Hidden template text")
expect(session.current_body_html).to_contain("<p>Visible</p>")
expect(session.current_body_html.contains("Hidden template text")).to_equal(false)
expect(session.render_html_document().contains("Hidden template text")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserSession HTML standard tag base coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
