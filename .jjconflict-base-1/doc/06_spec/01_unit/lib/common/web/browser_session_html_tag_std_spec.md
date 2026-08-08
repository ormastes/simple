# BrowserSession supported HTML tag projection

> Checks the supported sectioning fallback and inert-template behavior in the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession supported HTML tag projection

Checks the supported sectioning fallback and inert-template behavior in the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the supported sectioning fallback and inert-template behavior in the
BrowserSession document projection. This is not full HTML or pixel parity.

## Scenarios

### BrowserSession HTML standard tag base coverage

#### should preserve sectioning and landmark tags in visible fallback output

- Project supported HTML semantics to visible text
-  assert visible tag
-  assert visible tag
-  assert visible tag
-  assert visible tag
-  assert visible tag
-  assert visible tag
-  assert visible tag
-  assert visible tag
   - Expected: render.ok is true
   - Expected: render.width equals `320`
   - Expected: render.height equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
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

#### should keep template contents inert and out of visible body output

- Project supported HTML semantics to visible text
   - Expected: session.current_body_html does not contain `Hidden template text`
   - Expected: session.render_html_document() does not contain `Hidden template text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val session = _open_body("<p>Visible</p><template><section>Hidden template text</section></template>")
expect(session.source_html).to_contain("<template>")
expect(session.source_html).to_contain("Hidden template text")
expect(session.current_body_html).to_contain("<p>Visible</p>")
expect(session.current_body_html.contains("Hidden template text")).to_equal(false)
expect(session.render_html_document().contains("Hidden template text")).to_equal(false)
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
