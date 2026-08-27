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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the supported sectioning fallback and inert-template behavior in the
BrowserSession document projection. This is not full HTML or pixel parity.

## Scenarios

### BrowserSession HTML standard tag base coverage

#### should preserve sectioning and landmark tags in visible fallback output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve sectioning and landmark tags in visible fallback output
- Project supported HTML semantics to visible text
   - Expected: render.ok is true
   - Expected: render.width equals `320`
   - Expected: render.height equals `160`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve sectioning and landmark tags in visible fallback output")
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

- should keep template contents inert and out of visible body output
- Project supported HTML semantics to visible text
   - Expected: session.current_body_html does not contain `Hidden template text`
   - Expected: session.render_html_document() does not contain `Hidden template text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep template contents inert and out of visible body output")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-002`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eef35dfa3e484b5940a9e66e883ecabcd9c88d6a768df6b41b0e3445a0093493`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eef35dfa3e484b5940a9e66e883ecabcd9c88d6a768df6b41b0e3445a0093493`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eef35dfa3e484b5940a9e66e883ecabcd9c88d6a768df6b41b0e3445a0093493`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_html_tag_std_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=90 oracle=80
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/web/browser_session_html_tag_std_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_html_tag_std_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve sectioning and landmark tags in visible fallback output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve sectioning and landmark tags in visible fallback output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep template contents inert and out of visible body output' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_tag_std_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep template contents inert and out of visible body output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
