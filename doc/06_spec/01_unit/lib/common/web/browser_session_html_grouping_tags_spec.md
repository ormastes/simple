# BrowserSession HTML grouping text projection

> Projects the supported grouping and list semantics to visible text. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML grouping text projection

Projects the supported grouping and list semantics to visible text. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported grouping and list semantics to visible text. This is
focused text-projection evidence, not complete HTML parsing or rendering.

## Scenarios

### BrowserSession HTML grouping tag text semantics

#### should preserve paragraph pre blockquote figure and div text

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should preserve paragraph pre blockquote figure and div text
- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Paragraph\n Pre text QuoteFigure bodyCaption`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve paragraph pre blockquote figure and div text")
step("Project supported HTML semantics to visible text")
val html = "<div><p>Paragraph</p><hr><pre> Pre text </pre><blockquote>Quote</blockquote><figure><div>Figure body</div><figcaption>Caption</figcaption></figure></div>"
expect(html_to_text(html)).to_equal("Paragraph\n Pre text QuoteFigure bodyCaption")
```

</details>

#### should separate ordered unordered and menu list items

- should separate ordered unordered and menu list items
- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `One\nTwo\nAlpha\nBeta\nAction\nMore`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should separate ordered unordered and menu list items")
step("Project supported HTML semantics to visible text")
val html = "<ol><li>One</li><li>Two</li></ol><ul><li>Alpha</li><li>Beta</li></ul><menu><li>Action</li><li>More</li></menu>"
expect(html_to_text(html)).to_equal("One\nTwo\nAlpha\nBeta\nAction\nMore")
```

</details>

#### should separate definition list terms and descriptions

- should separate definition list terms and descriptions
- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Term: Description\nNext: More`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should separate definition list terms and descriptions")
step("Project supported HTML semantics to visible text")
val html = "<dl><dt>Term</dt><dd>Description</dd><dt>Next</dt><dd>More</dd></dl>"
expect(html_to_text(html)).to_equal("Term: Description\nNext: More")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `ce4b8a5a4bc30455ba4fd1f8bd880dd87b200bb591cea560e193a0e63c0e066d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce4b8a5a4bc30455ba4fd1f8bd880dd87b200bb591cea560e193a0e63c0e066d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce4b8a5a4bc30455ba4fd1f8bd880dd87b200bb591cea560e193a0e63c0e066d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=85 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve paragraph pre blockquote figure and div text' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve paragraph pre blockquote figure and div text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should separate ordered unordered and menu list items' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should separate ordered unordered and menu list items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should separate definition list terms and descriptions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_grouping_tags_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should separate definition list terms and descriptions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
