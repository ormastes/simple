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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported `details` and `dialog` visibility semantics to visible
text. This is focused text projection, not event or interaction evidence.

## Scenarios

### BrowserSession HTML interactive tag text semantics

#### should show summary text when details is closed and content when open

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should show summary text when details is closed and content when open
- Project supported HTML semantics to visible text
   - Expected: html_to_text(closed_html) equals `More`
   - Expected: html_to_text(open_html) equals `MoreVisible detail`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should show summary text when details is closed and content when open")
step("Project supported HTML semantics to visible text")
val closed_html = "<details><summary>More</summary><p>Hidden detail</p></details>"
val open_html = "<details open><summary>More</summary><p>Visible detail</p></details>"
expect(html_to_text(closed_html)).to_equal("More")
expect(html_to_text(open_html)).to_equal("MoreVisible detail")
```

</details>

#### should hide closed dialog content and expose open dialog fallback text

- should hide closed dialog content and expose open dialog fallback text
- Project supported HTML semantics to visible text
   - Expected: html_to_text(closed_html) equals `BeforeAfter`
   - Expected: html_to_text(open_html) equals `BeforeVisible dialogAfter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should hide closed dialog content and expose open dialog fallback text")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-002`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4be5847c86025c9b7b566c56e0ab2c0264b49fa10d499cc0200c28b8e7f4e7a7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4be5847c86025c9b7b566c56e0ab2c0264b49fa10d499cc0200c28b8e7f4e7a7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4be5847c86025c9b7b566c56e0ab2c0264b49fa10d499cc0200c28b8e7f4e7a7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show summary text when details is closed and content when open' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should show summary text when details is closed and content when open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should hide closed dialog content and expose open dialog fallback text' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_interactive_tags_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should hide closed dialog content and expose open dialog fallback text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
