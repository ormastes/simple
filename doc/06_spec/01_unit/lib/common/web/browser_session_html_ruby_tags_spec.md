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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Projects the supported ruby annotation semantics to visible text. This is
focused text-projection evidence, not ruby layout or typography evidence.

## Scenarios

### BrowserSession HTML ruby tag text semantics

#### should project ruby annotations without duplicating rp fallback markers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should project ruby annotations without duplicating rp fallback markers
- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `漢(kan)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should project ruby annotations without duplicating rp fallback markers")
step("Project supported HTML semantics to visible text")
val html = "<ruby>漢<rp>(</rp><rt>kan</rt><rp>)</rp></ruby>"
expect(html_to_text(html)).to_equal("漢(kan)")
```

</details>

#### should keep adjacent ruby annotations readable without rp fallback tags

- should keep adjacent ruby annotations readable without rp fallback tags
- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `東(east)京(capital)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should keep adjacent ruby annotations readable without rp fallback tags")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WEB-BROWSER-002`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `219987a8a9b721727fbb2a1984dde1720dbfddda70ef4e7f3866ba7ccfcfbd09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `219987a8a9b721727fbb2a1984dde1720dbfddda70ef4e7f3866ba7ccfcfbd09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `219987a8a9b721727fbb2a1984dde1720dbfddda70ef4e7f3866ba7ccfcfbd09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should project ruby annotations without duplicating rp fallback markers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should project ruby annotations without duplicating rp fallback markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep adjacent ruby annotations readable without rp fallback tags' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_ruby_tags_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep adjacent ruby annotations readable without rp fallback tags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
