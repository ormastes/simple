# BrowserSession HTML embedded fallback text projection

> Projects supported embedded-content alternatives and fallback content to

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML embedded fallback text projection

Projects supported embedded-content alternatives and fallback content to

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Projects supported embedded-content alternatives and fallback content to
visible text. This is not media loading, layout, or pixel evidence.

## Scenarios

### BrowserSession HTML embedded tag text alternatives

#### should use image alt text inside picture source fallback groups

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should use image alt text inside picture source fallback groups
- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Hero image`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should use image alt text inside picture source fallback groups")
step("Project supported HTML semantics to visible text")
val html = "<picture><source srcset='hero.avif' type='image/avif'><source srcset='hero.webp' type='image/webp'><img src='hero.png' alt='Hero image'></picture>"
expect(html_to_text(html)).to_equal("Hero image")
```

</details>

#### should use area alt text while preserving embedded fallback text

- should use area alt text while preserving embedded fallback text
- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Area labelFrame fallbackObject fallbackVideo fallbackAudio fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should use area alt text while preserving embedded fallback text")
step("Project supported HTML semantics to visible text")
val html = "<map name='m'><area href='/a' alt='Area label'></map><iframe>Frame fallback</iframe><object>Object fallback</object><video><track kind='captions' src='captions.vtt'>Video fallback</video><audio>Audio fallback</audio><embed src='plugin.bin'>"
expect(html_to_text(html)).to_equal("Area labelFrame fallbackObject fallbackVideo fallbackAudio fallback")
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

- Canonical SPipe generation for source `fccda15c34b8c9262f6d5da2f11561f71a912ea353f12d55d5fb4b9bd8e857ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fccda15c34b8c9262f6d5da2f11561f71a912ea353f12d55d5fb4b9bd8e857ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fccda15c34b8c9262f6d5da2f11561f71a912ea353f12d55d5fb4b9bd8e857ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use image alt text inside picture source fallback groups' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use image alt text inside picture source fallback groups' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use area alt text while preserving embedded fallback text' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/web/browser_session_html_embedded_tags_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use area alt text while preserving embedded fallback text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
